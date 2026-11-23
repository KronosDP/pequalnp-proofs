import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta168

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option linter.unusedSimpArgs false

/-- One gate step of the wire evaluation. -/
def stepB (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepB x := rfl

theorem foldl_stepB_length (gs : List Gate) (x : List Bool) :
    (gs.foldl stepB x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => simp [ih, stepB]; omega

theorem getD_concat {α : Type} (l : List α) (a d : α) (i : ℕ) :
    (l ++ [a]).getD i d = if i < l.length then l.getD i d else if i = l.length then a else d := by
  rcases lt_trichotomy i l.length with h | h | h
  · rw [if_pos h, List.getD_append _ _ _ _ h]
  · subst h; simp
  · rw [if_neg (by omega), if_neg (by omega), List.getD_eq_default]; simp; omega

/-- A gate reads wire `n` in the sense of the statement. -/
def Reads (n : ℕ) (g : Gate) : Prop :=
  g.op = GateOp.not ∧ g.inputs.head? = some n ∨ g.op ≠ GateOp.not ∧ n ∈ g.inputs

deriving instance DecidableEq for GateOp

instance (n : ℕ) (g : Gate) : Decidable (Reads n g) := by unfold Reads; infer_instance

/-- The operations of a fan-in-two circuit. -/
def OkOp (op : GateOp) : Prop := op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not

/-- An abstract wire value: a known constant, or a wire of the new circuit. -/
abbrev AV := Bool ⊕ ℕ

def interp (W : List Bool) : AV → Bool
  | Sum.inl b => b
  | Sum.inr w => W.getD w false

/-- The wires among a list of abstract values. -/
def rights : List AV → List ℕ
  | [] => []
  | Sum.inl _ :: l => rights l
  | Sum.inr w :: l => w :: rights l

/-- Simplify a gate whose inputs are abstract values. `inl v`: the gate's value is `v` and no
gate is needed; `inr g`: emit the gate `g`. -/
def simpGate (op : GateOp) (ins : List AV) : AV ⊕ Gate :=
  match op with
  | GateOp.and =>
    if Sum.inl false ∈ ins then Sum.inl (Sum.inl false) else
    match rights ins with
    | [] => Sum.inl (Sum.inl true)
    | [w] => Sum.inl (Sum.inr w)
    | ws => Sum.inr ⟨GateOp.and, ws⟩
  | GateOp.or =>
    if Sum.inl true ∈ ins then Sum.inl (Sum.inl true) else
    match rights ins with
    | [] => Sum.inl (Sum.inl false)
    | [w] => Sum.inl (Sum.inr w)
    | ws => Sum.inr ⟨GateOp.or, ws⟩
  | GateOp.not =>
    match ins.head? with
    | none => Sum.inl (Sum.inl true)
    | some (Sum.inl b) => Sum.inl (Sum.inl (!b))
    | some (Sum.inr w) => Sum.inr ⟨GateOp.not, [w]⟩
  | _ => Sum.inl (Sum.inl false)

/-- The value the simplified gate produces, on new wires `W`. -/
def simpVal (W : List Bool) : AV ⊕ Gate → Bool
  | Sum.inl v => interp W v
  | Sum.inr g => g.op.eval (g.inputs.map fun i => W.getD i false)

theorem simpGate_sound (W : List Bool) (op : GateOp) (ins : List AV) (hop : OkOp op)
    (hlen : ins.length ≤ 2) :
    simpVal W (simpGate op ins) = op.eval (ins.map (interp W)) := by
  obtain _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ := ins
  · rcases hop with rfl | rfl | rfl <;> simp [simpGate, simpVal, GateOp.eval, interp, rights]
  · rcases hop with rfl | rfl | rfl <;> rcases a with (_ | _) | a <;>
      simp [simpGate, simpVal, GateOp.eval, interp, rights]
  · rcases hop with rfl | rfl | rfl <;> rcases a with (_ | _) | a <;> rcases b with (_ | _) | b <;>
      simp [simpGate, simpVal, GateOp.eval, interp, rights]
  · simp at hlen

theorem simpGate_inl_inr (op : GateOp) (ins : List AV) (hop : OkOp op) (hlen : ins.length ≤ 2)
    (w : ℕ) (h : simpGate op ins = Sum.inl (Sum.inr w)) : Sum.inr w ∈ ins := by
  obtain _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ := ins
  · rcases hop with rfl | rfl | rfl <;> simp [simpGate, rights] at h
  · rcases hop with rfl | rfl | rfl <;> rcases a with (_ | _) | a <;> simp_all [simpGate, rights]
  · rcases hop with rfl | rfl | rfl <;> rcases a with (_ | _) | a <;> rcases b with (_ | _) | b <;>
      simp_all [simpGate, rights]
  · simp at hlen

theorem simpGate_inr (op : GateOp) (ins : List AV) (hop : OkOp op) (hlen : ins.length ≤ 2)
    (g : Gate) (h : simpGate op ins = Sum.inr g) :
    OkOp g.op ∧ g.inputs.length ≤ 2 ∧ ∀ i ∈ g.inputs, Sum.inr i ∈ ins := by
  obtain _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ := ins
  · rcases hop with rfl | rfl | rfl <;> simp [simpGate, rights] at h
  · rcases hop with rfl | rfl | rfl <;> rcases a with (_ | _) | a <;> simp [simpGate, rights] at h <;>
      subst h <;> simp [OkOp]
  · rcases hop with rfl | rfl | rfl <;> rcases a with (_ | _) | a <;> rcases b with (_ | _) | b <;>
      simp [simpGate, rights] at h <;> subst h <;> simp [OkOp]
  · simp at hlen

theorem simpGate_reads (op : GateOp) (ins : List AV) (hop : OkOp op) (hlen : ins.length ≤ 2)
    (h : op = GateOp.not ∧ ins.head? = some (Sum.inl false) ∨
      op ≠ GateOp.not ∧ Sum.inl false ∈ ins) :
    ∃ v, simpGate op ins = Sum.inl v := by
  obtain _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ := ins
  · rcases hop with rfl | rfl | rfl <;> simp at h
  · rcases hop with rfl | rfl | rfl <;> rcases a with (_ | _) | a <;> simp_all [simpGate, rights]
  · rcases hop with rfl | rfl | rfl <;> rcases a with (_ | _) | a <;> rcases b with (_ | _) | b <;>
      simp_all [simpGate, rights]
  · simp at hlen

/-- One step of the partial evaluation: the abstract values of the old wires, and the gates of
the new circuit on `n` inputs. -/
def stepS (n : ℕ) (s : List AV × List Gate) (g : Gate) : List AV × List Gate :=
  match simpGate g.op (g.inputs.map fun i => s.1.getD i (Sum.inl false)) with
  | Sum.inl v => (s.1 ++ [v], s.2)
  | Sum.inr g' => (s.1 ++ [Sum.inr (n + s.2.length)], s.2 ++ [g'])

/-- Gates of a fan-in-two circuit. -/
def OkGate (g : Gate) : Prop := OkOp g.op ∧ g.inputs.length ≤ 2

/-- The invariant of the partial evaluation, for new inputs `x` (of length `n`) and old wires `W`. -/
structure Inv (n : ℕ) (x : List Bool) (s : List AV × List Gate) (W : List Bool) : Prop where
  val : ∀ i, interp (s.2.foldl stepB x) (s.1.getD i (Sum.inl false)) = W.getD i false
  bound : ∀ i w, s.1.getD i (Sum.inl false) = Sum.inr w → w < n + s.2.length
  len : s.1.length = W.length
  fan : ∀ g ∈ s.2, OkGate g

theorem interp_mono (W : List Bool) (b : Bool) (v : AV)
    (hv : ∀ w, v = Sum.inr w → w < W.length) : interp (W ++ [b]) v = interp W v := by
  rcases v with c | w
  · rfl
  · simp only [interp]
    rw [List.getD_append _ _ _ _ (hv w rfl)]

theorem step_inv (n : ℕ) (x : List Bool) (hx : x.length = n) (s : List AV × List Gate)
    (W : List Bool) (g : Gate) (hg : OkGate g) (hI : Inv n x s W) :
    Inv n x (stepS n s g) (stepB W g) := by
  obtain ⟨a, ng⟩ := s
  obtain ⟨hval, hbound, hlen, hfan⟩ := hI
  simp only at hval hbound hlen hfan
  set newW := ng.foldl stepB x with hnewW
  have hnewLen : newW.length = n + ng.length := by
    rw [hnewW, foldl_stepB_length, hx]
  set ins := g.inputs.map fun i => a.getD i (Sum.inl false) with hins
  have hinsLen : ins.length ≤ 2 := by rw [hins, List.length_map]; exact hg.2
  have hkey : ins.map (interp newW) = g.inputs.map fun i => W.getD i false := by
    rw [hins, List.map_map]
    exact List.map_congr_left fun i _ => hval i
  have hsound := simpGate_sound newW g.op ins hg.1 hinsLen
  rw [hkey] at hsound
  have hinsBound : ∀ w, Sum.inr w ∈ ins → w < n + ng.length := by
    intro w hw
    rw [hins, List.mem_map] at hw
    obtain ⟨i, _, hi⟩ := hw
    exact hbound i w hi
  unfold stepS
  simp only
  rcases hsg : simpGate g.op ins with v | g'
  · rw [hsg] at hsound
    simp only [simpVal] at hsound
    refine ⟨?_, ?_, ?_, hfan⟩
    · intro i
      simp only [stepB]
      rw [getD_concat, getD_concat, hlen]
      split_ifs with h1 h2
      · exact hval i
      · exact hsound
      · rfl
    · intro i w hiw
      rw [getD_concat] at hiw
      split_ifs at hiw with h1 h2
      · exact hbound i w hiw
      · subst hiw
        exact hinsBound w (simpGate_inl_inr g.op ins hg.1 hinsLen w hsg)
    · simp [hlen, stepB]
  · rw [hsg] at hsound
    simp only [simpVal] at hsound
    obtain ⟨hok, hl2, hin⟩ := simpGate_inr g.op ins hg.1 hinsLen g' hsg
    have hfold : (ng ++ [g']).foldl stepB x = newW ++
        [g'.op.eval (g'.inputs.map fun i => newW.getD i false)] := by
      rw [List.foldl_append]; rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      simp only
      rw [hfold]
      simp only [stepB]
      rw [getD_concat, getD_concat, hlen]
      split_ifs with h1 h2
      · rw [interp_mono]
        · exact hval i
        · intro w hw
          rw [hnewLen]
          exact hbound i w hw
      · simp only [interp]
        rw [← hnewLen, getD_concat, if_neg (lt_irrefl _), if_pos rfl]
        exact hsound
      · rfl
    · intro i w hiw
      simp only at hiw ⊢
      rw [getD_concat] at hiw
      rw [List.length_append, List.length_singleton]
      split_ifs at hiw with h1 h2
      · have := hbound i w hiw; omega
      · cases hiw; omega
    · simp [hlen, stepB]
    · intro g'' hg''
      simp only [List.mem_append, List.mem_singleton] at hg''
      rcases hg'' with hg'' | rfl
      · exact hfan g'' hg''
      · exact ⟨hok, hl2⟩

theorem fold_inv (n : ℕ) (x : List Bool) (hx : x.length = n) (gs : List Gate)
    (hgs : ∀ g ∈ gs, OkGate g) (s : List AV × List Gate) (W : List Bool) (hI : Inv n x s W) :
    Inv n x (gs.foldl (stepS n) s) (gs.foldl stepB W) := by
  induction gs generalizing s W with
  | nil => exact hI
  | cons g gs ih =>
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) _ _
      (step_inv n x hx s W g (hgs g List.mem_cons_self) hI)

/-- The partial evaluation keeps the entry at `n` and adds at most one new gate per old gate,
none for a gate reading wire `n`. -/
theorem fold_count (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, OkGate g)
    (s : List AV × List Gate) (hn : n < s.1.length) (hs : s.1.getD n (Sum.inl false) = Sum.inl false) :
    (gs.foldl (stepS n) s).1.getD n (Sum.inl false) = Sum.inl false ∧
    (gs.foldl (stepS n) s).2.length + gs.countP (fun g => decide (Reads n g)) ≤
      s.2.length + gs.length := by
  induction gs generalizing s with
  | nil => exact ⟨hs, by simp⟩
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg := hgs g List.mem_cons_self
    have hrest : ∀ g' ∈ gs, OkGate g' := fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
    have hlen' : n < (stepS n s g).1.length := by
      unfold stepS; split <;> simp <;> omega
    have hs' : (stepS n s g).1.getD n (Sum.inl false) = Sum.inl false := by
      unfold stepS; split <;> simp only <;> rw [List.getD_append _ _ _ _ hn, hs]
    obtain ⟨h1, h2⟩ := ih hrest (stepS n s g) hlen' hs'
    refine ⟨h1, ?_⟩
    have hstep : (stepS n s g).2.length + (if Reads n g then 1 else 0) ≤ s.2.length + 1 := by
      set ins := g.inputs.map fun i => s.1.getD i (Sum.inl false) with hins
      have hinsLen : ins.length ≤ 2 := by rw [hins, List.length_map]; exact hg.2
      by_cases hr : Reads n g
      · rw [if_pos hr]
        have hread : g.op = GateOp.not ∧ ins.head? = some (Sum.inl false) ∨
            g.op ≠ GateOp.not ∧ Sum.inl false ∈ ins := by
          rcases hr with ⟨hop, hh⟩ | ⟨hop, hm⟩
          · left
            refine ⟨hop, ?_⟩
            rw [hins, List.head?_map, hh, Option.map_some, hs]
          · right
            refine ⟨hop, ?_⟩
            rw [hins, List.mem_map]
            exact ⟨n, hm, hs⟩
        obtain ⟨v, hv⟩ := simpGate_reads g.op ins hg.1 hinsLen hread
        unfold stepS
        rw [← hins, hv]
      · rw [if_neg hr]
        unfold stepS
        split <;> simp
    rw [List.countP_cons]
    have : (if (decide (Reads n g)) = true then 1 else 0) =
        (if Reads n g then 1 else 0) := by
      by_cases hr : Reads n g <;> simp [hr]
    rw [this]
    simp only [List.length_cons]
    omega

/-- Two different positions satisfying `p` give `countP p ≥ 2`. -/
theorem two_le_countP {α : Type} (p : α → Bool) :
    ∀ (l : List α) (j j' : Fin l.length), p (l.get j) → p (l.get j') → j ≠ j' → 2 ≤ l.countP p
  | [], j, _, _, _, _ => j.elim0
  | a :: l, j, j', hj, hj', hne => by
    rw [List.countP_cons]
    rcases j with ⟨_ | j, hjl⟩ <;> rcases j' with ⟨_ | j', hjl'⟩
    · exact absurd rfl hne
    · simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ] at hj hj'
      have : 1 ≤ l.countP p := List.countP_pos_iff.mpr ⟨_, List.getElem_mem _, hj'⟩
      rw [if_pos hj]; omega
    · simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ] at hj hj'
      have : 1 ≤ l.countP p := List.countP_pos_iff.mpr ⟨_, List.getElem_mem _, hj⟩
      rw [if_pos hj']; omega
    · have := two_le_countP p l ⟨j, by simpa using hjl⟩ ⟨j', by simpa using hjl'⟩
        (by simpa using hj) (by simpa using hj') (by
          intro h; apply hne; simp only [Fin.mk.injEq] at h ⊢; omega)
      split <;> omega

/-- With no gate reading wire `n`, the wires on two inputs differing only at `n` agree away
from `n`. -/
theorem fold_agree (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, ¬ Reads n g)
    (W1 W2 : List Bool) (hl : W1.length = W2.length)
    (h : ∀ i, i ≠ n → W1.getD i false = W2.getD i false) :
    ∀ i, i ≠ n → (gs.foldl stepB W1).getD i false = (gs.foldl stepB W2).getD i false := by
  induction gs generalizing W1 W2 with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
    · simp [stepB, hl]
    · intro i hi
      have hng := hgs g List.mem_cons_self
      have heval : g.op.eval (g.inputs.map fun i => W1.getD i false) =
          g.op.eval (g.inputs.map fun i => W2.getD i false) := by
        by_cases hop : g.op = GateOp.not
        · rw [hop]
          simp only [GateOp.eval]
          congr 1
          rcases hin : g.inputs with _ | ⟨k, ks⟩
          · rfl
          · have hk : k ≠ n := by
              intro hk; apply hng; left; exact ⟨hop, by rw [hin, hk]; rfl⟩
            simp only [List.map_cons, List.headD_cons]
            exact h k hk
        · congr 1
          refine List.map_congr_left fun k hk => h k ?_
          intro hkn; apply hng; right; exact ⟨hop, hkn ▸ hk⟩
      simp only [stepB]
      rw [getD_concat, getD_concat, hl, heval]
      split_ifs with h1
      · exact h i hi
      · rfl
      · rfl

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp

end PEqualNP.Outside.LMeta168

open PEqualNP.Outside.LMeta168 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_168 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y true)) → (∃ y y' : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false) ≠ PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y' false)) → (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => PEqualNP.MetaComplexity.circuitFun (n + 1) C (Fin.snoc y false)) s → C.size ≤ s + 1) → ∃ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) ∧ ∀ j' : Fin C.gates.length, ((C.gates.get j').op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j').inputs.head? = some n ∨ (C.gates.get j').op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j').inputs) → j' = j := by
  intro n C hmin hdep hnc hsave
  have hok : ∀ g ∈ C.gates, OkGate g := by
    intro g hg
    obtain ⟨hop, hl⟩ := hmin.1 g hg
    refine ⟨?_, hl⟩
    simpa [OkOp] using hop
  -- The partial evaluation of `C` with the last input fixed to `false`; it does not depend on `y`.
  obtain ⟨s0, hs0⟩ : ∃ s0 : List AV × List Gate,
      s0 = ((List.range n).map Sum.inr ++ [Sum.inl false], []) := ⟨_, rfl⟩
  obtain ⟨sF, hsF⟩ : ∃ sF, sF = C.gates.foldl (stepS n) s0 := ⟨_, rfl⟩
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) sF (C.wires (List.ofFn (Fin.snoc y false : Fin (n + 1) → Bool))) := by
    intro y
    rw [wires_eq, ofFn_snoc, hsF]
    apply fold_inv n _ (by simp) C.gates hok
    subst hs0
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      simp only [List.foldl_nil]
      rw [getD_concat, getD_concat]
      simp only [List.length_map, List.length_range, List.length_ofFn]
      split_ifs with h1 h2
      · simp [interp, List.getD_eq_getElem?_getD, h1]
      · rfl
      · rfl
    · intro i w hiw
      simp only at hiw
      rw [getD_concat] at hiw
      simp only [List.length_map, List.length_range] at hiw
      split_ifs at hiw with h1 h2
      · simp [List.getD_eq_getElem?_getD, h1] at hiw
        simp; omega
    · simp
    · simp
  obtain ⟨hFn, hcnt⟩ := fold_count n C.gates hok s0 (by simp [hs0])
    (by rw [hs0, getD_concat]; simp)
  rw [← hsF] at hFn hcnt
  simp only [hs0, List.length_nil, zero_add] at hcnt
  have hval : ∀ y : Fin n → Bool,
      interp (sF.2.foldl stepB (List.ofFn y)) (sF.1.getD C.output (Sum.inl false)) =
        circuitFun (n + 1) C (Fin.snoc y false) := fun y => (hinv y).val C.output
  -- The output is not a constant, since the restricted function is not constant.
  obtain ⟨w, hw⟩ : ∃ w, sF.1.getD C.output (Sum.inl false) = Sum.inr w := by
    rcases h : sF.1.getD C.output (Sum.inl false) with b | w
    · exfalso
      obtain ⟨y, y', hyy⟩ := hnc
      apply hyy
      rw [← hval y, ← hval y', h]
      rfl
    · exact ⟨w, rfl⟩
  -- The new circuit computes the restricted function with `sF.2.length` gates.
  have hD : HasCircuitSize n (fun y : Fin n → Bool => circuitFun (n + 1) C (Fin.snoc y false))
      sF.2.length := by
    refine ⟨⟨sF.2, w⟩, ?_, le_refl _, ?_⟩
    · intro g hg
      obtain ⟨hop, hl⟩ := (hinv (fun _ => false)).fan g hg
      refine ⟨?_, hl⟩
      rcases hop with h | h | h <;> simp [h]
    · intro y
      show Circuit.eval ⟨sF.2, w⟩ (List.ofFn y) = circuitFun (n + 1) C (Fin.snoc y false)
      rw [← hval y, hw]
      rfl
  have hsz := hsave _ hD
  -- Some gate reads the last input.
  have hex : ∃ j : Fin C.gates.length, Reads n (C.gates.get j) := by
    by_contra hno
    simp only [not_exists] at hno
    have hnoR : ∀ g ∈ C.gates, ¬ Reads n g := by
      intro g hg
      obtain ⟨j, rfl⟩ := List.get_of_mem hg
      exact hno j
    have hout : C.output ≠ n := by
      intro h
      rw [h, hFn] at hw
      cases hw
    obtain ⟨y, hy⟩ := hdep
    apply hy
    unfold circuitFun Circuit.eval
    rw [wires_eq, wires_eq, ofFn_snoc, ofFn_snoc]
    refine fold_agree n C.gates hnoR _ _ (by simp) ?_ C.output hout
    intro i hi
    rw [getD_concat, getD_concat]
    simp only [List.length_ofFn]
    split_ifs <;> simp_all
  -- At most one: two would save two gates.
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, hj, fun j' hj' => ?_⟩
  by_contra hne
  have h2 := two_le_countP (fun g => decide (Reads n g)) C.gates j' j
    (by simpa [Reads] using hj') (by simpa [Reads] using hj) hne
  simp only [Circuit.size] at hsz
  omega
