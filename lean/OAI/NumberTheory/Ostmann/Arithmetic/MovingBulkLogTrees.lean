import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkLogFactors

namespace OAI

/-! # The actual terminal bulk groups in the logarithmic comparison -/

namespace Ostmann
open scoped Classical BigOperators

def bulkLogLeafLists {σ : Type*} (tier : σ → ℕ) (k : ℕ) :
    {n : ℕ} → MovingSlotData σ n → List (List σ)
  | _, T@(.leaf _ _) => [T.regularSlots.filter (fun a => decide (tier a = k))]
  | _, .node _ _ _ _ left right => bulkLogLeafLists tier k left ++ bulkLogLeafLists tier k right

theorem bulkLogLeafLists_length {σ : Type*} (tier : σ → ℕ) (k : ℕ)
    {n : ℕ} (T : MovingSlotData σ n) : (bulkLogLeafLists tier k T).length = 2 ^ n := by
  induction T with
  | leaf => rfl
  | @node n s CL CR u left right ihL ihR =>
    simp only [bulkLogLeafLists, List.length_append, ihL, ihR, pow_succ]
    omega

theorem bulkLogLeafLists_length_le {σ : Type*} (tier : σ → ℕ) (k : ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (r : ℕ) (hT : T.RegularLengthLE r) :
    ∀ slots ∈ bulkLogLeafLists tier k T, slots.length ≤ r := by
  induction T with
  | leaf =>
    intro slots hs
    have he : slots = _ := List.mem_singleton.mp hs
    subst slots
    exact (List.length_filter_le _ _).trans hT
  | node s CL CR u left right ihL ihR =>
    intro slots hs
    rcases List.mem_append.mp hs with hs | hs
    · exact ihL hT.2.1 slots hs
    · exact ihR hT.2.2 slots hs

theorem movingBulkTreeLogWeight_eq_lists {σ : Type*} (value tier : σ → ℕ)
    (k : ℕ) (outside : List ℕ) (cb cd : ℝ) {n : ℕ} (T : MovingSlotData σ n) :
    movingBulkTreeLogWeight value tier k outside cb cd T =
      ((bulkLogLeafLists tier k T).map (movingBulkListLogWeight value outside cb cd)).prod := by
  induction T with
  | leaf => simp only [movingBulkTreeLogWeight, movingBulkLeafLogWeight,
      bulkLogLeafLists, List.map_singleton, List.prod_singleton]
  | node s CL CR u left right ihL ihR =>
    simp only [movingBulkTreeLogWeight, bulkLogLeafLists, List.map_append,
      List.prod_append, ihL, ihR]

/-- Every terminal logarithmic factor is retained. The constant spectator
weight factors out once per actual leaf. -/
theorem movingBulkTreeLogWeight_eq_cutoff_product {σ : Type*} (value tier : σ → ℕ)
    (hvalue : ∀ a, 0 < value a) (k : ℕ) (outside : List ℕ) (cb cd : ℝ)
    {n : ℕ} (T : MovingSlotData σ n) :
    movingBulkTreeLogWeight value tier k outside cb cd T =
      logCellProfile ((outside.map (fun p => Real.log (p : ℝ))).sum - cd) ^ (2 ^ n) *
        ∏ j : Fin (bulkLogLeafLists tier k T).length,
          bulkLogCutoffWeight (fun a => (value a : ℝ)) cb ((bulkLogLeafLists tier k T)[j]) := by
  rw [movingBulkTreeLogWeight_eq_lists]
  let slots := bulkLogLeafLists tier k T
  have he : (slots.map (movingBulkListLogWeight value outside cb cd)).prod =
      ∏ j : Fin slots.length, movingBulkListLogWeight value outside cb cd slots[j] :=
    (congrArg List.prod (List.ofFn_getElem_eq_map slots
      (movingBulkListLogWeight value outside cb cd))).symm.trans (Fin.prod_ofFn _)
  rw [he]
  simp only [movingBulkListLogWeight_eq_cutoff value hvalue, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hpow :
      logCellProfile ((outside.map (fun p => Real.log (p : ℝ))).sum - cd) ^ slots.length =
        logCellProfile ((outside.map (fun p => Real.log (p : ℝ))).sum - cd) ^ (2 ^ n) :=
    congrArg (fun m : ℕ => logCellProfile
      ((outside.map (fun p => Real.log (p : ℝ))).sum - cd) ^ m)
      (bulkLogLeafLists_length tier k T)
  rw [hpow]
  exact mul_comm _ _

/-- Both branches use their own actual terminal groups. The real logarithmic
weights commute with conjugation, but remain inside the common prime average. -/
theorem movingBulkPairLogWeight_eq_cutoff_product {σ : Type*} (value tier : σ → ℕ)
    (hvalue : ∀ a, 0 < value a) (k : ℕ) (outside : List ℕ) (cb cd : ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) :
    let L := bulkLogLeafLists tier k (T false)
    let R := bulkLogLeafLists tier k (T true)
    let slots := Fin.append (fun j : Fin L.length => L[j]) (fun j : Fin R.length => R[j])
    (movingBulkTreeLogWeight value tier k outside cb cd (T false) : ℂ) *
        star (movingBulkTreeLogWeight value tier k outside cb cd (T true) : ℂ) =
      (logCellProfile ((outside.map (fun p => Real.log (p : ℝ))).sum - cd) ^
        (2 ^ n + 2 ^ n) : ℝ) *
        ((∏ j, bulkLogCutoffWeight (fun a => (value a : ℝ)) cb (slots j) : ℝ) : ℂ) := by
  dsimp only
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  congr 1
  rw [movingBulkTreeLogWeight_eq_cutoff_product value tier hvalue k outside cb cd (T false),
    movingBulkTreeLogWeight_eq_cutoff_product value tier hvalue k outside cb cd (T true)]
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right, pow_add]
  ring

end Ostmann

end OAI
