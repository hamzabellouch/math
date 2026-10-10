import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.HalfLaws

namespace OAI

/-! Fixed rational distributions and their entropy and capacity formulas. -/

namespace MatrixMultiplication.AllFieldParameters

open scoped BigOperators

theorem normalized_singleton_law {A : Type*} [Fintype A] [DecidableEq A]
    (p : A → ℚ) (a : A) (hp : ∑ i, p i = 1)
    (hs : ∀ i, i ≠ a → p i = 0) (i : A) : p i = if i = a then 1 else 0 := by
  have ha : p a = 1 := by
    have hsum : (∑ i, p i) = p a := by
      apply Finset.sum_eq_single a
      · intro i _ hi
        exact hs i hi
      · simp
    exact hsum.symm.trans hp
  by_cases hi : i = a
  · simp [hi, ha]
  · simp [hi, hs i hi]

theorem pairWeight_zero : ∀ ij : PairSlot,
    statisticWeight ij.1 + statisticWeight ij.2 = 0 ↔ ij = (0,0) := by decide +kernel

theorem pairWeight_eight : ∀ ij : PairSlot,
    statisticWeight ij.1 + statisticWeight ij.2 = 8 ↔ ij = (5,5) := by decide +kernel

theorem pairKappa_zero : ∀ ij : PairSlot,
    (kappa ij.1, kappa ij.2) = (0,0) ↔ ij = (5,5) := by decide +kernel

theorem pairKappa_eight : ∀ ij : PairSlot,
    (kappa ij.1, kappa ij.2) = (5,5) ↔ ij = (0,0) := by decide +kernel

theorem halfLaw_weight_zero (t : Shape) (ht : t ∈ shapes 8) (w : Fin 3)
    (hw : t w = 0) (ij : PairSlot) :
    halfLaw t w ij = if ij = (0,0) then 1 else 0 := by
  apply normalized_singleton_law (halfLaw t w) (0,0) (halfLaw_normalized t ht w)
  intro pair hpair
  apply halfLaw_outside_support t ht w pair
  rw [hw]
  exact fun h => hpair ((pairWeight_zero pair).mp h)

theorem halfLaw_weight_eight (t : Shape) (ht : t ∈ shapes 8) (w : Fin 3)
    (hw : t w = 8) (ij : PairSlot) :
    halfLaw t w ij = if ij = (5,5) then 1 else 0 := by
  apply normalized_singleton_law (halfLaw t w) (5,5) (halfLaw_normalized t ht w)
  intro pair hpair
  apply halfLaw_outside_support t ht w pair
  rw [hw]
  exact fun h => hpair ((pairWeight_eight pair).mp h)

theorem complementary_half_sides_zero_parent : ∀ t ∈ shapes 8, ∀ w v : Fin 3,
    w ≠ v → t w + t v = 8 → t ∈ zeroSecond := by decide +kernel

theorem halfLaw_complementary_sides (t : Shape) (ht : t ∈ shapes 8)
    (w v : Fin 3) (hwv : w ≠ v) (hsum : t w + t v = 8) (ij : PairSlot) :
    halfLaw t w (kappa ij.1, kappa ij.2) = halfLaw t v ij := by
  by_cases hw : t w = 0
  · have hv : t v = 8 := by omega
    rw [halfLaw_weight_zero t ht w hw, halfLaw_weight_eight t ht v hv]
    simp only [pairKappa_zero]
  · by_cases hv : t v = 0
    · have hw8 : t w = 8 := by omega
      rw [halfLaw_weight_eight t ht w hw8, halfLaw_weight_zero t ht v hv]
      simp only [pairKappa_eight]
    · exact halfLaw_zero_complement t
        (complementary_half_sides_zero_parent t ht w v hwv hsum) w v hw hv hwv ij

theorem zero_maximum_axis_nonzero : ∀ t ∈ zeroSecond, t (halfMaxAxis t) ≠ 0 := by
  decide +kernel

theorem halfLaw_at_maximum (t : Shape) (ht : t ∈ zeroSecond) (ij : PairSlot) :
    halfLaw t (halfMaxAxis t) ij = zeroPairLaw t ij.1 ij.2 := by
  have hp : positive t ≠ true := by simpa using (List.mem_filter.mp ht).2
  simp only [halfLaw, hp, Bool.false_eq_true, ite_false,
    ite_eq_right (zero_maximum_axis_nonzero t ht), ite_true]

theorem zeroPairLaw_shapeMax_eight (t : Shape) (ht : t ∈ zeroSecond)
    (hmax : shapeMax t = 8) (ij : PairSlot) :
    zeroPairLaw t ij.1 ij.2 = if ij = (5,5) then 1 else 0 := by
  have hshape : t ∈ shapes 8 := (List.mem_filter.mp ht).1
  rw [← halfLaw_at_maximum t ht ij]
  exact halfLaw_weight_eight t hshape (halfMaxAxis t)
    ((halfMaxAxis_spec t hshape).trans hmax) ij

end MatrixMultiplication.AllFieldParameters

end OAI
