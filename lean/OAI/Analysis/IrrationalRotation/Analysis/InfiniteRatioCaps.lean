import OAI.Analysis.IrrationalRotation.Rotation.CircleCocycle

namespace OAI

open Function
open scoped BigOperators

namespace Invariant233.InfiniteRatioCaps

private theorem summable_finset_mask {I : Type*} [DecidableEq I] (c : I → ℝ) (s : Finset I) :
    Summable (fun i => if i ∈ s then c i else 0) := by
  classical
  apply summable_of_hasFiniteSupport
  apply s.finite_toSet.subset
  intro i hi
  by_contra hn
  change i ∉ s at hn
  exact hi (by simp [hn])

private theorem tsum_finset_mask {I : Type*} [DecidableEq I] (c : I → ℝ) (s : Finset I) :
    (∑' i, if i ∈ s then c i else 0) = ∑ i ∈ s, c i := by
  classical
  rw [tsum_eq_sum (s := s) (by intro i hi; simp [hi])]
  exact Finset.sum_congr rfl (by intro i hi; simp [hi])

theorem ratio_le_exp_exception_sub_crossings {I : Type*}
    (x y t c : I → ℝ) (a s : Finset I)
    (hx01 : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1)
    (hy01 : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (hxy : ∀ i, i ∉ a → x i ≤ y i)
    (hx : HasFiniteSupport (fun i => Int.floor (x i + t i)))
    (hy : HasFiniteSupport (fun i => Int.floor (y i + t i)))
    (hcross : ∀ i ∈ s, x i < 1 - Int.fract (t i) ∧
      1 - Int.fract (t i) ≤ y i) :
    Real.exp (-(∑' i, c i * (Int.floor (y i + t i) : ℝ))) /
      Real.exp (-(∑' i, c i * (Int.floor (x i + t i) : ℝ))) ≤
      Real.exp ((∑ i ∈ a, c i) - ∑ i ∈ s, c i) := by
  classical
  have hsx := FiniteSupportCocycle.summable_weighted_int c hx
  have hsy := FiniteSupportCocycle.summable_weighted_int c hy
  have hbound (i : I) :
      c i * (Int.floor (x i + t i) : ℝ) - c i * (Int.floor (y i + t i) : ℝ) ≤
        (if i ∈ a then c i else 0) - (if i ∈ s then c i else 0) := by
    by_cases his : i ∈ s
    · have hci := hcross i his
      have horder : x i ≤ y i := hci.1.le.trans hci.2
      have hdiff : (Int.floor (y i + t i) : ℝ) -
          (Int.floor (x i + t i) : ℝ) = 1 := by
        exact_mod_cast (FloorCocycle.floor_sub_eq_one_iff
          (hx01 i).1 (hx01 i).2 (hy01 i).1 (hy01 i).2 horder (t i)).mpr hci
      simp only [ite_eq_left his]
      by_cases hia : i ∈ a
      · simp only [ite_eq_left hia]
        nlinarith [hc i]
      · simp only [ite_eq_right hia]
        nlinarith [hc i]
    · by_cases hia : i ∈ a
      · have hdiff : (Int.floor (x i + t i) : ℝ) -
            (Int.floor (y i + t i) : ℝ) ≤ 1 := by
          exact_mod_cast (FloorCocycle.floor_sub_bounds
            (hy01 i).1 (hy01 i).2 (hx01 i).1 (hx01 i).2 (t i)).2
        simp only [ite_eq_left hia, ite_eq_right his, sub_zero]
        have := mul_le_mul_of_nonneg_left hdiff (hc i)
        nlinarith
      · have hfloor : (Int.floor (x i + t i) : ℝ) ≤
            (Int.floor (y i + t i) : ℝ) := by
          apply Int.cast_le.mpr
          apply Int.floor_mono
          linarith [hxy i hia]
        simp only [ite_eq_right hia, ite_eq_right his, sub_self]
        exact sub_nonpos.mpr (mul_le_mul_of_nonneg_left hfloor (hc i))
  have hsum := (hsx.sub hsy).tsum_le_tsum hbound
    ((summable_finset_mask c a).sub (summable_finset_mask c s))
  rw [hsx.tsum_sub hsy, (summable_finset_mask c a).tsum_sub
    (summable_finset_mask c s), tsum_finset_mask, tsum_finset_mask] at hsum
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  linarith

end Invariant233.InfiniteRatioCaps

namespace Invariant233.CircleWeights

theorem cocycle_ratio_cap_with_crossings {ι : Type*}
    (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ) (k : ℤ)
    (x y : UnitAddCircle) (a s : Finset ι)
    (hc : ∀ i, 0 ≤ c i)
    (hxy : ∀ i, i ∉ a → coordinate q i x ≤ coordinate q i y)
    (hx : HasFiniteSupport (fun i =>
      Int.floor (coordinate q i x + (k : ℝ) * phase θ q i)))
    (hy : HasFiniteSupport (fun i =>
      Int.floor (coordinate q i y + (k : ℝ) * phase θ q i)))
    (hcross : ∀ i ∈ s, coordinate q i x < 1 - Int.fract ((k : ℝ) * phase θ q i) ∧
      1 - Int.fract ((k : ℝ) * phase θ q i) ≤ coordinate q i y) :
    cocycle θ q c k y / cocycle θ q c k x ≤
      Real.exp ((∑ i ∈ a, c i) - ∑ i ∈ s, c i) := by
  exact InfiniteRatioCaps.ratio_le_exp_exception_sub_crossings
    (fun i => coordinate q i x) (fun i => coordinate q i y)
    (fun i => (k : ℝ) * phase θ q i) c a s
    (fun i => coordinate_mem_Ico q i x) (fun i => coordinate_mem_Ico q i y)
    hc hxy hx hy hcross

theorem cocycle_ratio_cap_finite_exceptions {ι : Type*}
    (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ) (k : ℤ)
    (x y : UnitAddCircle) (a : Finset ι)
    (hc : ∀ i, 0 ≤ c i)
    (hxy : ∀ i, i ∉ a → coordinate q i x ≤ coordinate q i y)
    (hx : HasFiniteSupport (fun i =>
      Int.floor (coordinate q i x + (k : ℝ) * phase θ q i)))
    (hy : HasFiniteSupport (fun i =>
      Int.floor (coordinate q i y + (k : ℝ) * phase θ q i))) :
    cocycle θ q c k y / cocycle θ q c k x ≤ Real.exp (∑ i ∈ a, c i) := by
  simpa only [Finset.sum_empty, sub_zero] using
    cocycle_ratio_cap_with_crossings θ q c k x y a ∅ hc hxy hx hy
      (by intro i hi; simp at hi)

end Invariant233.CircleWeights

end OAI
