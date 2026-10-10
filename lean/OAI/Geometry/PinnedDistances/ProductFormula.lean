import OAI.Geometry.PinnedDistances.MixtureLaw

namespace OAI

universe u1 u2 u3 u4

section

/- The finite-place absolute values are norm-normalized. Dividing their logarithms
   by [K:ℚ] gives the weighted contribution of locally normalized absolute values. -/

noncomputable section
open NumberField
open scoped BigOperators

namespace WeakPinned.Arithmetic

variable {K : Type u1} [Field K]

lemma totallyComplex_of_sq_neg_one (ii : K) (hii : ii ^ 2 = -1) :
    NumberField.IsTotallyComplex K := by
  constructor
  intro v
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hv
  let φ := InfinitePlace.embedding_of_isReal hv
  have h := congrArg φ hii
  simp only [map_pow, map_neg, map_one] at h
  nlinarith [sq_nonneg (φ ii)]

variable [NumberField K]

lemma log_product_formula (z : K) (hz : z ≠ 0) :
    (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (v z)) +
      ∑ᶠ v : FinitePlace K, Real.log (v z) = 0 := by
  have hi : ∀ v : InfinitePlace K, 0 < v z := fun _ => InfinitePlace.pos_iff.mpr hz
  have hf : ∀ v : FinitePlace K, 0 < v z := fun _ => FinitePlace.pos_iff.mpr hz
  have h := congrArg Real.log (NumberField.prod_abs_eq_one hz)
  rw [Real.log_mul (Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (hi v).ne')
    (finprod_ne_zero fun v => (hf v).ne'), Real.log_prod (fun v _ => pow_ne_zero _ (hi v).ne'),
    Real.log_finprod hf, Real.log_one] at h
  simpa only [Real.log_pow] using h

def archWeight (v : InfinitePlace K) : ℝ :=
  (v.mult : ℝ) / Module.finrank ℚ K

lemma sum_archWeight : ∑ v : InfinitePlace K, archWeight v = 1 := by
  classical
  unfold archWeight
  rw [← Finset.sum_div, ← Nat.cast_sum, InfinitePlace.sum_mult_eq, div_self]
  exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'

lemma archWeight_nonneg (v : InfinitePlace K) : 0 ≤ archWeight v := by
  unfold archWeight
  positivity

/-- The finitely many nonunit places for a given finite list of differences. -/
lemma finite_nonunit_places {ι : Type u2} [Finite ι] (z : ι → K)
    (hz : ∀ i, z i ≠ 0) :
    {v : FinitePlace K | ∃ i, v (z i) ≠ 1}.Finite := by
  have he : {v : FinitePlace K | ∃ i, v (z i) ≠ 1} =
      ⋃ i, Function.mulSupport (fun v : FinitePlace K => v (z i)) := by
    ext v
    simp
  rw [he]
  exact Set.finite_iUnion (fun i => FinitePlace.hasFiniteMulSupport (hz i))

omit [NumberField K] in
/-- Multiplicativity gives the constant depth sum on each nonzero fiber at
    every absolute value; neither the embeddings nor the field are fixed. -/
lemma raw_fiber_identity (v : AbsoluteValue K ℝ) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    -Real.log (v a) + -Real.log (v b) = -Real.log (v (a * b)) := by
  rw [map_mul, Real.log_mul (v.pos ha).ne' (v.pos hb).ne']
  ring

/-- The algebraic inversion identity used both by the unbounded tree argument
    and the bounded Mobius argument. This is valid in any field. -/
lemma paired_coordinate {F : Type u3} [Field F] (a b c d t : F)
    (ha : c ≠ a) (h : (c-a)*(d-b)=t) : d = b + t/(c-a) := by
  have h' : d-b = t/(c-a) := (eq_div_iff (sub_ne_zero.mpr ha)).mpr
    (by simpa [mul_comm] using h)
  rw [← h']
  ring

lemma paired_difference {F : Type u4} [Field F] (a b c d z w t : F)
    (hc : c ≠ a) (hz : z ≠ a)
    (hcd : (c-a)*(d-b)=t) (hzw : (z-a)*(w-b)=t) :
    w-d = t * (c-z) / ((z-a)*(c-a)) := by
  rw [paired_coordinate a b c d t hc hcd, paired_coordinate a b z w t hz hzw]
  field_simp
  ring

lemma finite_raw_ultra (v : FinitePlace K) {x y z : K}
    (_hxy : x ≠ y) (_hyz : y ≠ z) (hxz : x ≠ z) :
    min (-Real.log (v (x-y))) (-Real.log (v (y-z))) ≤ -Real.log (v (x-z)) := by
  have h := v.add_le (x-y) (y-z)
  rw [sub_add_sub_cancel] at h
  have hp : 0 < v (x-z) := FinitePlace.pos_iff.mpr (sub_ne_zero.mpr hxz)
  have hl := Real.log_le_log hp h
  by_cases hc : v (x-y) ≤ v (y-z)
  · rw [max_eq_right hc] at hl
    exact (min_le_right _ _).trans (neg_le_neg hl)
  · rw [max_eq_left (le_of_not_ge hc)] at hl
    exact (min_le_left _ _).trans (neg_le_neg hl)

lemma normalized_log_product_formula (z : K) (hz : z ≠ 0) :
    (∑ v : InfinitePlace K, archWeight v * (-Real.log (v z))) +
      (Module.finrank ℚ K : ℝ)⁻¹ * ∑ᶠ v : FinitePlace K, -Real.log (v z) = 0 := by
  have hh := log_product_formula z hz
  simp only [archWeight, div_eq_mul_inv]
  rw [finsum_neg_distrib]
  have he : (∑ v : InfinitePlace K, (v.mult:ℝ) * (Module.finrank ℚ K : ℝ)⁻¹ * (-Real.log (v z))) =
      -(Module.finrank ℚ K : ℝ)⁻¹ * ∑ v : InfinitePlace K, (v.mult:ℝ) * Real.log (v z) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [he]
  linear_combination -(Module.finrank ℚ K : ℝ)⁻¹ * hh

end WeakPinned.Arithmetic

end
end

end OAI
