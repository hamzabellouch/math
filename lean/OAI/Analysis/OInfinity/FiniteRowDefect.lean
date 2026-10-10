import OAI.Analysis.OInfinity.FiniteRowIsometry
import OAI.Analysis.OInfinity.ZeroCornerRows

namespace OAI

/-! # Exact defects of the finite row isometry

The explicit finite sum gives both forward and adjoint intertwining errors.
Its range projection is almost central and has small compression of the
source vacuum. These estimates do not discard either complementary corner.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E] [Fintype I] [DecidableEq I]

private lemma row_forward_square (q s t v : E) (a : ℝ)
    (hs : star s * s = 1) (hv : star v * v = q)
    (ht : star t * t = q) (hqt : q * t = t)
    (hc : star v * s * v = (a : ℂ) • t) :
    star (s * v - v * t) * (s * v - v * t) = ((2 - 2 * a : ℝ) : ℂ) • q := by
  have hcs : star v * star s * v = (a : ℂ) • star t := by
    have h := congrArg star hc
    simpa only [star_mul, star_star, star_smul, Complex.star_def,
      Complex.conj_ofReal, mul_assoc] using h
  calc
    _ = star v * (star s * s) * v - (star v * star s * v) * t -
        star t * (star v * s * v) + star t * (star v * v) * t := by
      simp only [star_sub, star_mul]
      noncomm_ring
    _ = q - (a : ℂ) • q - (a : ℂ) • q + q := by
      rw [hs, mul_one, hv, hcs, hc, smul_mul_assoc, mul_smul_comm, ht,
        mul_assoc, hqt, ht]
    _ = _ := by push_cast; module

private lemma row_backward_square (q s t v : E) (a : ℝ)
    (hv : star v * v = q) (htq : t * q = t)
    (hc : star v * s * v = (a : ℂ) • t)
    (hrange : star v * (s * star s) * v = (a : ℂ) • (t * star t)) :
    star (star s * v - v * star t) * (star s * v - v * star t) =
      ((1 - a : ℝ) : ℂ) • (t * star t) := by
  have hcs : star v * star s * v = (a : ℂ) • star t := by
    have h := congrArg star hc
    simpa only [star_mul, star_star, star_smul, Complex.star_def,
      Complex.conj_ofReal, mul_assoc] using h
  calc
    _ = star v * (s * star s) * v - (star v * s * v) * star t -
        t * (star v * star s * v) + t * (star v * v) * star t := by
      simp only [star_sub, star_mul, star_star]
      noncomm_ring
    _ = (a : ℂ) • (t * star t) - (a : ℂ) • (t * star t) -
        (a : ℂ) • (t * star t) + t * star t := by
      rw [hrange, hc, hcs, hv, htq, smul_mul_assoc, mul_smul_comm]
    _ = _ := by push_cast; module

private lemma finiteRow_ratio_sub (m : ℕ) :
    1 - (m : ℝ) / ((m : ℝ) + 1) = ((m : ℝ) + 1)⁻¹ := by
  have h : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The actual range projection of the finite isometry. -/
def finiteRowRange (s t : I → E) (r q : E) (m : ℕ) : E :=
  finiteRowIsometry s t r q m * star (finiteRowIsometry s t r q m)

omit [DecidableEq I] in
lemma finiteRowRange_star (s t : I → E) (r q : E) (m : ℕ) : star (finiteRowRange s t r q m) = finiteRowRange s t r q m := by
  simp only [finiteRowRange, star_mul, star_star]

section Actual

variable (s t : I → E) (r q : E)
    (hq : q * q = q) (hqs : star q = q) (hrr : star r * r = 1)
    (hr : ∀ i, star r * s i = 0)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (htq : ∀ i, t i * q = t i) (ht : ∑ i, t i * star (t i) = q)
    (htt : ∀ i j, star (t i) * t j = if i = j then q else 0)

include htq ht htt in
private lemma finiteRow_target_left (i : I) : q * t i = t i := by
  rw [← ht, Finset.sum_mul]
  have he (j : I) : t j * star (t j) * t i = if j = i then t i else 0 := by
    rw [mul_assoc, htt]
    split_ifs with h
    · subst j; exact htq i
    · exact mul_zero _
  simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

include hq hqs hrr hr hs htq ht htt

lemma finiteRowIsometry_forward_square (m : ℕ) (i : I) :
    star (s i * finiteRowIsometry s t r q m - finiteRowIsometry s t r q m * t i) *
      (s i * finiteRowIsometry s t r q m - finiteRowIsometry s t r q m * t i) =
        ((2 / ((m : ℝ) + 1) : ℝ) : ℂ) • q := by
  have h := row_forward_square q (s i) (t i) (finiteRowIsometry s t r q m)
    ((m : ℝ) / ((m : ℝ) + 1)) (by simpa using hs i i)
    (finiteRowIsometry_gram s t r q hq hqs hrr hr hs htq ht m)
    (by simpa using htt i i) (finiteRow_target_left t q htq ht htt i)
    (finiteRowIsometry_compression s t r q hq hqs hrr hr hs htq ht m i)
  have he : 2 - 2 * ((m : ℝ) / ((m : ℝ) + 1)) = 2 / ((m : ℝ) + 1) := by
    have hne : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  simpa only [he] using h

omit htt in
lemma finiteRowIsometry_backward_square (m : ℕ) (i : I) :
    star (star (s i) * finiteRowIsometry s t r q m - finiteRowIsometry s t r q m * star (t i)) *
      (star (s i) * finiteRowIsometry s t r q m - finiteRowIsometry s t r q m * star (t i)) =
        ((((m : ℝ) + 1)⁻¹ : ℝ) : ℂ) • (t i * star (t i)) := by
  have h := row_backward_square q (s i) (t i) (finiteRowIsometry s t r q m)
    ((m : ℝ) / ((m : ℝ) + 1))
    (finiteRowIsometry_gram s t r q hq hqs hrr hr hs htq ht m) (htq i)
    (finiteRowIsometry_compression s t r q hq hqs hrr hr hs htq ht m i)
    (finiteRowIsometry_range_compression s t r q hq hqs hrr hr hs htq ht m i)
  simpa only [finiteRow_ratio_sub] using h

omit htt in
lemma finiteRowIsometry_vacuum_compression (m : ℕ) :
    star (finiteRowIsometry s t r q m) * (1 - ∑ i, s i * star (s i)) *
      finiteRowIsometry s t r q m = ((((m : ℝ) + 1)⁻¹ : ℝ) : ℂ) • q := by
  rw [mul_sub, mul_one, sub_mul, Finset.mul_sum, Finset.sum_mul]
  simp only [finiteRowIsometry_gram s t r q hq hqs hrr hr hs htq ht,
    finiteRowIsometry_range_compression s t r q hq hqs hrr hr hs htq ht,
    ← Finset.smul_sum, ht]
  have he : (1 : ℂ) - (((m : ℝ) / ((m : ℝ) + 1) : ℝ) : ℂ) =
      ((((m : ℝ) + 1)⁻¹ : ℝ) : ℂ) := by exact_mod_cast finiteRow_ratio_sub m
  calc
    _ = ((1 : ℂ) - (((m : ℝ) / ((m : ℝ) + 1) : ℝ) : ℂ)) • q := by module
    _ = _ := by rw [he]

omit htt in
lemma finiteRowIsometry_norm_le (m : ℕ) : ‖finiteRowIsometry s t r q m‖ ≤ 1 := by
  have hnq : ‖q‖ ≤ 1 := IsStarProjection.norm_le q (isStarProjection_iff'.mpr ⟨hq, hqs⟩)
  have h := congrArg norm (finiteRowIsometry_gram s t r q hq hqs hrr hr hs htq ht m)
  rw [CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg (finiteRowIsometry s t r q m)]

lemma finiteRowIsometry_forward_norm_sq (m : ℕ) (i : I) :
    ‖s i * finiteRowIsometry s t r q m - finiteRowIsometry s t r q m * t i‖ ^ 2 ≤
      2 / ((m : ℝ) + 1) := by
  have h := congrArg norm (finiteRowIsometry_forward_square s t r q hq hqs hrr hr hs htq ht htt m i)
  rw [CStarRing.norm_star_mul_self, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 / ((m : ℝ) + 1))] at h
  rw [pow_two, h]
  exact mul_le_of_le_one_right (by positivity)
    (IsStarProjection.norm_le q (isStarProjection_iff'.mpr ⟨hq, hqs⟩))

lemma finiteRowIsometry_backward_norm_sq (m : ℕ) (i : I) :
    ‖star (s i) * finiteRowIsometry s t r q m - finiteRowIsometry s t r q m * star (t i)‖ ^ 2 ≤
      ((m : ℝ) + 1)⁻¹ := by
  have h := congrArg norm (finiteRowIsometry_backward_square s t r q hq hqs hrr hr hs htq ht m i)
  rw [CStarRing.norm_star_mul_self, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ((m : ℝ) + 1)⁻¹)] at h
  have hnt : ‖t i * star (t i)‖ ≤ 1 := by
    rw [CStarRing.norm_self_mul_star]
    have he := congrArg norm (htt i i)
    simp only [ite_true, CStarRing.norm_star_mul_self] at he
    rw [he]
    exact IsStarProjection.norm_le q (isStarProjection_iff'.mpr ⟨hq, hqs⟩)
  rw [pow_two, h]
  exact mul_le_of_le_one_right (by positivity) hnt


omit htt in
lemma finiteRowRange_sq (m : ℕ) : finiteRowRange s t r q m * finiteRowRange s t r q m = finiteRowRange s t r q m := by
  let v := finiteRowIsometry s t r q m
  have hvg : star v * v = q := finiteRowIsometry_gram s t r q hq hqs hrr hr hs htq ht m
  have hvq : v * q = v := relativeIsometry_mul_support v q hvg hqs hq
  change (v * star v) * (v * star v) = v * star v
  calc
    _ = v * (star v * v) * star v := by noncomm_ring
    _ = _ := by rw [hvg, hvq]

omit htt in
lemma finiteRowRange_vacuum (m : ℕ) :
    finiteRowRange s t r q m * (1 - ∑ i, s i * star (s i)) * finiteRowRange s t r q m =
      ((((m : ℝ) + 1)⁻¹ : ℝ) : ℂ) • finiteRowRange s t r q m := by
  let v := finiteRowIsometry s t r q m
  have hvg : star v * v = q := finiteRowIsometry_gram s t r q hq hqs hrr hr hs htq ht m
  have hvq : v * q = v := relativeIsometry_mul_support v q hvg hqs hq
  calc
    _ = v * (star v * (1 - ∑ i, s i * star (s i)) * v) * star v := by
      change (v * star v) * (1 - ∑ i, s i * star (s i)) * (v * star v) = _
      noncomm_ring
    _ = v * (((((m : ℝ) + 1)⁻¹ : ℝ) : ℂ) • q) * star v := by
      rw [finiteRowIsometry_vacuum_compression s t r q hq hqs hrr hr hs htq ht]
    _ = _ := by rw [mul_smul_comm, smul_mul_assoc, hvq]; rfl

omit htt in
lemma finiteRowRange_vacuum_norm (m : ℕ) :
    ‖finiteRowRange s t r q m * (1 - ∑ i, s i * star (s i)) * finiteRowRange s t r q m‖ ≤
      ((m : ℝ) + 1)⁻¹ := by
  rw [finiteRowRange_vacuum s t r q hq hqs hrr hr hs htq ht,
    norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ ((m : ℝ) + 1)⁻¹)]
  apply mul_le_of_le_one_right (by positivity)
  exact IsStarProjection.norm_le _ (isStarProjection_iff'.mpr
    ⟨finiteRowRange_sq s t r q hq hqs hrr hr hs htq ht m,
      finiteRowRange_star s t r q m⟩)

lemma finiteRowRange_commutator_bound (m : ℕ) (i : I) :
    ‖s i * finiteRowRange s t r q m - finiteRowRange s t r q m * s i‖ ≤
      Real.sqrt (2 / ((m : ℝ) + 1)) + Real.sqrt (((m : ℝ) + 1)⁻¹) := by
  let v := finiteRowIsometry s t r q m
  have hvn : ‖v‖ ≤ 1 := finiteRowIsometry_norm_le s t r q hq hqs hrr hr hs htq ht m
  have hf := finiteRowIsometry_forward_norm_sq s t r q hq hqs hrr hr hs htq ht htt m i
  have hb := finiteRowIsometry_backward_norm_sq s t r q hq hqs hrr hr hs htq ht htt m i
  have hf' : ‖s i * v - v * t i‖ ≤ Real.sqrt (2 / ((m : ℝ) + 1)) := by
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hf
  have hb' : ‖star (s i) * v - v * star (t i)‖ ≤ Real.sqrt (((m : ℝ) + 1)⁻¹) := by
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hb
  have he : s i * (v * star v) - (v * star v) * s i =
      (s i * v - v * t i) * star v - v * star (star (s i) * v - v * star (t i)) := by
    simp only [star_sub, star_mul, star_star]
    noncomm_ring
  change ‖s i * (v * star v) - (v * star v) * s i‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖(s i * v - v * t i) * star v‖ + ‖v * star (star (s i) * v - v * star (t i))‖ := norm_sub_le _ _
    _ ≤ ‖s i * v - v * t i‖ + ‖star (s i) * v - v * star (t i)‖ := by
      apply add_le_add
      · exact (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _)
          (by simpa only [norm_star] using hvn))
      · have hbmul := (norm_mul_le v (star (star (s i) * v - v * star (t i)))).trans
          (mul_le_of_le_one_left (norm_nonneg _) hvn)
        simpa only [norm_star] using hbmul
    _ ≤ _ := add_le_add hf' hb'

end Actual
end WeakPureInfiniteness

end

end OAI
