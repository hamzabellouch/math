import OAI.Analysis.KadisonKastler.SpectralClipping
import OAI.Analysis.KadisonKastler.TracialCauchySchwarz
import Mathlib.Algebra.Order.BigOperators.Expect

namespace OAI

/-! # Fourth-moment control of the clipping error

The continuous cutoff already used for quotient lifts also supplies the
tracial tail estimate needed to test bimodular operators on bounded balls.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

theorem discardedFunction_square_le_fourth {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) :
    (t * (1 - clippingFunction β t)) ^ 2 ≤ t ^ 4 / β ^ 2 := by
  rw [mul_sub, mul_one, mul_clippingFunction hβ]
  by_cases htβ : t ≤ β
  · rw [min_eq_left htβ, sub_self, zero_pow (by decide)]
    exact div_nonneg (pow_nonneg ht _) (sq_nonneg β)
  · have hβt : β ≤ t := (lt_of_not_ge htβ).le
    rw [min_eq_right hβt]
    apply (le_div_iff₀ (sq_pos_of_pos hβ)).mpr
    have hprod : β * (t - β) ≤ t * t :=
      mul_le_mul hβt (sub_le_self t hβ.le) (sub_nonneg.mpr hβt) ht
    have hs := (sq_le_sq₀ (mul_nonneg hβ.le (sub_nonneg.mpr hβt))
      (mul_nonneg ht ht)).mpr hprod
    nlinarith only [hs]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The discarded square is bounded by the fourth power divided by the
square of the cutoff, in the C*-algebra order. -/
theorem spectralClip_discard_fourth_bound {β : ℝ} (hβ : 0 < β) (x : A) :
    star (x - spectralClip β x) * (x - spectralClip β x) ≤
      (β ^ 2)⁻¹ • (star x * x) ^ 2 := by
  have hcut : x - spectralClip β x =
      x * cfc (fun t => 1 - clippingFunction β t) (CFC.abs x) := by
    rw [cfc_sub (fun _ : ℝ => 1) (clippingFunction β) _ (by fun_prop)
      (clippingFunction_continuous hβ).continuousOn, cfc_const_one ℝ (CFC.abs x),
      mul_sub, mul_one]
    rfl
  have hfour : cfc (fun t : ℝ => t ^ 4) (CFC.abs x) = (star x * x) ^ 2 := by
    rw [cfc_pow_id (R := ℝ) (CFC.abs x) 4 (CFC.abs_nonneg x).isSelfAdjoint]
    calc
      CFC.abs x ^ 4 = (CFC.abs x ^ 2) ^ 2 := by rw [← pow_mul]
      _ = (star x * x) ^ 2 := by rw [pow_two (CFC.abs x), CFC.abs_mul_abs]
  have hright : cfc (fun t : ℝ => t ^ 4 / β ^ 2) (CFC.abs x) =
      (β ^ 2)⁻¹ • (star x * x) ^ 2 := by
    simp_rw [div_eq_mul_inv, mul_comm (_ ^ 4)]
    rw [cfc_const_mul _ (fun t : ℝ => t ^ 4) _ (by fun_prop), hfour]
  rw [hcut, star_mul_cfc_abs x (fun t : ℝ => 1 - clippingFunction β t)
    (continuous_const.sub (clippingFunction_continuous hβ)), ← hright]
  apply (cfc_le_iff _ _ _
    ((continuous_id.mul (continuous_const.sub (clippingFunction_continuous hβ))).pow 2).continuousOn
    (by fun_prop)).mpr
  intro t ht
  exact discardedFunction_square_le_fourth hβ
    (spectrum_nonneg_of_nonneg (CFC.abs_nonneg x) ht)

/-- A positive trace is monotone on selfadjoint elements. -/
theorem FaithfulTracialState.re_mono (τ : FaithfulTracialState A) {x y : A}
    (hxy : x ≤ y) : (τ.toLinearMap x).re ≤ (τ.toLinearMap y).re := by
  obtain ⟨z, hz⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hxy)
  have h := τ.positive z
  rw [← hz, map_sub, Complex.sub_re] at h
  linarith

/-- Fourth moments control the squared tracial norm lost to clipping. -/
theorem traceTwoNorm_spectralClip_discard_sq_le
    (τ : FaithfulTracialState A) {β : ℝ} (hβ : 0 < β) (x : A) :
    traceTwoNorm τ (x - spectralClip β x) ^ 2 ≤
      (τ.toLinearMap ((star x * x) ^ 2)).re / β ^ 2 := by
  have h := τ.re_mono (spectralClip_discard_fourth_bound hβ x)
  rw [traceTwoNorm_sq]
  simpa only [LinearMap.map_smul_of_tower, Complex.smul_re,
    smul_eq_mul, div_eq_mul_inv, mul_comm] using h

theorem traceTwoNorm_spectralClip_le (τ : FaithfulTracialState A)
    {β : ℝ} (hβ : 0 < β) (x : A) :
    traceTwoNorm τ (spectralClip β x) ≤ traceTwoNorm τ x := by
  have h := τ.re_mono (spectralClip_star_mul_self_le hβ x)
  rw [← traceTwoNorm_sq, ← traceTwoNorm_sq] at h
  nlinarith [traceTwoNorm_nonneg τ (spectralClip β x), traceTwoNorm_nonneg τ x]

/-- A uniform fourth-moment bound gives the averaged squared tail bound. -/
theorem expect_traceTwoNorm_spectralClip_discard_sq_le
    {ι : Type*} [Fintype ι] (τ : FaithfulTracialState A) (x : ι → A)
    {β C : ℝ} (hβ : 0 < β)
    (hfour : (𝔼 i, (τ.toLinearMap ((star (x i) * x i) ^ 2)).re) ≤ C) :
    (𝔼 i, traceTwoNorm τ (x i - spectralClip β (x i)) ^ 2) ≤ C / β ^ 2 := by
  calc
    _ ≤ 𝔼 i, (τ.toLinearMap ((star (x i) * x i) ^ 2)).re / β ^ 2 :=
      Finset.expect_le_expect fun i _ => traceTwoNorm_spectralClip_discard_sq_le τ hβ (x i)
    _ = (𝔼 i, (τ.toLinearMap ((star (x i) * x i) ^ 2)).re) / β ^ 2 :=
      (Finset.expect_div _ _ _).symm
    _ ≤ C / β ^ 2 := div_le_div_of_nonneg_right hfour (sq_nonneg β)

end

end KadisonKastler

end OAI
