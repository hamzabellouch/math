import OAI.Analysis.KadisonKastler.TracialProducts

namespace OAI

/-! # The product Hölder inequality for the tracial one-norm -/

namespace KadisonKastler

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

local instance : PartialOrder B := CStarAlgebra.spectralOrder B
local instance : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

/-- The tracial one-norm, using the C*-algebra absolute value. -/
def traceOneNorm (τ : FaithfulTracialState B) (x : B) : ℝ :=
  (τ.toLinearMap (CFC.abs x)).re

private def clippedPolar (ε : ℝ) (x : B) : B := ε⁻¹ • spectralClip ε x

private def clippedPolarFunction (ε t : ℝ) : ℝ :=
  ε⁻¹ * (clippingFunction ε t * t ^ 2)

private theorem clippedPolarFunction_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (clippedPolarFunction ε) :=
  continuous_const.mul ((clippingFunction_continuous hε).mul (continuous_id.pow 2))

private theorem clippedPolarFunction_error {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    0 ≤ t - clippedPolarFunction ε t ∧ t - clippedPolarFunction ε t ≤ ε := by
  by_cases hsmall : t ≤ ε
  · have hmul : ε⁻¹ * t ≤ 1 := by
      have hm := mul_le_mul_of_nonneg_left hsmall (inv_nonneg.mpr hε.le)
      rwa [inv_mul_cancel₀ hε.ne'] at hm
    have ht2 : ε⁻¹ * t ^ 2 ≤ t := by
      have hm := mul_le_mul_of_nonneg_right hmul ht
      nlinarith
    have hn : 0 ≤ ε⁻¹ * t ^ 2 := mul_nonneg (inv_nonneg.mpr hε.le) (sq_nonneg t)
    simp only [clippedPolarFunction, clippingFunction, max_eq_left hsmall,
      div_self hε.ne', one_mul]
    constructor <;> linarith
  · have hlarge : ε ≤ t := (le_of_lt (lt_of_not_ge hsmall))
    have htpos : 0 < t := hε.trans_le hlarge
    have heq : clippedPolarFunction ε t = t := by
      simp only [clippedPolarFunction, clippingFunction, max_eq_right hlarge]
      field_simp
    rw [heq, sub_self]
    exact ⟨le_rfl, hε.le⟩

private theorem clippedPolar_norm_le {ε : ℝ} (hε : 0 < ε) (x : B) :
    ‖clippedPolar ε x‖ ≤ 1 := by
  rw [clippedPolar, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
  calc
    ε⁻¹ * ‖spectralClip ε x‖ ≤ ε⁻¹ * ε :=
      mul_le_mul_of_nonneg_left (spectralClip_norm_le hε x) (inv_nonneg.mpr hε.le)
    _ = 1 := inv_mul_cancel₀ hε.ne'

private theorem clippedPolar_pair (ε : ℝ) (hε : 0 < ε) (x : B) :
    star (clippedPolar ε x) * x = cfc (clippedPolarFunction ε) (CFC.abs x) := by
  have hf := clippingFunction_continuous hε
  have hfstar : star (cfc (clippingFunction ε) (CFC.abs x)) =
      cfc (clippingFunction ε) (CFC.abs x) :=
    (cfc_predicate (clippingFunction ε) (CFC.abs x)).star_eq
  calc
    star (clippedPolar ε x) * x =
        ε⁻¹ • (cfc (clippingFunction ε) (CFC.abs x) * (star x * x)) := by
      simp only [clippedPolar, spectralClip, star_smul, star_mul, star_trivial,
        hfstar, smul_mul_assoc, mul_assoc]
    _ = ε⁻¹ • (cfc (clippingFunction ε) (CFC.abs x) *
        cfc (fun t : ℝ => t ^ 2) (CFC.abs x)) := by
      rw [cfc_pow_id (R := ℝ) _ 2, pow_two, CFC.abs_mul_abs]
    _ = ε⁻¹ • cfc (fun t => clippingFunction ε t * t ^ 2) (CFC.abs x) := by
      rw [← cfc_mul (clippingFunction ε) (fun t : ℝ => t ^ 2) _
        hf.continuousOn (by fun_prop)]
    _ = cfc (clippedPolarFunction ε) (CFC.abs x) := by
      change ε⁻¹ • cfc (fun t => clippingFunction ε t * t ^ 2) (CFC.abs x) =
        cfc (fun t => ε⁻¹ * (clippingFunction ε t * t ^ 2)) (CFC.abs x)
      rw [cfc_const_mul ε⁻¹ _ _ (by fun_prop)]

/-- The clipped polar contraction recovers the absolute value with an
operator-norm error at most the cutoff. -/
private theorem clippedPolar_pair_error {ε : ℝ} (hε : 0 < ε) (x : B) :
    ‖CFC.abs x - star (clippedPolar ε x) * x‖ ≤ ε := by
  rw [clippedPolar_pair ε hε x]
  have he : CFC.abs x - cfc (clippedPolarFunction ε) (CFC.abs x) =
      cfc (fun t : ℝ => t - clippedPolarFunction ε t) (CFC.abs x) := by
    rw [cfc_sub (fun t : ℝ => t) (clippedPolarFunction ε) (CFC.abs x)
      continuous_id.continuousOn (clippedPolarFunction_continuous hε).continuousOn,
      cfc_id' ℝ (CFC.abs x)]
  rw [he]
  apply norm_cfc_le hε.le
  intro t ht
  obtain ⟨h0, h1⟩ := clippedPolarFunction_error hε
    (spectrum_nonneg_of_nonneg (CFC.abs_nonneg x) ht)
  simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using h1

/-- The explicit normalized spectral clip is a contraction. -/
theorem normalized_spectralClip_norm_le {ε : ℝ} (hε : 0 < ε) (x : B) :
    ‖ε⁻¹ • spectralClip ε x‖ ≤ 1 :=
  clippedPolar_norm_le hε x

/-- Approximate duality with an explicit continuous cutoff formula. -/
theorem traceOneNorm_le_normalized_spectralClip_pair (τ : FaithfulTracialState B)
    (x : B) {ε : ℝ} (hε : 0 < ε) :
    traceOneNorm τ x ≤
      (τ.toLinearMap (star (ε⁻¹ • spectralClip ε x) * x)).re + ε := by
  have htrace := (Complex.re_le_norm (τ.toLinearMap
      (CFC.abs x - star (clippedPolar ε x) * x))).trans
    ((τ.norm_apply_le_norm _).trans (clippedPolar_pair_error hε x))
  rw [map_sub, Complex.sub_re] at htrace
  exact (sub_le_iff_le_add.mp htrace).trans_eq (add_comm _ _)

/-- The tracial one-norm is recovered, to arbitrary accuracy, by pairing
with a contraction in the algebra. -/
theorem traceOneNorm_approx_dual (τ : FaithfulTracialState B) (x : B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : B, ‖v‖ ≤ 1 ∧ traceOneNorm τ x ≤
      (τ.toLinearMap (star v * x)).re + ε := by
  refine ⟨clippedPolar ε x, clippedPolar_norm_le hε x, ?_⟩
  have htrace := (Complex.re_le_norm (τ.toLinearMap
      (CFC.abs x - star (clippedPolar ε x) * x))).trans
    ((τ.norm_apply_le_norm _).trans (clippedPolar_pair_error hε x))
  rw [map_sub, Complex.sub_re] at htrace
  exact (sub_le_iff_le_add.mp htrace).trans_eq (add_comm _ _)

/-- Product Hölder inequality, proved through the clipped polar
contractions and Cauchy–Schwarz. -/
theorem traceOneNorm_mul_le (τ : FaithfulTracialState B) (x y : B) :
    traceOneNorm τ (x * y) ≤ traceTwoNorm τ x * traceTwoNorm τ y := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨v, hv, happ⟩ := traceOneNorm_approx_dual τ (x * y) hε
  have hcs : (τ.toLinearMap (star v * (x * y))).re ≤
      traceTwoNorm τ (star x * v) * traceTwoNorm τ y := by
    have he : star (star x * v) * y = star v * (x * y) := by
      simp only [star_mul, star_star, mul_assoc]
    rw [← he]
    exact (Complex.re_le_norm _).trans (τ.cauchySchwarz _ _)
  have hnorm : traceTwoNorm τ (star x * v) ≤ traceTwoNorm τ x := by
    calc
      traceTwoNorm τ (star x * v) ≤ traceTwoNorm τ (star x) * ‖v‖ :=
        traceTwoNorm_mul_le_right τ _ _
      _ ≤ traceTwoNorm τ (star x) * 1 :=
        mul_le_mul_of_nonneg_left hv (traceTwoNorm_nonneg τ _)
      _ = traceTwoNorm τ x := by rw [mul_one, traceTwoNorm_star]
  have hb := hcs.trans (mul_le_mul_of_nonneg_right hnorm (traceTwoNorm_nonneg τ y))
  linarith

end

end KadisonKastler

end OAI
