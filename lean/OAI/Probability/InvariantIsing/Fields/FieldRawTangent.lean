import OAI.Probability.InvariantIsing.Fields.FieldAffineMoments

namespace OAI

/-! Gaussian integration by parts identifies the raw affine-noise
tangent with the scalar variance generator already used in the field recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma fieldAmplitudeCurvature_abs_le (a v t : ℝ) {m : ℝ} (hm : 0 < m)
    (hs : m ≤ a + v * t) :
    |fieldAmplitudeCurvature a v t| ≤
      (|v| / 2) * m⁻¹ * (|v| / (2 * Real.sqrt m)) := by
  have hv : 0 < a + v * t := hm.trans_le hs
  rw [fieldAmplitudeCurvature, abs_mul, abs_mul, abs_neg, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_inv,
    Real.sq_sqrt hv.le, abs_of_pos hv]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (inv_anti₀ hm hs) (by positivity))
    (abs_div_two_sqrt_le hm hs v) (abs_nonneg _) (by positivity)

namespace FieldSecondFamily

variable {I : Set ℝ} (F : FieldSecondFamily I)

lemma rawTangent_eq (a v ζ : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ I)
    (hv : 0 < a + v * p.1) :
    (∫ u, F.shiftedTangent a v u p ∂F.toFieldSmoothFamily.affineLaw a v ζ p) =
      F.toFieldSmoothFamily.tangent a v ζ p := by
  let r := Real.sqrt (a + v * p.1)
  let ν := F.toFieldSmoothFamily.affineLaw a v ζ p
  have hiT : Integrable (fun u => F.T (p.1, p.2 + r * u)) ν :=
    F.toFieldSmoothFamily.affineLaw_bounded_integrable a v ζ p
      (F.mT.comp (by fun_prop)) F.KT (fun u => F.bT _ hp)
  have hiZX : Integrable (fun u => u * F.X (p.1, p.2 + r * u)) ν := by
    apply F.toFieldSmoothFamily.affineLaw_linear_integrable a v ζ p
      (measurable_id.mul (F.mX.comp (by fun_prop))) F.kx_nonneg
    intro u
    change |u * F.X (p.1, p.2 + r * u)| ≤ F.KX * (1 + |u|)
    rw [abs_mul]
    calc
      _ ≤ |u| * F.KX := mul_le_mul_of_nonneg_left (F.bX _) (abs_nonneg _)
      _ ≤ F.KX * (1 + |u|) := by nlinarith [F.kx_nonneg]
  have he : (fun u => F.shiftedTangent a v u p) =
      fun u => F.T (p.1, p.2 + r * u) + (v / (2 * r)) * (u * F.X (p.1, p.2 + r * u)) := by
    funext u
    dsimp only [shiftedTangent, fieldAmplitudeSlope, r]
    ring
  rw [he, integral_add hiT (hiZX.const_mul _), integral_const_mul]
  have hibp := field_gaussian_tilted_ibp (F.mU.comp (by fun_prop)) (F.growth p.1)
    (F.mX.comp (by fun_prop)) (F.mXX.comp (by fun_prop))
    (fun y => F.bX (p.1, y)) (fun y => F.bXX (p.1, y))
    (F.spatial p.1) (F.second p.1) r ζ p.2
  change (∫ u, u * F.X (p.1, p.2 + r * u) ∂ν) =
    r * (∫ u, F.XX (p.1, p.2 + r * u) + ζ * (F.X (p.1, p.2 + r * u)) ^ 2 ∂ν) at hibp
  rw [hibp]
  change _ = (∫ u, F.T (p.1, p.2 + r * u) ∂ν) + v / 2 *
    (∫ u, F.XX (p.1, p.2 + r * u) + ζ * (F.X (p.1, p.2 + r * u)) ^ 2 ∂ν)
  have hr : r ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
  field_simp [hr]

end FieldSecondFamily
end InvariantIsing

end

end OAI
