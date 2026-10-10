import OAI.Geometry.SurfaceImmersion.Correction.SmoothingDerivativeBounds
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! First-moment control of the error of the actual convolution operator. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

def firstMoment (K : Base → ℝ) : ℝ := ∫ x, ‖K x‖ * ‖x‖

lemma firstMoment_nonneg (K : Base → ℝ) : 0 ≤ firstMoment K :=
  integral_nonneg fun _x => mul_nonneg (norm_nonneg _) (norm_nonneg _)

lemma firstMoment_dilate (K : Base → ℝ) {s : ℝ} (hs : 0 < s) :
    firstMoment (dilate K s) = s * firstMoment K := by
  have hdim : Module.finrank ℝ Base = 2 := by simp [Base]
  have hn (x : Base) : ‖x‖ = s * ‖s⁻¹ • x‖ := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hs]
    field_simp
  have heq : (fun x => ‖dilate K s x‖ * ‖x‖) =
      fun x => (s / s ^ 2) * ((fun y => ‖K y‖ * ‖y‖) (s⁻¹ • x)) := by
    funext x
    rw [hn x, norm_dilate]
    unfold dilate
    ring
  unfold firstMoment
  rw [heq, integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume (fun x => ‖K x‖ * ‖x‖) hs.le]
  rw [hdim, smul_eq_mul]
  field_simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The smoothing error loses one derivative and gains one power of its scale. -/
theorem smooth_sub_norm_le (r : ℕ) {s C : ℝ} (hs : 0 < s)
    {f : Base → E} (hf : ContDiff ℝ ∞ f)
    (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (x : Base) :
    ‖f x - smooth r s f x‖ ≤ s * firstMoment (kernel r) * C := by
  let K := dilate (kernel r) s
  have hk : HasCompactSupport K := compact_dilate (kernel_compact r) hs.ne'
  have hkc : Continuous K := (smooth_dilate (kernel_smooth r) s).continuous
  have hi₁ : Integrable (fun y => K y • f x) := by
    exact ((hkc.smul continuous_const).integrable_of_hasCompactSupport
      (hk.smul_right (f' := fun _ => f x)))
  have hi₂ : Integrable (fun y => K y • f (x - y)) := by
    exact ((hkc.smul (hf.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (hk.smul_right (f' := fun y => f (x - y))))
  have heq : f x - smooth r s f x = ∫ y, K y • (f x - f (x - y)) := by
    simp_rw [smul_sub]
    rw [integral_sub hi₁ hi₂, integral_smul_const]
    change f x - smooth r s f x = (∫ y, dilate (kernel r) s y) • f x - smooth r s f x
    rw [mass_dilate _ hs, kernel_mass, one_smul]
  have him : Integrable (fun y => ‖K y‖ * ‖y‖ * C) := by
    exact ((hkc.norm.mul continuous_norm).integrable_of_hasCompactSupport
      (hk.norm.mul_right (f' := fun y => ‖y‖))).mul_const C
  rw [heq]
  calc
    _ ≤ ∫ y, ‖K y‖ * ‖y‖ * C := by
      apply norm_integral_le_of_norm_le him
      exact Filter.Eventually.of_forall fun y => by
        rw [norm_smul]
        have h := Convex.norm_image_sub_le_of_norm_fderiv_le
          (s := Set.univ) (fun z _ => hf.differentiable (by simp) z)
          (fun z _ => hb z) convex_univ (Set.mem_univ (x - y)) (Set.mem_univ x)
        have hd : ‖f x - f (x - y)‖ ≤ C * ‖y‖ := by
          simpa only [sub_sub_cancel] using h
        nlinarith [mul_le_mul_of_nonneg_left hd (norm_nonneg (K y))]
    _ = firstMoment K * C := by rw [integral_mul_const]; rfl
    _ = s * firstMoment (kernel r) * C := by rw [firstMoment_dilate _ hs]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
