import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneTestIntegral

namespace OAI

/-! Quantitative error bounds used by the compact-test mass argument. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory

theorem abs_increment_le_of_derivative_bound {F d : ℝ → ℝ} {T C : ℝ}
    (hT : 0 ≤ T) (hc : ContinuousOn F (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt F (d t) t)
    (hb : ∀ t ∈ Ioo 0 T, |d t| ≤ C) : |F T - F 0| ≤ C * T := by
  have hdiff : DifferentiableOn ℝ F (interior (Icc 0 T)) := by
    rw [interior_Icc]
    exact fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
  have hu : ∀ t ∈ interior (Icc 0 T), deriv F t ≤ C := by
    rw [interior_Icc]
    intro t ht
    rw [(hd t ht).deriv]
    exact (abs_le.mp (hb t ht)).2
  have hl : ∀ t ∈ interior (Icc 0 T), -C ≤ deriv F t := by
    rw [interior_Icc]
    intro t ht
    rw [(hd t ht).deriv]
    exact (abs_le.mp (hb t ht)).1
  have hu' := (convex_Icc (0 : ℝ) T).image_sub_le_mul_sub_of_deriv_le hc hdiff hu
    0 ⟨le_rfl, hT⟩ T ⟨hT, le_rfl⟩ hT
  have hl' := (convex_Icc (0 : ℝ) T).mul_sub_le_image_sub_of_le_deriv hc hdiff hl
    0 ⟨le_rfl, hT⟩ T ⟨hT, le_rfl⟩ hT
  apply abs_le.mpr
  constructor <;> linarith

theorem abs_integral_mul_le {f g : Plane → ℝ} (hf : Integrable f)
    (hg : AEStronglyMeasurable g) {C : ℝ} (hb : ∀ x, |g x| ≤ C) :
    |∫ x, f x * g x| ≤ C * ∫ x, |f x| := by
  have hi : Integrable (fun x => f x * g x) := hf.mul_bdd hg (by
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using hb x)
  calc
    _ ≤ ∫ x, |f x * g x| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f x * g x)
    _ ≤ ∫ x, C * |f x| := by
      apply integral_mono hi.norm (hf.norm.const_mul C)
      intro x
      simp only [Real.norm_eq_abs]
      rw [abs_mul]
      simpa only [mul_comm C] using mul_le_mul_of_nonneg_left (hb x) (abs_nonneg (f x))
    _ = _ := integral_const_mul _ _

theorem lower_increment_of_derivative_bound {F d : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn F (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt F (d t) t)
    (hb : ∀ t ∈ Ioo a b, -C ≤ d t) : F a - C * (b - a) ≤ F b := by
  have hdiff : DifferentiableOn ℝ F (interior (Icc a b)) := by
    rw [interior_Icc]
    exact fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
  have hl : ∀ t ∈ interior (Icc a b), -C ≤ deriv F t := by
    rw [interior_Icc]
    intro t ht
    rw [(hd t ht).deriv]
    exact hb t ht
  have h := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hc hdiff hl
    a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
  linarith

end ForcedComputation.VelocityDetector

end

end OAI
