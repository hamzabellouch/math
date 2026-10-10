import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLogMeasure
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support

namespace OAI

/-! The exact radial energy identity and Hardy bound, with the
hyperbolic spectral threshold equal to one. -/
noncomputable section
open MeasureTheory Function
namespace CubicFirstMoment

private lemma norm_square_integrable {f : ℝ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) : Integrable (fun t : ℝ => ‖f t‖^2) := by
  have h : HasCompactSupport (fun t : ℝ => ‖f t‖^2) :=
    hc.comp_left (g:=fun z : ℂ => ‖z‖^2) (by simp)
  exact (hf.norm.pow 2).integrable_of_hasCompactSupport h

private lemma cross_compact {f g : ℝ → ℂ} (hc : HasCompactSupport f) :
    HasCompactSupport (fun t : ℝ => 2*inner ℝ (f t) (g t)) := by
  apply hc.mono' (f':=fun t : ℝ => 2*inner ℝ (f t) (g t))
  intro t ht
  by_contra hn
  have hz : f t=0 := image_eq_zero_of_notMem_tsupport hn
  exact ht (by simp [hz])

private lemma cross_integrable {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hc : HasCompactSupport f) : Integrable (fun t : ℝ => 2*inner ℝ (f t) (g t)) := by
  have hi : Continuous (fun t : ℝ => inner ℝ (f t) (g t)) := hf.inner hg
  exact (continuous_const.mul hi).integrable_of_hasCompactSupport (cross_compact hc)

lemma cubicTheta_log_cross_integral {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    (∫ t : ℝ, 2*inner ℝ (f t) (deriv f t))=0 := by
  have hdc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ‖f t‖^2) (2*inner ℝ (f t) (deriv f t)) t :=
    fun t => ((hf.differentiable (by norm_num)) t).hasDerivAt.norm_sq
  exact integral_eq_zero_of_hasDerivAt_of_integrable hd
    (cross_integrable hf.continuous hdc hc) (norm_square_integrable hf.continuous hc)

theorem cubicTheta_log_energy_identity {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    (∫ t : ℝ, ‖f t+deriv f t‖^2)=
      (∫ t : ℝ, ‖f t‖^2)+(∫ t : ℝ, ‖deriv f t‖^2) := by
  have hdc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have h₀ := norm_square_integrable hf.continuous hc
  have h₁ := norm_square_integrable hdc hc.deriv
  have hcross := cross_integrable hf.continuous hdc hc
  simp_rw [norm_add_sq_real]
  have hi := integral_add (h₀.add hcross) h₁
  simp only [Pi.add_apply] at hi
  rw [hi,integral_add h₀ hcross,
    cubicTheta_log_cross_integral hf hc,add_zero]

theorem cubicTheta_radial_energy_identity {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    (∫ v in Set.Ioi (0:ℝ), ‖deriv (cubicThetaLogLift f) v‖^2/v)=
      (∫ v in Set.Ioi (0:ℝ), ‖cubicThetaLogLift f v‖^2/v^3)+
        ∫ t : ℝ, ‖deriv f t‖^2 := by
  rw [cubicThetaLogLift_energy (hf.differentiable (by norm_num)),
    cubicThetaLogLift_mass,cubicTheta_log_energy_identity hf hc]

theorem cubicTheta_radial_hardy {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    (∫ v in Set.Ioi (0:ℝ), ‖cubicThetaLogLift f v‖^2/v^3) ≤
      (∫ v in Set.Ioi (0:ℝ), ‖deriv (cubicThetaLogLift f) v‖^2/v) := by
  rw [cubicTheta_radial_energy_identity hf hc]
  exact le_add_of_nonneg_right (integral_nonneg (fun _ => sq_nonneg _))

end CubicFirstMoment

end

end OAI
