import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspHardy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspPotential

namespace OAI

/-! The radial energy form of the separated hyperbolic operator.
Integration by parts and coercivity are proved on compactly supported
complex test functions, including the actual nonzero-frequency potential. -/
noncomputable section
open MeasureTheory Function
namespace CubicFirstMoment

lemma cubicTheta_inner_compact {f g : ℝ → ℂ} (hc : HasCompactSupport f) :
    HasCompactSupport (fun t => inner ℝ (f t) (g t)) := by
  apply hc.mono'
  intro t ht
  by_contra hn
  have hz : f t=0 := image_eq_zero_of_notMem_tsupport hn
  exact ht (by simp [hz])

lemma cubicTheta_inner_integrable {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hc : HasCompactSupport f) : Integrable (fun t => inner ℝ (f t) (g t)) :=
  (hf.inner hg).integrable_of_hasCompactSupport (cubicTheta_inner_compact hc)

lemma cubicTheta_test_integrationByParts {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport f) :
    (∫ t : ℝ, inner ℝ (f t) (deriv g t))=
      -(∫ t : ℝ, inner ℝ (deriv f t) (g t)) := by
  have hdf := hf.continuous_deriv le_rfl
  have hdg := hg.continuous_deriv le_rfl
  have h₀ := cubicTheta_inner_integrable hf.continuous hdg hc
  have h₁ := cubicTheta_inner_integrable hdf hg.continuous hc.deriv
  have hD t : HasDerivAt (fun t => inner ℝ (f t) (g t))
      (inner ℝ (f t) (deriv g t)+inner ℝ (deriv f t) (g t)) t :=
    ((hf.differentiable (by norm_num) t).hasDerivAt).inner ℝ
      ((hg.differentiable (by norm_num) t).hasDerivAt)
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hD (h₀.add h₁)
    (cubicTheta_inner_integrable hf.continuous hg.continuous hc)
  rw [integral_add h₀ h₁] at hzero
  linarith

def cubicThetaRadialOperator (A : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  -deriv (deriv f) t+(1+A*Real.exp (2*t):ℝ) • f t

lemma cubicThetaRadialOperator_energy {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (A : ℝ) :
    (∫ t : ℝ, inner ℝ (f t) (cubicThetaRadialOperator A f t))=
      (∫ t : ℝ, ‖deriv f t‖^2)+(∫ t : ℝ, ‖f t‖^2)+
        ∫ t : ℝ, A*Real.exp (2*t)*‖f t‖^2 := by
  have hf₁ : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hdf : ContDiff ℝ 1 (deriv f) := contDiff_iff_contDiffAt.mpr (fun t => hf.contDiffAt.derivWithin (m:=1) (by norm_num))
  have hddf : Continuous (deriv (deriv f)) := hdf.continuous_deriv le_rfl
  have hI := cubicTheta_test_integrationByParts hf₁ hdf hc
  simp only [real_inner_self_eq_norm_sq] at hI
  have hF := cubicTheta_inner_integrable hf.continuous hf.continuous hc
  simp only [real_inner_self_eq_norm_sq] at hF
  have hD := cubicTheta_inner_integrable hf.continuous hddf hc
  have hP : Integrable (fun t : ℝ => A*Real.exp (2*t)*‖f t‖^2) := by
    have hs : HasCompactSupport (fun t : ℝ => ‖f t‖^2) :=
      hc.comp_left (g:=fun z : ℂ => ‖z‖^2) (by simp)
    have hs' : HasCompactSupport (fun t : ℝ => A*Real.exp (2*t)*‖f t‖^2) := hs.mul_left
    have hcont : Continuous (fun t : ℝ => A*Real.exp (2*t)*‖f t‖^2) := by fun_prop
    exact hcont.integrable_of_hasCompactSupport hs'
  have he : (fun t => inner ℝ (f t) (cubicThetaRadialOperator A f t))=
      (fun t => -inner ℝ (f t) (deriv (deriv f) t)+
        (‖f t‖^2+A*Real.exp (2*t)*‖f t‖^2)) := by
    funext t
    simp only [cubicThetaRadialOperator,inner_add_right,inner_neg_right,
      real_inner_smul_right,real_inner_self_eq_norm_sq]
    ring
  have hi := integral_add hD.neg (hF.add hP)
  simp only [Pi.add_apply,Pi.neg_apply] at hi
  rw [he,hi,integral_neg,integral_add hF hP,hI]
  ring

lemma cubicThetaRadialOperator_coercive {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) {A : ℝ} (hA : 0 ≤ A) :
    (∫ t : ℝ, ‖f t‖^2) ≤ ∫ t : ℝ, inner ℝ (f t) (cubicThetaRadialOperator A f t) := by
  rw [cubicThetaRadialOperator_energy hf hc]
  have hD : 0 ≤ ∫ t : ℝ, ‖deriv f t‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hP : 0 ≤ ∫ t : ℝ, A*Real.exp (2*t)*‖f t‖^2 :=
    integral_nonneg (fun _ => mul_nonneg (mul_nonneg hA (Real.exp_nonneg _)) (sq_nonneg _))
  linarith

end CubicFirstMoment

end

end OAI
