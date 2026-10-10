import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.Model
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

namespace OAI

/-! C1 functions with square-integrable classical partials belong to the
actual weak H1 domain. Only the test function needs compact support; this
allows the decaying manufactured orbitals and their finite Slater sums. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem complex_C1_test_ibp {n : ℕ} (f : Configuration n → ℂ) (hf : ContDiff ℝ 1 f)
    (φ : Configuration n → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (v : Configuration n) :
    (∫ x, f x * (fderiv ℝ φ x v : ℂ)) = -(∫ x, fderiv ℝ f x v * (φ x : ℂ)) := by
  let g : Configuration n → ℂ := fun x => (φ x : ℂ)
  have hg : ContDiff ℝ 1 g := Complex.ofRealCLM.contDiff.comp hφ
  have hgc : HasCompactSupport g := hc.comp_left Complex.ofReal_zero
  have hd (x : Configuration n) : fderiv ℝ g x v = (fderiv ℝ φ x v : ℂ) :=
    congrArg (fun L : Configuration n →L[ℝ] ℂ => L v)
      ((Complex.ofRealCLM.hasFDerivAt.comp x (hφ.differentiable (by norm_num) x).hasFDerivAt).fderiv)
  have hf' : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hg' : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hi1 : Integrable (fun x => fderiv ℝ f x v * g x) :=
    (hf'.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hi2 : Integrable (fun x => f x * fderiv ℝ g x v) :=
    (hf.continuous.mul hg').integrable_of_hasCompactSupport (hgc.fderiv_apply ℝ v).mul_left
  have hi3 : Integrable (fun x => f x * g x) :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi1 hi2 hi3
    (fun x _ => hf.differentiable (by norm_num) x) (fun x _ => hg.differentiable (by norm_num) x)
  simpa only [hd] using h

def classicalH1State {n : ℕ} (f : SpinConfiguration n → Configuration n → ℂ)
    (hf : ∀ s, ContDiff ℝ 1 (f s)) (hL2 : ∀ s, MemLp (f s) 2)
    (hpartial : ∀ s a, MemLp (fun x => fderiv ℝ (f s) x (EuclideanSpace.single a 1)) 2) :
    Coulomb.H1Vector n where
  value := f
  gradient s a x := fderiv ℝ (f s) x (EuclideanSpace.single a 1)
  value_L2 := hL2
  partial_L2 := hpartial
  weak_partial s a φ hφ hc := complex_C1_test_ibp (f s) (hf s) φ (hφ.of_le (by simp)) hc _

end ContinuumCoulomb

end

end OAI
