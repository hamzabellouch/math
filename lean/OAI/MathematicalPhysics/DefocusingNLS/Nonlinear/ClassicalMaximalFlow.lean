import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.MaximalStrongSolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace OAI

/-! # The maximal Sobolev flow is a classical solution of the defocusing equation -/

open Set
open scoped ContDiff
namespace DefocusingNLS

def IsClassicalDefocusingFlow (k : ℝ) (hk : 6 < k) (m : ℕ) (f : FourierL2) : Prop :=
  let u := maximalSobolevSchrodingerFlow k hk m f
  let D := maximalSobolevInteractionDomain k hk m f
  u 0 = f ∧ ContinuousOn u D ∧
    ContDiffOn ℝ 1 (fun t => lowerSobolevInclusion (u t)) D ∧
    ∀ t ∈ D, HasDerivAt (fun s => lowerSobolevInclusion (u s))
      (lowerSobolevGenerator (u t) - Complex.I • lowerSobolevInclusion
        (sobolevOddPower k hk m (u t))) t

theorem maximalSobolev_classical (k : ℝ) (hk : 6 < k) (m : ℕ) (f : FourierL2) :
    IsClassicalDefocusingFlow k hk m f := by
  let u := maximalSobolevSchrodingerFlow k hk m f
  let D := maximalSobolevInteractionDomain k hk m f
  let v := fun t => lowerSobolevGenerator (u t) - Complex.I • lowerSobolevInclusion
    (sobolevOddPower k hk m (u t))
  have hu : ContinuousOn u D := continuousOn_maximalSobolevSchrodingerFlow k hk m f
  have hv : ContinuousOn v D :=
    (lowerSobolevGenerator.continuous.comp_continuousOn hu).sub
      ((lowerSobolevInclusion.continuous.comp_continuousOn
        ((contDiff_sobolevOddPower k hk m).continuous.comp_continuousOn hu)).const_smul Complex.I)
  have hd (t : ℝ) (ht : t ∈ D) :
      HasDerivAt (fun s => lowerSobolevInclusion (u s)) (v t) t :=
    hasDerivAt_maximalSobolevSchrodingerFlow k hk m f ht
  have hopen : IsOpen D := isOpen_maximalSobolevInteractionDomain k hk m f
  have hdiff : ContDiffOn ℝ 1 (fun t => lowerSobolevInclusion (u t)) D := by
    rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hopen]
    refine ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · norm_num
    · apply contDiffOn_zero.mpr
      apply hv.congr
      intro t ht
      exact (hd t ht).deriv
  exact ⟨maximalSobolevSchrodingerFlow_initial k hk m f, hu, hdiff, hd⟩

end DefocusingNLS

end OAI
