import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGluedAverage
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRegularPrimitive
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace OAI

/-! Smoothness through the origin for the actual regular Volterra solutions. -/

open Set MeasureTheory
open scoped ContDiff BoundedContinuousFunction
namespace DefocusingNLS

theorem homogeneousGlued_average_congr (d : ℕ) (h R : ℝ) (f g : ℝ → ℂ)
    (he : EqOn f g (Icc 0 R)) (r : ℝ) (hr : r ∈ Icc 0 R) :
    spectralRegularAverage d h f r = spectralRegularAverage d h g r := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  have hrt : r * t ∈ Icc 0 R :=
    ⟨mul_nonneg hr.1 ht.1, (mul_le_of_le_one_right hr.1 ht.2).trans hr.2⟩
  dsimp only
  rw [he hrt]

theorem homogeneousGlued_regular_origin (d : ℕ) (R α : ℝ)
    (hR : 0 < R) (hα : 0 < α) (A B : ℝ →ᵇ ℂ) (cp cm : ℂ) (c : ℂ × ℂ)
    (v s : RegularSpectralSpace)
    (hv : v = spectralRegularInitial R α hα.le c + spectralRegularPairKernel d R α hR.le hα s)
    (hs : s = spectralRegularSourceCLM A B cp cm v)
    (hA : ContDiffOn ℝ ∞ A (Icc 0 R)) (hB : ContDiffOn ℝ ∞ B (Icc 0 R)) :
    ContDiffOn ℝ ∞ (spectralRegularLift d α c s) (Icc 0 R) := by
  let F := fun r => (spectralRegularLift d α c s r).1
  let G := fun r => (spectralRegularLift d α c s r).2
  have he (r : ℝ) (hr : r ∈ Icc 0 R) :=
    spectralRegularLift_source d R α hR.le hα A B cp cm c v s hv hs r hr
  have hep : EqOn (spectralRegularWeightedSource α s.1)
      (fun r => A r * F r + B r * G r - cp * F r) (Icc 0 R) := by
    intro r hr
    exact congrArg Prod.fst (he r hr)
  have hem : EqOn (spectralRegularWeightedSource α s.2)
      (fun r => star (B r) * F r + star (A r) * G r - cm * G r) (Icc 0 R) := by
    intro r hr
    exact congrArg Prod.snd (he r hr)
  have hdF (r : ℝ) (hr : r ∈ Icc 0 R) : HasDerivWithinAt F
      ((r : ℂ) * spectralRegularAverage d 1
        (fun t => A t * F t + B t * G t - cp * F t) r) (Icc 0 R) r := by
    have hd := ((ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r
      (spectralRegularLift_hasDerivAt d α c s r)).hasDerivWithinAt
      (s := Icc 0 R)
    simp only [ContinuousLinearMap.coe_fst'] at hd
    rw [homogeneousGlued_average_congr d 1 R _ _ hep r hr] at hd
    exact hd
  have hdG (r : ℝ) (hr : r ∈ Icc 0 R) : HasDerivWithinAt G
      ((r : ℂ) * spectralRegularAverage d (-1)
        (fun t => star (B t) * F t + star (A t) * G t - cm * G t) r) (Icc 0 R) r := by
    have hd := ((ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r
      (spectralRegularLift_hasDerivAt d α c s r)).hasDerivWithinAt
      (s := Icc 0 R)
    simp only [ContinuousLinearMap.coe_snd'] at hd
    rw [homogeneousGlued_average_congr d (-1) R _ _ hem r hr] at hd
    exact hd
  obtain ⟨hf, hg⟩ := homogeneousGlued_origin_smooth d R hR A B cp cm hA hB F G
    (spectralRegularLift_continuous d α c s).fst.continuousOn
    (spectralRegularLift_continuous d α c s).snd.continuousOn hdF hdG
  exact hf.prodMk hg

theorem homogeneousGlued_regular_physical_origin (ell d : ℕ) (R α : ℝ)
    (hR : 0 < R) (hα : 0 < α) (A B : ℝ →ᵇ ℂ) (cp cm : ℂ) (c : ℂ × ℂ)
    (v s : RegularSpectralSpace)
    (hv : v = spectralRegularInitial R α hα.le c + spectralRegularPairKernel d R α hR.le hα s)
    (hs : s = spectralRegularSourceCLM A B cp cm v)
    (hA : ContDiffOn ℝ ∞ A (Icc 0 R)) (hB : ContDiffOn ℝ ∞ B (Icc 0 R)) :
    ContDiffOn ℝ ∞
      (fun r => (spectralAngularPair ell (spectralRegularState d α c s) r).1.1) (Icc 0 R) ∧
    ContDiffOn ℝ ∞
      (fun r => (spectralAngularPair ell (spectralRegularState d α c s) r).2.1) (Icc 0 R) := by
  have hL := homogeneousGlued_regular_origin d R α hR hα A B cp cm c v s hv hs hA hB
  have hp : ContDiffOn ℝ ∞ (fun r : ℝ => (r : ℂ) ^ ell) (Icc 0 R) :=
    (Complex.ofRealCLM.contDiff.pow ell).contDiffOn
  exact ⟨hp.mul hL.fst, hp.mul hL.snd⟩

end DefocusingNLS

end OAI
