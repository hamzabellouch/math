import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianStepCalculus

namespace OAI

section

noncomputable section
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem hasDerivAt_dslope_zero_of_analytic {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    HasDerivAt (dslope f 0) (iteratedDeriv 2 f 0/2) 0 := by
  have H := hf.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.hasDerivAt
  change HasDerivAt (dslope f 0)
    ((FormalMultilinearSeries.ofScalars ℝ (fun n => iteratedDeriv n f 0 / n.factorial)).fslope.coeff 1) 0 at H
  norm_num only [FormalMultilinearSeries.coeff_fslope,
    FormalMultilinearSeries.coeff_ofScalars,Nat.reduceAdd,Nat.factorial_two,Nat.cast_ofNat] at H
  exact H

section Mass
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem BoundedDerivs.integrableExpSet_section {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (x : E) : integrableExpSet (fun y => f (x,y)) (gaussianReal 0 1) = Set.univ := by
  ext m
  simp only [mem_univ,iff_true]
  exact hf.exp_integrable m x

 theorem BoundedDerivs.mem_interior_integrableExpSet_section {f : E × ℝ → ℝ}
    (hf : BoundedDerivs f) (x : E) (m : ℝ) :
    m ∈ interior (integrableExpSet (fun y => f (x,y)) (gaussianReal 0 1)) := by
  rw [hf.integrableExpSet_section,interior_univ]
  trivial

theorem gaussianStep_mass_eq_dslope {f : E × ℝ → ℝ} (hf : BoundedDerivs f) (x : E) :
    (fun m => gaussianStep m f x) = dslope (cgf (fun y => f (x,y)) (gaussianReal 0 1)) 0 := by
  funext m
  by_cases hm : m = 0
  · subst m
    rw [dslope_same,deriv_cgf_zero (hf.mem_interior_integrableExpSet_section x 0)]
    simp [gaussianStep]
  · rw [dslope_of_ne _ hm]
    simp only [gaussianStep,ite_eq_right hm,positiveGaussianLogStep,slope,cgf,mgf,sub_zero,
      smul_eq_mul,vsub_eq_sub]
    simp only [zero_mul,Real.exp_zero,integral_const,Measure.real,measure_univ,
      ENNReal.toReal_one,one_smul,Real.log_one,sub_zero]
    ring

theorem gaussianStep_hasDerivAt_mass_zero {f : E × ℝ → ℝ} (hf : BoundedDerivs f) (x : E) :
    HasDerivAt (fun m => gaussianStep m f x)
      (variance (fun y => f (x,y)) (gaussianReal 0 1)/2) 0 := by
  rw [gaussianStep_mass_eq_dslope hf x]
  have ht := hf.mem_interior_integrableExpSet_section x 0
  have H := hasDerivAt_dslope_zero_of_analytic (analyticAt_cgf ht)
  rw [iteratedDeriv_two_cgf ht,deriv_cgf_zero ht] at H
  have hmem : MemLp (fun y => f (x,y)) 2 (gaussianReal 0 1) :=
    memLp_of_mem_interior_integrableExpSet ht 2
  rw [variance_eq_sub hmem]
  simpa only [zero_mul,Real.exp_zero,mul_one,mgf_zero,Measure.real,measure_univ,ENNReal.toReal_one,div_one,
    Pi.pow_apply] using H

theorem gaussianStep_hasDerivAt_mass_ne_zero {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (x : E) {m : ℝ} (hm : m ≠ 0) :
    HasDerivAt (fun a => gaussianStep a f x)
      (((∫ y, f (x,y) ∂gaussianStepLaw m f x)-gaussianStep m f x)/m) m := by
  let g := cgf (fun y => f (x,y)) (gaussianReal 0 1)
  have ht := hf.mem_interior_integrableExpSet_section x m
  have hg := (analyticAt_cgf ht).differentiableAt.hasDerivAt
  have H := hg.div (hasDerivAt_id m) hm
  have he : (fun a => gaussianStep a f x) =ᶠ[𝓝 m] (fun a => g a/a) := by
    filter_upwards [eventually_ne_nhds hm] with a ha
    simp only [gaussianStep,ite_eq_right ha,positiveGaussianLogStep,g,cgf,mgf]
  apply (H.congr_of_eventuallyEq he).congr_deriv
  rw [← integral_tilted_mul_self ht]
  change ((∫ y, f (x,y) ∂gaussianStepLaw m f x)*m-g m*1)/m^2 = _
  simp only [gaussianStep,ite_eq_right hm,positiveGaussianLogStep]
  change _ = ((∫ y, f (x,y) ∂gaussianStepLaw m f x)-g m/m)/m
  field_simp

end Mass

end SK.Analytic

end
end

end OAI
