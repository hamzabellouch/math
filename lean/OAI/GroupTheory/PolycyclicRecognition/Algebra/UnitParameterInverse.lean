import OAI.GroupTheory.PolycyclicRecognition.Geometry.LocalParameterSmoothness

namespace OAI

/-! # Recovering a map from local parameters with identity derivative -/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Manifold Topology ContDiff

variable {V E M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem regularity_of_unit_parameter
    (P : V → V) (hP : ContDiffAt ℝ ∞ P 0)
    (hd : HasFDerivAt P (ContinuousLinearMap.id ℝ V) 0) (hzero : P 0 = 0)
    (f : V → M) (D : V →L[ℝ] E)
    (hcomp : ContMDiffAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) ∞ (f ∘ P) 0)
    (hdcomp : HasMFDerivAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) (f ∘ P) 0 D) :
    ContMDiffAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) ∞ f 0 ∧
      HasMFDerivAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) f 0 D := by
  let d : V ≃L[ℝ] V := ContinuousLinearEquiv.refl ℝ V
  have hd' : HasFDerivAt P d.toContinuousLinearMap 0 := hd
  let q := hP.localInverse hd' (by simp)
  have hq0 : q 0 = 0 := by
    have hh := hP.localInverse_apply_image hd' (by simp)
    rwa [hzero] at hh
  have hq : ContDiffAt ℝ ∞ q 0 := by
    have hh := hP.to_localInverse hd' (by simp)
    rwa [hzero] at hh
  have hqd : HasFDerivAt q (ContinuousLinearMap.id ℝ V) 0 := by
    have hh := (hP.hasStrictFDerivAt' hd' (by simp)).to_localInverse.hasFDerivAt
    simpa only [q, ContDiffAt.localInverse, d, hzero, ContinuousLinearEquiv.refl_symm,
      ContinuousLinearEquiv.coe_refl] using hh
  have hright : ∀ᶠ x in 𝓝 (0 : V), P (q x) = x := by
    have hh := (hP.hasStrictFDerivAt' hd' (by simp)).eventually_right_inverse
    simpa only [q, ContDiffAt.localInverse, d, hzero, ContinuousLinearEquiv.refl_symm,
      ContinuousLinearEquiv.coe_refl] using hh
  have heq : (f ∘ P) ∘ q =ᶠ[𝓝 0] f := hright.mono fun x hx => congrArg f hx
  constructor
  · exact (hcomp.comp_of_eq hq.contMDiffAt hq0).congr_of_eventuallyEq heq.symm
  · have hdcomp' : HasMFDerivAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) (f ∘ P) (q 0) D := by
      rwa [hq0]
    have hh := hdcomp'.comp 0 hqd.hasMFDerivAt
    have hh' : HasMFDerivAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) ((f ∘ P) ∘ q) 0 D :=
      hh.congr_mfderiv (by ext v; rfl)
    exact hh'.congr_of_eventuallyEq_abuse heq.symm

end PolycyclicRecognition

end

end OAI
