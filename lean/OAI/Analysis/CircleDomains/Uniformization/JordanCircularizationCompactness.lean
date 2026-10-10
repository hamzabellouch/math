import OAI.Analysis.CircleDomains.Uniformization.JordanConfigurationExterior
import OAI.Analysis.CircleDomains.Sobolev.ExteriorCoefficientAreaProof
import OAI.Analysis.CircleDomains.Topology.FiniteCircleGreenProof
import OAI.Analysis.CircleDomains.Uniformization.MontelProof
import OAI.Analysis.CircleDomains.Uniformization.HurwitzUnivalentProof

namespace OAI

/-! Normal-family compactness for the actual successive circularizations.
The source exterior radius supplies uniform bounds for every cumulative
map and every omitted component, without assuming a circular limit. -/
open Set Function Metric Filter Asymptotics Bornology
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity.FiniteJordanConfiguration
variable {I : Type*} [Finite I]

lemma circularization_uniform_bounds (C : FiniteJordanConfiguration I) (schedule : ℕ → I)
    {R : ℝ} (hR : 0<R)
    (hsource : ((((↑) : ℂ → Sphere) '' ball 0 R)ᶜ) ⊆ C.region) (n : ℕ) :
    (∀ p ∈ (iterate C schedule n).regionᶜ,
      p ∈ ((↑) : ℂ → Sphere) '' closedBall 0 (3*R)) ∧
    (∀ z : ℂ, z ∈ C.planeRegion → ‖z‖≤4*R →
      ‖finiteCoord (cumulativeMap C schedule n (z : Sphere))‖≤5*R) ∧
    (∀ z : ℂ, 2*R≤‖z‖ →
      ‖finiteCoord (cumulativeMap C schedule n (z : Sphere))-z‖≤2*R^2/‖z‖) := by
  let harea := exteriorCoefficientAreaTheorem planarSchoenflies unorientedFiniteCircleGreenFormula
  have hconf := cumulativeMap_conformal C schedule n
  obtain ⟨fi,heq⟩ := hconf.exists_smooth_inverse C.region_open (iterate C schedule n).region_open
  have hext : ((((↑) : ℂ → Sphere) '' closedBall 0 R)ᶜ) ⊆ C.region :=
    (compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans hsource
  have hc : IsConformalOn (cumulativeMap C schedule n)
      ((((↑) : ℂ → Sphere) '' closedBall 0 R)ᶜ) := fun p hp => hconf.1 p (hext hp)
  obtain ⟨homit,hsmall⟩ := normalized_model_uniform_bound harea heq
    (iterate C schedule n).region_open hR hsource hc (cumulativeMap_principal C schedule n)
  refine ⟨homit,?_,normalized_sphere_model_exterior_decay harea heq hR hsource hc
    (cumulativeMap_principal C schedule n)⟩
  intro z hz hzn
  obtain ⟨w,hw,he⟩ := hsmall z hz hzn
  have hew : w=finiteCoord (cumulativeMap C schedule n (z : Sphere)) := by
    simpa only [finiteCoord_coe] using congrArg finiteCoord he
  simpa only [hew,mem_closedBall,dist_zero_right] using hw

lemma exists_circularization_normal_limit_along (C : FiniteJordanConfiguration I)
    (schedule : ℕ → I) (t : ℕ → ℕ) :
    ∃ (s : ℕ → ℕ) (F : ℂ → ℂ), StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n (z : ℂ) =>
        finiteCoord (cumulativeMap C schedule (t (s n)) (z : Sphere))) F atTop C.planeRegion ∧
      DifferentiableOn ℂ F C.planeRegion ∧ InjOn F C.planeRegion ∧
      (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹) := by
  obtain ⟨R,hR,hsource⟩ := C.exists_exterior_radius
  have hfin (n : ℕ) := (cumulativeMap_conformal C schedule n).1.finite_open_embedding
    C.region_open (cumulativeMap_conformal C schedule n).bijOn.injOn C.infty_mem_region
    (cumulativeMap_principal C schedule n).1
  have hext : {z : ℂ | 2*R≤‖z‖} ⊆ C.planeRegion := by
    intro z hz
    apply hsource
    simpa only [OnePoint.coe_injective.mem_set_image,mem_ball,dist_zero_right,
      mem_compl_iff,not_lt] using (show R≤‖z‖ by change 2*R≤‖z‖ at hz; linarith)
  obtain ⟨s,F,hs,hlim,hd,hi,hn,_⟩ := exists_normalized_univalent_limit montelExhaustion
    hurwitzUnivalentLimit hR (fun _ => C.planeRegion_open)
    (fun _ => C.planeRegion_connected) (fun _ _ _ => Subset.rfl)
    (fun n => (hfin (t n)).1) (fun n => (hfin (t n)).2.2) hext
    (fun n z hz hzn => (circularization_uniform_bounds C schedule hR hsource (t n)).2.1 z hz hzn)
    (fun n => (circularization_uniform_bounds C schedule hR hsource (t n)).2.2)
  exact ⟨s,F,hs,by simpa only [iUnion_const] using hlim,
    by simpa only [iUnion_const] using hd,by simpa only [iUnion_const] using hi,hn⟩

lemma exists_circularization_normal_limit (C : FiniteJordanConfiguration I) (schedule : ℕ → I) :
    ∃ (s : ℕ → ℕ) (F : ℂ → ℂ), StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n (z : ℂ) =>
        finiteCoord (cumulativeMap C schedule (s n) (z : Sphere))) F atTop C.planeRegion ∧
      DifferentiableOn ℂ F C.planeRegion ∧ InjOn F C.planeRegion ∧
      (fun z => F z-z) =O[cobounded ℂ] (fun z => z⁻¹) :=
  exists_circularization_normal_limit_along C schedule id

end CircleDomainRigidity.FiniteJordanConfiguration

end

end OAI
