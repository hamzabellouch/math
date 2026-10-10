import OAI.Analysis.CircleDomains.Transfer.GlobalCoreExtension
import OAI.Analysis.CircleDomains.Uniformization.ConformalFiniteEmbedding
import OAI.Analysis.CircleDomains.Topology.ConformalBoundaryApproach

namespace OAI

/-! Finite coordinates of the actual compact-core extension are
continuous on boundary collars and holomorphic on their exterior side. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {I:Type*} [Finite I] {C:FiniteJordanConfiguration I}

omit [Finite I] in
lemma finite_core_image_ne_infty {E:Sphere→Sphere}
    (hi:InjOn E (closure C.region)) (hfix:E ∞=∞)
    {z:ℂ} (hz:(z:Sphere)∈closure C.region) : E (z:Sphere)≠∞ := by
  intro he
  have heq : (z:Sphere)=∞ := hi hz (subset_closure C.infty_mem_region) (he.trans hfix.symm)
  exact OnePoint.coe_ne_infty z heq

omit [Finite I] in
lemma finite_core_trace_continuousOn {E:Sphere→Sphere}
    (hc:ContinuousOn E (closure C.region)) (hi:InjOn E (closure C.region)) (hfix:E ∞=∞)
    {A:Set ℂ} {β:ℂ→ℂ} (hβ:ContinuousOn β A)
    (hm:∀z∈A,(β z:Sphere)∈closure C.region) :
    ContinuousOn (fun z => finiteCoord (E (β z:Sphere))) A := by
  have hec : ContinuousOn (fun z => E (β z:Sphere)) A :=
    hc.comp (OnePoint.continuous_coe.comp_continuousOn hβ) hm
  intro z hz
  exact ContinuousAt.comp_continuousWithinAt (f := fun w : ℂ => E (β w:Sphere))
    (continuousAt_finiteCoord_of_ne_infty (finite_core_image_ne_infty hi hfix (hm z hz))) (hec z hz)

lemma finite_core_trace_differentiableAt {E f:Sphere→Sphere} {V:Set Sphere}
    (he:EqOn E f C.region) (hf:IsConformalEquivalence f C.region V) (hfix:f ∞=∞)
    {β:ℂ→ℂ} {z:ℂ} (hβ:DifferentiableAt ℂ β z) (hz:(β z:Sphere)∈C.region) :
    DifferentiableAt ℂ (fun w => finiteCoord (E (β w:Sphere))) z := by
  have hfin : f (β z:Sphere)≠∞ := finite_image_of_fixes_infty hf.bijOn.injOn
    C.infty_mem_region hfix hz
  have hfd := (analyticAt_finite_map_of_conformal C.region_open hf.1 hz hfin).differentiableAt
  have hd := hfd.comp z hβ
  have hnear : ∀ᶠw in 𝓝 z,(β w:Sphere)∈C.region :=
    (OnePoint.continuous_coe.continuousAt.comp hβ.continuousAt).eventually
      (C.region_open.mem_nhds hz)
  have heq : (fun w => finiteCoord (E (β w:Sphere))) =ᶠ[𝓝 z]
      (fun w => finiteCoord (f (β w:Sphere))) := by
    filter_upwards [hnear] with w hw
    rw [he hw]
  exact heq.differentiableAt_iff.mpr hd

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
