import OAI.Analysis.CircleDomains.Topology.ComponentShrinkingSequence
import OAI.Analysis.CircleDomains.Uniformization.UniformLimitFibers

namespace OAI

/-! The sphere realization of the actual component quotient. The map is
constructed as a uniform limit of shrinking homeomorphisms. A simultaneous
quotient-valued inverse limit proves the exact, rather than approximate,
fiber identity. No sphere decomposition theorem is assumed. -/
open Set Function Filter TopologicalSpace
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric

lemma componentSphereQuotient_of_shrinking
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hc : IsConnected G) (hi : ∞ ∈ G) :
    ∃ π : Sphere → Sphere, Continuous π ∧ IsClosedMap π ∧ Surjective π ∧
      (∀ x y, π x=π y ↔ x=y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) ∧
      IsTotallyDisconnected (π '' G)ᶜ := by
  let : MetrizableSpace (ComponentQuotient G) := componentQuotient_metrizable hG
  let : MetricSpace (ComponentQuotient G) := metrizableSpaceMetric (ComponentQuotient G)
  let q := componentProjection G
  have hq : Continuous q := componentProjection_continuous G
  have hconstant : ∀ x ∈ Gᶜ, ∀ y ∈ connectedComponentIn Gᶜ x, q y=q x := by
    intro x hx y hy
    exact ((componentProjection_eq G x y).mpr (Or.inr ⟨hx,hy⟩)).symm
  obtain ⟨H,hsmall,hforward,hinverse⟩ :=
    exists_sphere_component_shrink hsard hsch hG hc hi q hq hconstant
  obtain ⟨f,hf,_⟩ := exists_continuous_uniformLimit_of_geometric_steps
    (fun n => (H n : Sphere → Sphere)) (fun n => (H n).continuous) 2 (by
      intro n x
      rw [dist_comm]
      exact (hforward n x).le)
  obtain ⟨g,hg,_⟩ := exists_continuous_uniformLimit_of_geometric_steps
    (fun n x => q ((H n).symm x)) (fun n => hq.comp (H n).symm.continuous) 1 (by
      intro n x
      rw [dist_comm,one_mul]
      exact (hinverse n x).le)
  have hgf : ∀ x, g (f x)=q x :=
    uniform_limit_inverse_observation H q g.continuous hf hg
  have hsurj : Surjective f := surjective_uniform_limit f.continuous
    (fun n => (H n : Sphere → Sphere)) (fun n => (H n).surjective) hf
  have hr : ∀ x y, f x=f y ↔ x=y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x) := by
    intro x y
    constructor
    · intro h
      apply (componentProjection_eq G x y).mp
      change q x=q y
      rw [← hgf x,← hgf y,h]
    · rintro (rfl | ⟨hx,hy⟩)
      · rfl
      · exact uniform_limit_eq_of_shrinking_distance hf (fun n => (hsmall n x hx y hy).le)
  exact ⟨f,f.continuous,f.continuous.isClosedMap,hsurj,hr,
    totallyDisconnected_of_component_collapse G hG f f.continuous
      f.continuous.isClosedMap hsurj hr⟩

end CircleDomainRigidity

end

end OAI
