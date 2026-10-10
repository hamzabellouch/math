import OAI.Analysis.CircleDomains.Reflection.ClosedExteriorExtension
import OAI.Analysis.CircleDomains.Topology.CyclicBoundaryCorrespondence

namespace OAI

/-! Each actual circularization step extends to a homeomorphism of the
entire compact finite core. The construction is restricted from the
proved closed-exterior extension. -/
open Set Function Filter Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {I:Type*} [Finite I] {C:FiniteJordanConfiguration I} {j:I}

omit [Finite I] in
lemma Step.exists_core_correspondence_exact (q:Step C j)
    (ha:IsAnalyticJordanCap (C.hole j)) :
    ∃e : closure C.region ≃ₜ closure q.target.region,
      (∀p, (e p:Sphere)=(exteriorDiskNormalization q.center q.radius q.radius_pos).symm
        (extendFrom (closedTerminalCap (C.hole j))ᶜ
          (exteriorDiskNormalization q.center q.radius q.radius_pos ∘ q.map) p)) ∧
      ∀p : closure C.region, (p:Sphere)∈C.region → (e p:Sphere)=q.map p := by
  let U := (closedTerminalCap (C.hole j))ᶜ
  let T := exteriorDiskNormalization q.center q.radius q.radius_pos
  let E := T.symm ∘ extendFrom U (T ∘ q.map)
  have hCU : C.region⊆U := by
    intro p hp hpj
    exact hp (mem_iUnion.mpr ⟨j,hpj⟩)
  have hCUc : closure C.region⊆closure U := closure_mono hCU
  obtain ⟨hc,he,hi,_⟩ := analytic_closed_exterior_extension ha q.radius_pos q.exterior_conformal
  change ContinuousOn E (closure U) at hc
  change EqOn E q.map U at he
  change InjOn E (closure U) at hi
  have hc' := hc.mono hCUc
  have he' : EqOn E q.map C.region := he.mono hCU
  have him : E '' closure C.region=closure q.target.region := by
    rw [closed_extension_image_of_compact isClosed_closure.isCompact hc' he',
      q.conformal.bijOn.image_eq]
  have hb : BijOn E (closure C.region) (closure q.target.region) :=
    ⟨fun p hp => him ▸ mem_image_of_mem E hp,hi.mono hCUc,fun p hp => by
      rw [←him] at hp
      exact hp⟩
  let : CompactSpace (closure C.region) := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  let e : closure C.region ≃ closure q.target.region :=
    Equiv.ofBijective (hb.mapsTo.restrict E _ _) hb.bijective
  have hec : Continuous e := hc'.mapsToRestrict hb.mapsTo
  refine ⟨hec.homeoOfEquivCompactToT2,fun _ => rfl,?_⟩
  intro p hp
  exact he' hp

omit [Finite I] in
lemma Step.exists_core_correspondence (q:Step C j)
    (ha:IsAnalyticJordanCap (C.hole j)) :
    ∃e : closure C.region ≃ₜ closure q.target.region,
      ∀p : closure C.region, (p:Sphere)∈C.region → (e p:Sphere)=q.map p := by
  obtain ⟨e,_,he⟩ := q.exists_core_correspondence_exact ha
  exact ⟨e,he⟩

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
