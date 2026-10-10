import OAI.Analysis.CircleDomains.Selection.CountableConstantPieces
import OAI.Analysis.CircleDomains.Selection.SelectedCoordinateTest
import OAI.Analysis.CircleDomains.Rigidity.MatchedRoundDisks
import OAI.Analysis.CircleDomains.Topology.PlaneComponentRelation

namespace OAI

/-! The actual selected matched field is finite, measurable, and bounded
on every compact part of the source plane. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem planeRelation_ne_infty (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    {z : ℂ} {p : Sphere} (hp : D.planeRelation z p) : p ≠ OnePoint.infty := by
  by_cases hz : (z : Sphere) ∈ G
  · intro he
    have hze : f (z : Sphere) = f OnePoint.infty :=
      (D.componentRelation_on_domain hz hp).symm.trans (he.trans hfix.symm)
    exact OnePoint.coe_ne_infty z (hf.bijOn.injOn hz hinf hze)
  · obtain ⟨q,_,hqe⟩ := D.componentRelation_source_fiber hG hf hz
    have hq : p ∈ connectedComponentIn (f '' G)ᶜ q := hqe ▸ hp
    intro he
    exact (connectedComponentIn_subset _ _ hq) (he.symm ▸ (hfix ▸ mem_image_of_mem f hinf))

 theorem selectedTarget_finite (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (z : ℂ) : D.selectedTarget hG hf (z : Sphere) ≠ OnePoint.infty :=
  D.planeRelation_ne_infty hG hinf hf hfix (D.selectedTarget_mem hG hf _)

 def selectedPlane (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G)) (z : ℂ) : ℂ :=
    finiteCoord (D.selectedTarget hG hf (z : Sphere))

 theorem selectedPlane_measurable [Countable D.IndexedMatchedPair]
    (E : D.MatchedRoundDisks) (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G) :
    Measurable (D.selectedPlane hG.1 hf) := by
  apply measurable_of_countable_constant_pieces
    (fun j => closedBall (E.sourceCenter j) (E.sourceRadius j))
    (fun _ => isClosed_closedBall) (D.selectedPlane hG.1 hf)
    (fun j => D.selectedPlane hG.1 hf (E.sourceCenter j))
  · intro j z hz
    have hc : (E.sourceCenter j : Sphere) ∈ j.val.1 := by
      rw [E.source_eq]
      exact mem_image_of_mem _ (mem_closedBall_self (E.source_nonneg j))
    have hz' : (z : Sphere) ∈ j.val.1 := by rw [E.source_eq]; exact mem_image_of_mem _ hz
    have hcg : (E.sourceCenter j : Sphere) ∈ Gᶜ := by
      rw [j.property.1.1.eq_component_of_mem hc] at hc
      exact connectedComponentIn_subset _ _ hc
    have he := D.selectedTarget_eq_on_component hG.1 hf hcg
      (show (z : Sphere) ∈ connectedComponentIn Gᶜ (E.sourceCenter j : Sphere) by
        rw [← j.property.1.1.eq_component_of_mem hc]; exact hz')
    exact congrArg finiteCoord he.symm
  · intro z hz
    have hsingle := (D.plane_fiber_singleton_or_indexed hG hinf hf hH hinf' z).resolve_right (by
      rintro ⟨j,hj⟩
      rw [E.source_eq] at hj
      obtain ⟨w,hw,hew⟩ := hj
      have hwz : w = z := OnePoint.coe_injective hew
      subst w
      exact hz (mem_iUnion.mpr ⟨j,hw⟩))
    have hs : ContinuousAt (fun z : ℂ => D.selectedTarget hG.1 hf (z : Sphere)) z :=
      (closed_relation_selection_continuousAt (D.planeRelation_closed hf)
        _ (fun z => D.selectedTarget_mem hG.1 hf (z : Sphere)) hsingle)
    have hc : ContinuousAt finiteCoord (D.selectedTarget hG.1 hf (z : Sphere)) :=
      (continuousOn_finiteCoord_of_avoids_infty (S := {OnePoint.infty}ᶜ)
      (by simp)).continuousAt (isOpen_compl_singleton.mem_nhds
        (D.selectedTarget_finite hG.1 hinf hf hfix z))
    exact (hc.comp_of_eq hs rfl).continuousWithinAt

 theorem compact_relation_finite_image (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    {K : Set ℂ} (hK : IsCompact K) :
    IsCompact {w : ℂ | ∃ z ∈ K, ∃ p, D.planeRelation z p ∧ finiteCoord p = w} := by
  let S := (K ×ˢ (univ : Set Sphere)) ∩ {p : ℂ × Sphere | D.planeRelation p.1 p.2}
  have hS : IsCompact S := (hK.prod isCompact_univ).inter_right (D.planeRelation_closed hf)
  have hT := hS.image continuous_snd
  have havoid : OnePoint.infty ∉ Prod.snd '' S := by
    rintro ⟨⟨z,p⟩,hp,he⟩
    exact D.planeRelation_ne_infty hG hinf hf hfix hp.2 he
  have hcont := continuousOn_finiteCoord_of_avoids_infty havoid
  convert hT.image_of_continuousOn hcont using 1
  ext w
  simp only [S,mem_image,mem_inter_iff,mem_prod,mem_univ,and_true,Prod.exists]
  constructor
  · rintro ⟨z,hz,p,hr,rfl⟩
    exact ⟨p,⟨z,p,⟨hz,hr⟩,rfl⟩,rfl⟩
  · rintro ⟨p,⟨z,q,⟨hz,hr⟩,rfl⟩,rfl⟩
    exact ⟨z,hz,q,hr,rfl⟩

 theorem selectedPlane_bounded_on_compact (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    {K : Set ℂ} (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ z ∈ K, ‖D.selectedPlane hG hf z‖ < B := by
  obtain ⟨B,hB,hbound⟩ := (D.compact_relation_finite_image hG hinf hf hfix hK).isBounded.exists_pos_norm_lt
  exact ⟨B,hB,fun z hz => hbound _ ⟨z,hz,_,D.selectedTarget_mem hG hf _,rfl⟩⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
