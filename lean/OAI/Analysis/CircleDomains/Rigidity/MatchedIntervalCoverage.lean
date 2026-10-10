import OAI.Analysis.CircleDomains.Topology.ClosedRelationIntermediateValue
import OAI.Analysis.CircleDomains.Topology.ComponentRelationSelection

namespace OAI

/-! The actual matched end relation covers all scalar values between
selected endpoints of a source segment. No continuity of the selection
at a nontrivial complementary component is assumed. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 theorem targetFiber_isPreconnected (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) (q : Sphere) :
    IsPreconnected (D.targetFiber q) := by
  by_cases hq : q ∈ G
  · have he : D.targetFiber q = {f q} := by
      ext p
      exact ⟨fun hp => D.componentRelation_on_domain hq hp,
        fun hp => (mem_singleton_iff.mp hp) ▸ D.componentRelation_graph hf hq⟩
    rw [he]
    exact isPreconnected_singleton
  · obtain ⟨p,_,he⟩ := D.componentRelation_source_fiber hG hf hq
    change IsPreconnected {p' | D.componentRelation q p'}
    rw [he]
    exact isPreconnected_connectedComponentIn

 theorem interval_fiber_scalar_coverage (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {γ : ℝ → Sphere} (hγ : Continuous γ)
    {φ : Sphere → ℝ} (hφ : Continuous φ) {a b : ℝ} (hab : a ≤ b)
    {pa pb : Sphere} (hpa : D.componentRelation (γ a) pa)
    (hpb : D.componentRelation (γ b) pb)
    {t : ℝ} (ht : t ∈ uIcc (φ pa) (φ pb)) :
    ∃ x ∈ Icc a b, ∃ p, D.componentRelation (γ x) p ∧ φ p = t := by
  let X := Icc a b
  let : PreconnectedSpace X := Subtype.preconnectedSpace isPreconnected_Icc
  let R : X → Sphere → Prop := fun x p => D.componentRelation (γ x) p
  have hR : IsClosed {p : X × Sphere | R p.1 p.2} :=
    (D.componentRelation_closed hf).preimage
      ((hγ.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
  have hne (x : X) : ∃ p, R x p := D.targetFiber_nonempty hG hf (γ x)
  have hc (x : X) : IsPreconnected {p | R x p} := D.targetFiber_isPreconnected hG hf (γ x)
  have ha : a ∈ X := left_mem_Icc.mpr hab
  have hb : b ∈ X := right_mem_Icc.mpr hab
  have hqa : R ⟨a,ha⟩ pa := hpa
  have hqb : R ⟨b,hb⟩ pb := hpb
  rcases le_total (φ pa) (φ pb) with h | h
  · rw [uIcc_of_le h] at ht
    obtain ⟨x,p,hxp,hpt⟩ := closed_relation_intermediate_value hR hne hc hφ hqa hqb ht.1 ht.2
    exact ⟨x,x.property,p,hxp,hpt⟩
  · rw [uIcc_of_ge h] at ht
    obtain ⟨x,p,hxp,hpt⟩ := closed_relation_intermediate_value hR hne hc hφ hqb hqa ht.1 ht.2
    exact ⟨x,x.property,p,hxp,hpt⟩

 theorem interval_scalar_coverage (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {γ : ℝ → Sphere} (hγ : Continuous γ)
    {φ : Sphere → ℝ} (hφ : Continuous φ) {a b : ℝ} (hab : a ≤ b)
    {t : ℝ} (ht : t ∈ uIcc (φ (D.selectedTarget hG hf (γ a)))
      (φ (D.selectedTarget hG hf (γ b)))) :
    ∃ x ∈ Icc a b, ∃ p, D.componentRelation (γ x) p ∧ φ p = t :=
  D.interval_fiber_scalar_coverage hG hf hγ hφ hab
    (D.selectedTarget_mem hG hf (γ a)) (D.selectedTarget_mem hG hf (γ b)) ht

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
