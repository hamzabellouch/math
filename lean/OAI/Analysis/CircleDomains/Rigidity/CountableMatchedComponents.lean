import OAI.Analysis.CircleDomains.Topology.ComponentRelationSelection
import OAI.Analysis.CircleDomains.Topology.ComponentTopology
import OAI.Analysis.CircleDomains.Topology.BoundedRoundDisks

namespace OAI

/-! The exceptional component pairs in the trace argument are countable:
one side has nonempty interior. Common point pairs remain unrestricted. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem IsComplementaryComponent.eq_component_of_mem {G K : Set Sphere}
    (hK : IsComplementaryComponent G K) {q : Sphere} (hq : q ∈ K) :
    K = connectedComponentIn Gᶜ q := by
  obtain ⟨p,_,rfl⟩ := hK
  exact connectedComponentIn_eq hq

 theorem circle_component_euclidean {G K : Set Sphere}
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hK : IsComplementaryComponent G K) :
    ∃ (c : ℂ) (r : ℝ), 0 ≤ r ∧ K = ((↑) : ℂ → Sphere) '' Metric.closedBall c r := by
  obtain ⟨p,hp,rfl⟩ := hK
  rcases hG.2.2 p hp with ⟨q,he⟩ | hround
  · cases q using OnePoint.rec with
    | infty =>
      have hi : OnePoint.infty ∈ connectedComponentIn Gᶜ p := he.symm ▸ mem_singleton _
      exact ((connectedComponentIn_subset _ _ hi) hinf).elim
    | coe z =>
      refine ⟨z,0,le_rfl,?_⟩
      simpa only [Metric.closedBall_zero,image_singleton] using he
  · obtain ⟨c,r,hr,he⟩ := isRoundClosedDisk_eq_euclidean hround
      (fun h => (connectedComponentIn_subset _ _ h) hinf)
    exact ⟨c,r,hr.le,he⟩

 theorem circle_component_singleton_or_interior {G K : Set Sphere}
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hK : IsComplementaryComponent G K) :
    (∃ q, K = {q}) ∨ (interior K).Nonempty := by
  obtain ⟨p,hp,rfl⟩ := hK
  rcases hG.2.2 p hp with hpoint | hround
  · exact Or.inl hpoint
  · have hn : OnePoint.infty ∉ connectedComponentIn Gᶜ p :=
      fun h => (connectedComponentIn_subset _ _ h) hinf
    obtain ⟨c,r,hr,he⟩ := isRoundClosedDisk_eq_euclidean hround hn
    right
    rw [he]
    refine ⟨(c : Sphere),mem_interior_iff_mem_nhds.mpr ?_⟩
    exact Filter.mem_of_superset ((OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball).mem_nhds
      (mem_image_of_mem _ (Metric.mem_ball_self hr))) (image_mono Metric.ball_subset_closedBall)

namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 def IsMatchedComponentPair (P : Set Sphere × Set Sphere) : Prop :=
  IsComplementaryComponent G P.1 ∧ IsComplementaryComponent (f '' G) P.2 ∧
    ∀ q ∈ P.1, D.targetFiber q = P.2

 theorem IsMatchedComponentPair.fst_injective {P Q : Set Sphere × Set Sphere}
    (hP : D.IsMatchedComponentPair P) (hQ : D.IsMatchedComponentPair Q) (hPQ : P.1 = Q.1) : P = Q := by
  obtain ⟨q,hq⟩ := hP.1.nonempty
  have hq' : q ∈ Q.1 := hPQ ▸ hq
  exact Prod.ext hPQ ((hP.2.2 q hq).symm.trans (hQ.2.2 q hq'))

 theorem equal_target_fibers_equal_source_components (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {q q' : Sphere}
    (hq : q ∈ Gᶜ) (_hq' : q' ∈ Gᶜ) (he : D.targetFiber q = D.targetFiber q') :
    connectedComponentIn Gᶜ q = connectedComponentIn Gᶜ q' := by
  obtain ⟨p,hr⟩ := D.targetFiber_nonempty hG hf q
  obtain ⟨t,ht,hfiber⟩ := D.componentRelation_source_fiber hG hf hq
  have hp : p ∈ (f '' G)ᶜ := by
    apply connectedComponentIn_subset (f '' G)ᶜ t
    rw [← hfiber]
    exact hr
  obtain ⟨s,_,hs⟩ := D.componentRelation_target_fiber hG hf hp
  have hqs : q ∈ connectedComponentIn Gᶜ s := by rw [← hs]; exact hr
  have hq's : q' ∈ connectedComponentIn Gᶜ s := by
    rw [← hs]
    change p ∈ D.targetFiber q'
    rw [← he]
    exact hr
  exact (connectedComponentIn_eq hqs).symm.trans (connectedComponentIn_eq hq's)

 theorem IsMatchedComponentPair.snd_injective (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {P Q : Set Sphere × Set Sphere}
    (hP : D.IsMatchedComponentPair P) (hQ : D.IsMatchedComponentPair Q) (hPQ : P.2 = Q.2) : P = Q := by
  obtain ⟨q,hq⟩ := hP.1.nonempty
  obtain ⟨q',hq'⟩ := hQ.1.nonempty
  have hqG : q ∈ Gᶜ := by
    rw [hP.1.eq_component_of_mem hq] at hq
    exact connectedComponentIn_subset _ _ hq
  have hq'G : q' ∈ Gᶜ := by
    rw [hQ.1.eq_component_of_mem hq'] at hq'
    exact connectedComponentIn_subset _ _ hq'
  have he : D.targetFiber q = D.targetFiber q' :=
    (hP.2.2 q hq).trans (hPQ.trans (hQ.2.2 q' hq').symm)
  apply Prod.ext _ hPQ
  rw [hP.1.eq_component_of_mem hq,hQ.1.eq_component_of_mem hq']
  exact D.equal_target_fibers_equal_source_components hG hf hqG hq'G he

 theorem exists_matched_pair_of_source (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {q : Sphere} (hq : q ∈ Gᶜ) :
    ∃ P : Set Sphere × Set Sphere, D.IsMatchedComponentPair P ∧
      P.1 = connectedComponentIn Gᶜ q := by
  obtain ⟨p,hp,he⟩ := D.componentRelation_source_fiber hG hf hq
  refine ⟨(connectedComponentIn Gᶜ q,connectedComponentIn (f '' G)ᶜ p),
    ⟨⟨q,hq,rfl⟩,⟨p,hp,rfl⟩,?_⟩,rfl⟩
  intro q' hq'
  exact (D.targetFiber_eq_on_component hG hf hq hq').symm.trans he

 theorem exists_matched_pair_of_target (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) {p : Sphere} (hp : p ∈ (f '' G)ᶜ) :
    ∃ P : Set Sphere × Set Sphere, D.IsMatchedComponentPair P ∧
      P.2 = connectedComponentIn (f '' G)ᶜ p := by
  obtain ⟨q,hq,he⟩ := D.componentRelation_target_fiber hG hf hp
  have hr : D.componentRelation q p := by
    change q ∈ {q' | D.componentRelation q' p}
    rw [he]
    exact mem_connectedComponentIn hq
  obtain ⟨P,hP,hPq⟩ := D.exists_matched_pair_of_source hG hf hq
  have hqP : q ∈ P.1 := hPq.symm ▸ mem_connectedComponentIn hq
  have hpP : p ∈ P.2 := by
    rw [← hP.2.2 q hqP]
    exact hr
  exact ⟨P,hP,hP.2.1.eq_component_of_mem hpP⟩

 theorem matched_pair_indexed_or_common_point
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hG' : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    {P : Set Sphere × Set Sphere} (hP : D.IsMatchedComponentPair P) :
    ((interior P.1).Nonempty ∨ (interior P.2).Nonempty) ∨
      ((∃ q, P.1 = {q}) ∧ (∃ p, P.2 = {p})) := by
  rcases circle_component_singleton_or_interior hG hinf hP.1 with hq | hi
  · rcases circle_component_singleton_or_interior hG' hinf' hP.2.1 with hp | hi
    · exact Or.inr ⟨hq,hp⟩
    · exact Or.inl (Or.inr hi)
  · exact Or.inl (Or.inl hi)

 theorem countable_matched_nonpoint_components (hG : IsOpen G)
    (hf : IsConformalEquivalence f G (f '' G)) :
    {P : Set Sphere × Set Sphere | D.IsMatchedComponentPair P ∧
      ((interior P.1).Nonempty ∨ (interior P.2).Nonempty)}.Countable := by
  let A := {P : Set Sphere × Set Sphere | D.IsMatchedComponentPair P ∧ (interior P.1).Nonempty}
  let B := {P : Set Sphere × Set Sphere | D.IsMatchedComponentPair P ∧ (interior P.2).Nonempty}
  have hA : A.Countable :=
    (show MapsTo Prod.fst A {K | IsComplementaryComponent G K ∧ (interior K).Nonempty} from
      fun _ h => ⟨h.1.1,h.2⟩).countable_of_injOn
      (fun _ hP _ hQ he => IsMatchedComponentPair.fst_injective D hP.1 hQ.1 he)
      (countable_complementaryComponents_with_interior G)
  have hB : B.Countable :=
    (show MapsTo Prod.snd B {K | IsComplementaryComponent (f '' G) K ∧ (interior K).Nonempty} from
      fun _ h => ⟨h.1.2.1,h.2⟩).countable_of_injOn
      (fun _ hP _ hQ he => IsMatchedComponentPair.snd_injective D hG hf hP.1 hQ.1 he)
      (countable_complementaryComponents_with_interior (f '' G))
  apply (hA.union hB).mono
  intro P hP
  exact hP.2.elim (fun h => Or.inl ⟨hP.1,h⟩) (fun h => Or.inr ⟨hP.1,h⟩)

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
