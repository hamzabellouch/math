import OAI.Analysis.CircleDomains.Rigidity.MatchedScalarIntervals
import OAI.Analysis.CircleDomains.Rigidity.CorrespondenceMaskContinuity

namespace OAI

/-! The closed matched correspondence in the finite source chart. Every
point has a singleton fiber or belongs to one of the actual indexed disks. -/
open Set Function Filter Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} (D : MatchedConformalEnds G f)

 def planeRelation (z : ℂ) (p : Sphere) : Prop := D.componentRelation (z : Sphere) p

 theorem planeRelation_closed (hf : IsConformalEquivalence f G (f '' G)) :
    IsClosed {p : ℂ × Sphere | D.planeRelation p.1 p.2} :=
  (D.componentRelation_closed hf).preimage
    ((OnePoint.continuous_coe.comp continuous_fst).prodMk continuous_snd)

 theorem plane_fiber_singleton_or_indexed
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hG' : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    (z : ℂ) :
    (∀ p, D.planeRelation z p → p = D.selectedTarget hG.1 hf (z : Sphere)) ∨
      ∃ j : D.IndexedMatchedPair, (z : Sphere) ∈ j.val.1 := by
  by_cases hz : (z : Sphere) ∈ G
  · left
    intro p hp
    exact (D.componentRelation_on_domain hz hp).trans (D.selectedTarget_on_domain hG.1 hf hz).symm
  · obtain ⟨P,hP,hPe⟩ := D.exists_matched_pair_of_source hG.1 hf hz
    have hzP : (z : Sphere) ∈ P.1 := by rw [hPe]; exact mem_connectedComponentIn hz
    rcases D.matched_pair_indexed_or_common_point hG hinf hG' hinf' hP with hi | ⟨_,hp⟩
    · exact Or.inr ⟨⟨P,hP,hi⟩,hzP⟩
    · left
      obtain ⟨p,hp⟩ := hp
      have he : D.targetFiber (z : Sphere) = {p} := (hP.2.2 _ hzP).trans hp
      intro t ht
      have ht' : t = p := mem_singleton_iff.mp (he ▸ ht)
      have hs : D.selectedTarget hG.1 hf (z : Sphere) = p :=
        mem_singleton_iff.mp (he ▸ D.selectedTarget_mem hG.1 hf (z : Sphere))
      exact ht'.trans hs.symm

 theorem plane_center_interval_represents [Encodable D.IndexedMatchedPair]
    (E : D.MatchedRoundDisks) (hG : IsOpen G) (hf : IsConformalEquivalence f G (f '' G))
    (φ : Sphere → ℝ) (L : ℝ≥0) (n : ℕ) (t : ℝ)
    (ht : t ∈ E.traceInterval hG hf φ L n) :
    ∃ p : Sphere, D.planeRelation (E.traceCenter n) p ∧ |t-φ p| ≤ E.traceWidth L n :=
  E.traceInterval_represents hG hf φ L n t ht

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
