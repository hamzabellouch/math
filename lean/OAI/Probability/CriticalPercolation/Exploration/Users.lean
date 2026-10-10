import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.LocalNode
import OAI.Probability.CriticalPercolation.Modular.OrderMass

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.OrderedQuery
open QueryTree MarkedTree Priority FiniteEntropy

variable {E I : Type*} [Fintype I]

noncomputable instance (priority := 2000) localNodeDecidable (t : I → QueryTree E) :
    DecidableEq (LocalNode t) := Classical.decEq _

noncomputable def users (t : I → QueryTree E) (ω : E → Bool) (e : E) : Finset I :=
  Finset.univ.filter (fun i => e ∈ (t i).reads ω)

noncomputable def otherUsers (t : I → QueryTree E) (i : I) (ω : E → Bool) (e : E) :
    Finset {j : I // j ≠ i} := (users t ω e).subtype (fun j => j ≠ i)

lemma mem_users (t : I → QueryTree E) (ω : E → Bool) (e : E) (i : I) :
    i ∈ users t ω e ↔ e ∈ (t i).reads ω := by simp [users]

lemma mem_otherUsers (t : I → QueryTree E) (i : I) (ω : E → Bool) (e : E)
    (j : {j : I // j ≠ i}) : j ∈ otherUsers t i ω e ↔ e ∈ (t j.val).reads ω := by
  simp [otherUsers, mem_users]

lemma otherUsers_card (t : I → QueryTree E) (i : I) (ω : E → Bool) (e : E)
    (hi : e ∈ (t i).reads ω) : (otherUsers t i ω e).card = (users t ω e).card - 1 := by
  rw [otherUsers, Finset.card_subtype]
  have he : (users t ω e).filter (fun j => j ≠ i) = (users t ω e).erase i := by
    ext j
    simp [and_comm]
  rw [he, Finset.card_erase_of_mem ((mem_users t ω e i).mpr hi)]

lemma visits_bit_mem (t : QueryTree E) (ω : E → Bool) (n : t.Node)
    (hn : t.visits n ω) : t.bit n ∈ t.reads ω := by
  rw [← map_bit_pathNodes]
  exact List.mem_map.mpr ⟨n, (mem_pathNodes t ω n).mpr hn, rfl⟩

lemma otherUsers_card_le_three (t : I → QueryTree E) (i : I) (ω : E → Bool)
    (n : (t i).Node) (hn : (t i).visits n ω) (h : (users t ω ((t i).bit n)).card ≤ 4) :
    (otherUsers t i ω ((t i).bit n)).card ≤ 3 := by
  rw [otherUsers_card t i ω _ (visits_bit_mem _ _ _ hn)]
  omega

lemma first_iff_no_prior (t : I → QueryTree E) (o : Order I) (i : I)
    (ω : E → Bool) (e : E) :
    First o i (otherUsers t i ω e) ↔ ∀ j ∈ priorList o i, e ∉ (t j).reads ω := by
  constructor
  · intro h j hj hr
    have hji : j ≠ i := fun he => (priorList_suffix o i).2.1 (he ▸ hj)
    exact h ⟨j,hji⟩ ((mem_otherUsers t i ω e ⟨j,hji⟩).mpr hr) hj
  · intro h j hj hjp
    exact h j.val hjp ((mem_otherUsers t i ω e j).mp hj)

variable [Fintype E]

lemma fresh_order_node (t : I → QueryTree E) (o : Order I) (i : I) (n : (t i).Node)
    (ht : (t i).Valid ∅) (ω : E → Bool) :
    (coord t ⟨i,n⟩, ⟨i,n⟩) ∈ (combined t o.val).trace ω ↔
      (t i).visits n ω ∧ First o i (otherUsers t i ω ((t i).bit n)) := by
  change ((t i).bit n, ⟨i,n⟩) ∈ (combined t o.val).trace ω ↔ _
  rw [(priorList_suffix o i).1]
  rw [fresh_local_node t _ _ _ _ _ (priorList_suffix o i).2.1 (priorList_suffix o i).2.2 ht]
  rw [first_iff_no_prior]

end CriticalPercolation.OrderedQuery

end
end

end OAI
