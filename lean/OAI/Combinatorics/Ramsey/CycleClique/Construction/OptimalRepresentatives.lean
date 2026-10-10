import OAI.Combinatorics.Ramsey.CycleClique.Construction.RepresentativeBallGrowth
import OAI.Combinatorics.Ramsey.CycleClique.Construction.OptimalPathSystem

namespace OAI

/-! The complete ground set and representative finset of an optimal system. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

noncomputable def ground (S : ExpandedPathSystem G Q) : Finset V := Q ∪ S.vertices

noncomputable def representativeFinset (S : ExpandedPathSystem G Q) : Finset V :=
  S.toRaw.completeClique.representatives.toFinset

theorem ground_card (S : ExpandedPathSystem G Q) : S.ground.card = Q.card + S.amount := by
  have hc := Finset.card_union_add_card_inter Q S.vertices
  have hpart := Finset.card_sdiff_add_card_inter S.vertices Q
  have hi : (Q ∩ S.vertices).card = (S.vertices ∩ Q).card := by rw [Finset.inter_comm]
  unfold ground amount
  omega

theorem representativeFinset_card (S : ExpandedPathSystem G Q) :
    S.representativeFinset.card = Q.card := by
  rw [representativeFinset, List.toFinset_card_of_nodup S.toRaw.completeClique.representatives_nodup,
    RawPathSystem.completeClique_representatives_length]

theorem representativeFinset_subset_ground (S : ExpandedPathSystem G Q) :
    S.representativeFinset ⊆ S.ground := by
  intro v hv
  have hv' := S.toRaw.completeClique.representatives_sublist.subset (List.mem_toFinset.mp hv)
  have hvU : v ∈ S.toRaw.completeClique.vertices := List.mem_toFinset.mpr hv'
  rw [RawPathSystem.completeClique_vertices] at hvU
  exact Finset.mem_union.mpr (Finset.mem_union.mp hvU).symm

theorem IsOptimal.ground_card_le {S : ExpandedPathSystem G Q} {k : ℕ}
    (hopt : S.IsOptimal k) (hQk : Q.card ≤ k) : S.ground.card ≤ k := by
  rw [ground_card]
  have h := hopt.budget
  omega

theorem IsOptimal.representativeFinset_one_exclusion {S : ExpandedPathSystem G Q} {k : ℕ}
    (hopt : S.IsOptimal k) (hk : 3 ≤ k) (hQk : Q.card ≤ k)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    {x y : V} (hx : x ∈ S.representativeFinset) (hy : y ∈ S.representativeFinset) (hne : x ≠ y) :
    ¬ OutsidePath G (S.ground : Set V) x y 1 := by
  simpa only [ground, Finset.coe_union] using
    hopt.completed_representatives_one_exclusion hk hQk hQ hcycle
      (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy) hne

end CycleClique.Construction.ExpandedPathSystem

end OAI
