import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalRepresentatives
import OAI.Combinatorics.Ramsey.CycleClique.Construction.OptimalRepresentatives

namespace OAI

/-! Separate the original representatives from the singleton representatives
of missing clique vertices. -/

namespace CycleClique.Construction.ExpandedPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

noncomputable def incidentRepresentatives (S : ExpandedPathSystem G Q) : Finset V :=
  S.toRaw.representatives.toFinset

theorem incidentRepresentatives_card (S : ExpandedPathSystem G Q) :
    S.incidentRepresentatives.card = S.incident := by
  rw [incidentRepresentatives, List.toFinset_card_of_nodup S.toRaw.representatives_nodup,
    RawPathSystem.representatives_length, S.incident_eq_chainCliqueCount]
  rfl

theorem incidentRepresentatives_subset_vertices (S : ExpandedPathSystem G Q) :
    S.incidentRepresentatives ⊆ S.vertices := by
  intro x hx
  exact List.mem_toFinset.mpr (S.toRaw.representatives_sublist.subset (List.mem_toFinset.mp hx))

theorem complete_representatives_eq (S : ExpandedPathSystem G Q) :
    S.toRaw.completeClique.representatives = S.toRaw.representatives ++ (Q \ S.vertices).toList := by
  simp [RawPathSystem.representatives, RawPathSystem.completeClique, chainRepresentatives,
    representativesFrom, List.map_append, List.flatten_append, List.map_map, Function.comp_def]
  change ((Q \ S.vertices).toList.map (fun v => [v])).flatten = _
  generalize (Q \ S.vertices).toList = L
  induction L with
  | nil => rfl
  | cons x L ih => simpa using congrArg (List.cons x) ih

theorem representativeFinset_eq_union (S : ExpandedPathSystem G Q) :
    S.representativeFinset = S.incidentRepresentatives ∪ (Q \ S.vertices) := by
  rw [representativeFinset, S.complete_representatives_eq, List.toFinset_append]
  simp only [Finset.toList_toFinset, incidentRepresentatives]

theorem incidentRepresentatives_subset_representatives (S : ExpandedPathSystem G Q) :
    S.incidentRepresentatives ⊆ S.representativeFinset := by
  rw [S.representativeFinset_eq_union]
  exact Finset.subset_union_left

theorem missing_subset_representatives (S : ExpandedPathSystem G Q) :
    Q \ S.vertices ⊆ S.representativeFinset := by
  rw [S.representativeFinset_eq_union]
  exact Finset.subset_union_right

theorem missing_card_add_incident (S : ExpandedPathSystem G Q) :
    (Q \ S.vertices).card + S.incident = Q.card := by
  have hh := Finset.card_sdiff_add_card_inter Q S.vertices
  simpa only [incident, Finset.inter_comm] using hh

theorem IsOptimal.terminal_finset_classification {S : ExpandedPathSystem G Q} {k d : ℕ}
    (hopt : S.IsOptimal k) (ht : 9 ≤ Q.card) (hQk : Q.card ≤ k)
    (hkQ : k ≤ 2 * Q.card + 1) (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G (k + 1)) (hd : 1 ≤ d) (hd' : d ≤ 6)
    {x y : V} (hx : x ∈ S.representativeFinset) (hy : y ∈ S.representativeFinset)
    (hne : x ≠ y) (hout : OutsidePath G (S.ground : Set V) x y d) :
    x ∈ Q ∧ y ∈ Q ∧ S.amount = k - Q.card ∧ d * S.assignedCount ≤ S.amount ∧
      TerminalAlternative S k d x y := by
  apply hopt.terminal_completed_classification ht hQk hkQ hQ hcycle hd hd' (fun _ => false)
    (x := x) (y := y)
  · simpa [RawPathSystem.representatives, RawPathSystem.orientChains,
      RawPathSystem.orientedChain] using List.mem_toFinset.mp hx
  · simpa [RawPathSystem.representatives, RawPathSystem.orientChains,
      RawPathSystem.orientedChain] using List.mem_toFinset.mp hy
  · exact hne
  · simpa only [ground, Finset.coe_union] using hout

end CycleClique.Construction.ExpandedPathSystem

end OAI
