import OAI.Combinatorics.Ryser.Construction.ExceptionalCover
import OAI.Combinatorics.Ryser.Construction.ExceptionalBudget
import OAI.Combinatorics.Ryser.Construction.CoverBudget
import OAI.Combinatorics.Ryser.Construction.GadgetConsequences

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G]
variable [Fintype k] [Fintype F]
variable (σ : k →+* F) (M : G → PlaneLinearMap F) (b : G → Point F)
variable (Y : Finset (Point k)) (X : Finset (Point F))

local notation "cfg" => placedConfiguration σ M b Y X
local notation "axes" => (fun i => axisDirections σ (M i))

theorem exceptional_cover_card_lower_bound
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hY : GadgetCoverProperty (Y.image cubeMap)) (i : G)
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hcover : ∀ w ∈ Y, ∃ v ∈ C, v ∈ exceptionalEdge cfg i w) :
    Fintype.card k ≤ C.card := by
  obtain ⟨L, hLC, hLcover⟩ :=
    exists_line_cover_of_exceptional_cover σ M b Y X hcop i C hcover
  have hweight := hY.weighted_card_lower_bound ∅ L (by
    intro y hy
    exact Or.inr (hLcover y hy))
  simp only [Finset.card_empty, Nat.add_zero] at hweight
  omega

theorem exceptional_resource_weight_lower_bound
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hY : GadgetCoverProperty (Y.image cubeMap)) (i : G)
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hcover : ∀ w ∈ Y, ∃ v ∈ C, v ∈ exceptionalEdge cfg i w) :
    2 * Fintype.card k ≤
      2 * (lineResources cfg axes C i).card + (pointResources cfg axes C i).card := by
  obtain ⟨L, B, hL, hB, hcover'⟩ :=
    exists_mixed_cover_of_exceptional_cover σ M b Y X hcop i C hcover
  have hweight := hY.weighted_card_lower_bound B L hcover'
  omega

variable [Fintype G]

theorem single_infinite_center_impossible
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hY : GadgetCoverProperty (Y.image cubeMap))
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hC : IsCover (hypergraph cfg) C) (hCcard : C.card ≤ Fintype.card F)
    (B : Finset (AffineLine F)) (d : Direction F) (i : G)
    (hd : d ∈ alteredDirections σ (M i))
    (hforced : forcedPencilVertices cfg B (Sum.inr d) ⊆ C)
    (hdeleted : (B ∩ affinePencil (Sum.inr d)).card ≤ Fintype.card k - 1) :
    False := by
  have hcover := exceptional_cover_additional_of_altered cfg C hC B d i hd
  have hlower := exceptional_cover_card_lower_bound σ M b Y X hcop hY i
    (C \ forcedPencilVertices cfg B (Sum.inr d)) hcover
  have hupper := infinite_additional_card_le_of_deleted_le cfg B d C hforced hCcard
    (Fintype.card k - 1) hdeleted
  have hs : 0 < Fintype.card k := Fintype.card_pos
  omega

theorem double_infinite_center_impossible
    (hcop : Nat.Coprime 3 (Fintype.card k - 1))
    (hY : GadgetCoverProperty (Y.image cubeMap))
    (C : Finset (Vertex (k := k) (cfg).altered))
    (hC : IsCover (hypergraph cfg) C) (hCcard : C.card ≤ Fintype.card F)
    (B : Finset (AffineLine F)) (d : Direction F) (i j : G) (hij : i ≠ j)
    (hdi : d ∈ alteredDirections σ (M i))
    (hdj : d ∈ alteredDirections σ (M j))
    (haxesij : axisDirections σ (M i) ⊆ alteredDirections σ (M j))
    (haxesji : axisDirections σ (M j) ⊆ alteredDirections σ (M i))
    (hforced : forcedPencilVertices cfg B (Sum.inr d) ⊆ C)
    (hdeleted : (B ∩ affinePencil (Sum.inr d)).card ≤ 2 * (Fintype.card k - 1)) :
    False := by
  let A := C \ forcedPencilVertices cfg B (Sum.inr d)
  have hcoveri : ∀ w ∈ Y, ∃ v ∈ A, v ∈ exceptionalEdge cfg i w :=
    exceptional_cover_additional_of_altered cfg C hC B d i hdi
  have hcoverj : ∀ w ∈ Y, ∃ v ∈ A, v ∈ exceptionalEdge cfg j w :=
    exceptional_cover_additional_of_altered cfg C hC B d j hdj
  have hi := exceptional_resource_weight_lower_bound σ M b Y X hcop hY i A hcoveri
  have hj := exceptional_resource_weight_lower_bound σ M b Y X hcop hY j A hcoverj
  have hbudget : A.card ≤ 2 * (Fintype.card k - 1) :=
    infinite_additional_card_le_of_deleted_le cfg B d C hforced hCcard
      (2 * (Fintype.card k - 1)) hdeleted
  exact two_group_resource_budget_impossible A
    (lineResources cfg axes A i) (pointResources cfg axes A i)
    (lineResources cfg axes A j) (pointResources cfg axes A j)
    (Fintype.card k) Fintype.card_pos
    (lineResources_subset cfg axes A i) (pointResources_subset cfg axes A i)
    (lineResources_subset cfg axes A j) (pointResources_subset cfg axes A j)
    (lineResources_disjoint_pointResources cfg axes A i)
    (lineResources_disjoint_pointResources cfg axes A j)
    (lineResources_disjoint_other_of_axis_subset cfg axes A i j hij haxesij)
    (lineResources_disjoint_other_of_axis_subset cfg axes A j i hij.symm haxesji)
    hi hj hbudget

end RyserCoveringCounterexample.Construction

end OAI
