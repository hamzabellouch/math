import OAI.Combinatorics.Ryser.Construction.OrdinaryCover
import OAI.Combinatorics.Ryser.Geometry.Cardinality
import Lean.Elab.Tactic.Omega

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F G : Type*} [instFieldk : Field k] [Field F]
variable [DecidableEq k] [DecidableEq F] [DecidableEq G] [Fintype F]

theorem card_forcedPencilVertices_add_card_deletedPencil
    (data : ConfigurationData k F G) (B : Finset (AffineLine F))
    (p : ProjectivePoint F) :
    (forcedPencilVertices data B p).card + (B ∩ affinePencil p).card =
      (affinePencil p).card := by
  rw [card_forcedPencilVertices]
  simpa only [Finset.inter_comm] using
    Finset.card_sdiff_add_card_inter (affinePencil p) B

theorem card_forcedPencilVertices_finite (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : Point F) :
    (forcedPencilVertices data B (Sum.inl p)).card =
      Fintype.card F + 1 - (B ∩ affinePencil (Sum.inl p)).card := by
  rw [card_forcedPencilVertices, Finset.card_sdiff, card_affinePencil_finite]

theorem card_forcedPencilVertices_infinite (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (d : Direction F) :
    (forcedPencilVertices data B (Sum.inr d)).card =
      Fintype.card F - (B ∩ affinePencil (Sum.inr d)).card := by
  rw [card_forcedPencilVertices, Finset.card_sdiff, card_affinePencil_infinite]

theorem card_additionalPencilVertices_eq (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F)
    (C : Finset (Vertex (k := let _ := instFieldk; k) data.altered))
    (hforced : forcedPencilVertices data B p ⊆ C) :
    (C \ forcedPencilVertices data B p).card =
      C.card - (forcedPencilVertices data B p).card :=
  Finset.card_sdiff_of_subset hforced

theorem forced_additional_card_eq (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F)
    (C : Finset (Vertex (k := let _ := instFieldk; k) data.altered))
    (hforced : forcedPencilVertices data B p ⊆ C) :
    (forcedPencilVertices data B p).card +
      (C \ forcedPencilVertices data B p).card = C.card := by
  simpa only [Nat.add_comm] using Finset.card_sdiff_add_card_eq_card hforced

theorem forced_additional_card_le (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B p ⊆ C) (hC : C.card ≤ Fintype.card F) :
    (forcedPencilVertices data B p).card +
      (C \ forcedPencilVertices data B p).card ≤ Fintype.card F :=
  (forced_additional_card_eq data B p C hforced).trans_le hC

theorem pencil_additional_card_le (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : ProjectivePoint F)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B p ⊆ C) (hC : C.card ≤ Fintype.card F) :
    (affinePencil p).card + (C \ forcedPencilVertices data B p).card ≤
      Fintype.card F + (B ∩ affinePencil p).card := by
  have hsplit := card_forcedPencilVertices_add_card_deletedPencil data B p
  have hbudget := forced_additional_card_le data B p C hforced hC
  omega

theorem finite_deletedPencil_card_pos (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : Point F)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B (Sum.inl p) ⊆ C)
    (hC : C.card ≤ Fintype.card F) :
    0 < (B ∩ affinePencil (Sum.inl p)).card := by
  have hbudget := pencil_additional_card_le data B (Sum.inl p) C hforced hC
  rw [card_affinePencil_finite] at hbudget
  omega

theorem finite_additional_card_le (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (p : Point F)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B (Sum.inl p) ⊆ C)
    (hC : C.card ≤ Fintype.card F) :
    (C \ forcedPencilVertices data B (Sum.inl p)).card ≤
      (B ∩ affinePencil (Sum.inl p)).card - 1 := by
  have hbudget := pencil_additional_card_le data B (Sum.inl p) C hforced hC
  rw [card_affinePencil_finite] at hbudget
  omega

theorem infinite_additional_card_le (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (d : Direction F)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B (Sum.inr d) ⊆ C)
    (hC : C.card ≤ Fintype.card F) :
    (C \ forcedPencilVertices data B (Sum.inr d)).card ≤
      (B ∩ affinePencil (Sum.inr d)).card := by
  have hbudget := pencil_additional_card_le data B (Sum.inr d) C hforced hC
  rw [card_affinePencil_infinite] at hbudget
  omega

theorem infinite_additional_card_le_of_deleted_le (data : ConfigurationData k F G)
    (B : Finset (AffineLine F)) (d : Direction F)
    (C : Finset (Vertex (k := k) data.altered))
    (hforced : forcedPencilVertices data B (Sum.inr d) ⊆ C)
    (hC : C.card ≤ Fintype.card F) (N : ℕ)
    (hdeleted : (B ∩ affinePencil (Sum.inr d)).card ≤ N) :
    (C \ forcedPencilVertices data B (Sum.inr d)).card ≤ N :=
  (infinite_additional_card_le data B d C hforced hC).trans hdeleted

end RyserCoveringCounterexample.Construction

end OAI
