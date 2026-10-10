import OAI.Computability.UniqueGames.Reduction.ActualGame
import OAI.Computability.UniqueGames.Reduction.GapSemanticsLemmas
import OAI.Computability.UniqueGames.Reduction.NoiseEnumerationLemmas

namespace OAI

namespace UniqueGamesTheorem.Integration.TableReduction

open BinaryLinear NoiseTables UniqueGamesTheorem.Reduction.ActualSource
open UniqueGamesTheorem.Reduction.ActualGame UniqueGamesTheorem.Foundations.Target

variable {s d : Nat}

def tableEnumeration (T : Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) : NoiseEnumeration (T.gadget f hf) where
  indices := List.finRange T.vectors.length
  nodup := List.nodup_finRange _
  complete i := List.mem_finRange i

/-- The projection is used only to fill an erased witness field. It is never
used when generating constraints or evaluating their permutation tables. -/
def tableSkeleton (T : Table s d) : SplitGadget s d :=
  T.gadget Prod.fst (fun _ _ => rfl)

/-- A total executable map with finite vector data and no nonlinear-map input. -/
def output (S : Source) (k : Nat) (T : Table s d) : Instance (2 ^ s) :=
  outputInstanceWithEnumeration S k (tableSkeleton T)
    (tableEnumeration T Prod.fst (fun _ _ => rfl))

/-- Every correcting-map witness generates exactly the same numbered instance,
including the ordered constraint list and all permutation entries. -/
theorem output_eq_with_witness (S : Source) (k : Nat) (T : Table s d)
    (f : Ambient s d → Alphabet s) (hf : ∀ x c, f (x + (c, 0)) = f x + c) :
    output S k T =
      outputInstanceWithEnumeration S k (T.gadget f hf) (tableEnumeration T f hf) := by
  rfl

theorem completeAt_output_iff (error : RationalError) (S : Source) (k : Nat)
    (T : Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) :
    CompleteAt error (output S k T) ↔
      CompleteAt error (outputInstance S k (T.gadget f hf)) := by
  rw [output_eq_with_witness S k T f hf]
  exact completeAt_outputInstanceWithEnumeration_iff _ _ _ _ _

theorem soundAt_output_iff (error : RationalError) (S : Source) (k : Nat)
    (T : Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) :
    SoundAt error (output S k T) ↔
      SoundAt error (outputInstance S k (T.gadget f hf)) := by
  rw [output_eq_with_witness S k T f hf]
  exact soundAt_outputInstanceWithEnumeration_iff _ _ _ _ _

theorem edge_ofEnumeration (S : Source) (k : Nat) (g : SplitGadget s d)
    (en : NoiseEnumeration g)
    (ω : Outcome S k ((Table.ofEnumeration g en).gadget g.f g.equivariant)) :
    edge S k ((Table.ofEnumeration g en).gadget g.f g.equivariant) ω =
      edge S k g (ω.1, Table.positionEquiv g en ω.2.1, ω.2.2) := by
  simp only [edge, leftQuery, rightQuery]
  erw [Table.noise_positionEquiv g en ω.2.1]

theorem acceptance_ofEnumeration (S : Source) (k : Nat) (g : SplitGadget s d)
    (en : NoiseEnumeration g) (label : Fin (vertexCount S k s d) → Fin (2 ^ s)) :
    acceptanceProbability S k ((Table.ofEnumeration g en).gadget g.f g.equivariant) label =
      acceptanceProbability S k g label := by
  apply Fintype.expect_equiv ((Equiv.refl (Query S k s d)).prodCongr
    ((Table.positionEquiv g en).prodCongr (Equiv.refl (Dual k))))
  intro ω
  exact congrArg
    (fun c : Constraint (vertexCount S k s d) (2 ^ s) =>
      if c.satisfied label then (1 : ℚ) else 0)
    (edge_ofEnumeration S k g en ω)

theorem rate_ofEnumeration (S : Source) (k : Nat) (g : SplitGadget s d)
    (en : NoiseEnumeration g) (label : Fin (vertexCount S k s d) → Fin (2 ^ s)) :
    GapSemantics.satisfactionRate
      (outputInstance S k ((Table.ofEnumeration g en).gadget g.f g.equivariant)) label =
      GapSemantics.satisfactionRate (outputInstance S k g) label := by
  exact (acceptanceProbability_eq_count S k _ label).symm.trans
    ((acceptance_ofEnumeration S k g en label).trans
      (acceptanceProbability_eq_count S k g label))

/-- Normalization to a concrete table preserves the original completeness
threshold exactly; there is no additional approximation loss. -/
theorem completeAt_ofEnumeration_iff (error : RationalError)
    (S : Source) (k : Nat) (g : SplitGadget s d) (en : NoiseEnumeration g) :
    CompleteAt error (output S k (Table.ofEnumeration g en)) ↔
      CompleteAt error (outputInstance S k g) := by
  rw [completeAt_output_iff error S k _ g.f g.equivariant]
  rw [GapSemantics.completeAt_iff, GapSemantics.completeAt_iff]
  constructor
  · rintro ⟨label, h⟩
    exact ⟨label, h.trans_eq (rate_ofEnumeration S k g en label)⟩
  · rintro ⟨label, h⟩
    exact ⟨label, h.trans_eq (rate_ofEnumeration S k g en label).symm⟩

theorem soundAt_ofEnumeration_iff (error : RationalError)
    (S : Source) (k : Nat) (g : SplitGadget s d) (en : NoiseEnumeration g) :
    SoundAt error (output S k (Table.ofEnumeration g en)) ↔
      SoundAt error (outputInstance S k g) := by
  rw [soundAt_output_iff error S k _ g.f g.equivariant]
  rw [GapSemantics.soundAt_iff, GapSemantics.soundAt_iff]
  constructor
  · intro h label
    exact (rate_ofEnumeration S k g en label).symm.trans_le (h label)
  · intro h label
    exact (rate_ofEnumeration S k g en label).trans_le (h label)

end UniqueGamesTheorem.Integration.TableReduction

end OAI
