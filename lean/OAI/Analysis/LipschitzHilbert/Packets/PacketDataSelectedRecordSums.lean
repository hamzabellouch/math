import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedPackets
import Mathlib.Data.List.Pairwise

namespace OAI

/-! Disjoint selected records give exact sums over the selected union. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem sizeSelectionRecords_disjoint (negative : Bool) (w cb A : ℝ) (hA : 1/2≤A)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (R : Finset P.PacketIndex) (tops : List SlopeBox) :
    (P.sizeSelectionRecords negative w cb A cell grid R tops).Pairwise
      (fun p q => Disjoint p.2 q.2) := by
  induction tops generalizing R with
  | nil => exact List.Pairwise.nil
  | cons T tops ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih _⟩
    intro p hp
    have hsub := P.sizeSelectionRecords_subset negative w cb A cell grid
      (R\P.sizeDeletePackets w A cell grid R T) tops p hp
    apply Finset.disjoint_left.mpr
    intro q hq hqp
    exact (Finset.mem_sdiff.mp (hsub hqp)).2
      (P.sizeTestPackets_subset_delete negative w cb A hA cell grid R T hq)

theorem selectedPackets_sum {E : Type*} [AddCommMonoid E]
    (negative : Bool) (w cb A : ℝ) (hA : 1/2≤A)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (R : Finset P.PacketIndex) (tops : List SlopeBox) (f : P.PacketIndex → E) :
    (∑ q∈P.selectedPackets negative w cb A cell grid R tops, f q)=
      ∑ p∈(P.sizeSelectionRecords negative w cb A cell grid R tops).toFinset, ∑ q∈p.2, f q := by
  let : Std.Symm (fun p q : SlopeBox × Finset P.PacketIndex => Disjoint p.2 q.2) :=
    ⟨fun _ _ h => h.symm⟩
  apply Finset.sum_biUnion
  intro p hp q hq hpq
  exact (P.sizeSelectionRecords_disjoint negative w cb A hA cell grid R tops).forall
    (List.mem_toFinset.mp hp) (List.mem_toFinset.mp hq) hpq

end LipschitzHilbert.PacketLatticeData

end

end OAI
