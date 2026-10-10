import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceCollisionBlocks
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceCollisionOrdered

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSourceCollision
open Construction Conclusion Filter

theorem selected_small_outside_pairwise_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ spectator : PrimeSource,
      (∀ p : spectator.Sample, Real.exp ((1/2000:ℝ)*L) ≤ Real.log (p:ℕ) ∧
        Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∀ l : ℕ,
      ∀ x y : SourceAssignment C.sources
        (Template.current (Template.initial (2*(bulkSize k L/2)) k) l),
      (assignmentPrior C.sources (Template.current
        (Template.initial (2*(bulkSize k L/2)) k) l)).mass x ≠ 0 →
      (∀ i : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length,
        (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)[i].role ≠ .bulk →
        (x i:ℕ) = (y i:ℕ)) →
      ∀ outside : List ℕ,
      (∀ q ∈ outside, ∃ p : spectator.Sample, p.val = q ∧ spectator.law.mass p ≠ 0) →
      ((assignedSlots C.sources (Template.current
        (Template.initial (2*(bulkSize k L/2)) k) l) y).map SmallSlot.value ++ outside).Pairwise Nat.Coprime →
      Function.Injective (fun u : Fin (2^l) × Fin (2*(bulkSize k L/2)) =>
        (x ((currentBulkPositionEquiv (2*(bulkSize k L/2)) k l).symm u).val).val) →
      ((assignedSlots C.sources (Template.current
        (Template.initial (2*(bulkSize k L/2)) k) l) x).map SmallSlot.value ++ outside).Pairwise Nat.Coprime := by
  filter_upwards [initial_source_cross_role_separation_eventually d Bs BD Bz hk] with L hsep
  intro E C hG hcl hcu hb hd spectator hs l x y hx hnonbulk outside hout href hinj
  exact assigned_small_outside_pairwise C spectator (hsep E C hG hcl hcu hb hd spectator hs)
    _ (fun _ hz => Template.mem_current_mem_seed hz) x y hx hnonbulk outside hout href
    (assigned_bulk_nodup_of_ordered_injective C.sources _ k l x hinj)

end Ostmann.Arithmetic.HistoryBulkSourceCollision

end

end OAI
