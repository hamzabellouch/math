import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreSourceMeanValues
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceCollisionSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPrincipalCollisionError
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryBulkFibreOriginalReference HistoryBulkFibreSourceMean HistoryBulkSourceCollision
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

def fibreSmallOutsideGuard (C : InitialSourceChoice d Bs BD Bz k L E)
    (outside : List ℕ) (a : SelectedNonbulkSample C l) (u : SelectedBulkSample C l) : Prop :=
  ((assignedSlots C.sources (SelectedTemplate k L l) (fibreAssignment C a u)).map
    SmallSlot.value ++ outside).Pairwise Nat.Coprime

theorem selected_fibreSmallOutsideGuard_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20 : ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter : ℝ) →
      (C.giantCenter : ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin : ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin : ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ spectator : PrimeSource,
      (∀ p : spectator.Sample, Real.exp ((1/2000 : ℝ)*L) ≤ Real.log (p : ℕ) ∧
        Real.log (p : ℕ) ≤ Real.exp ((1/1000 : ℝ)*L)) →
      ∀ (l : ℕ) (a : SelectedNonbulkSample C l) (u y : SelectedBulkSample C l),
      (selectedNonbulkPrior C l).mass a ≠ 0 →
      (selectedBulkPrior C l).mass u ≠ 0 →
      ∀ outside : List ℕ,
      (∀ q ∈ outside, ∃ p : spectator.Sample, p.val = q ∧ spectator.law.mass p ≠ 0) →
      fibreSmallOutsideGuard C outside a y →
      Function.Injective (fun j => (u j).val) →
      fibreSmallOutsideGuard C outside a u := by
  filter_upwards [selected_small_outside_pairwise_eventually d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd spectator hs l a u y ha hu outside hout href hinj
  have hx : (assignmentPrior C.sources (SelectedTemplate k L l)).mass
      (fibreAssignment C a u) ≠ 0 := by
    rw [fibreAssignment_mass]
    exact mul_ne_zero ha hu
  apply hL E C hG hcl hcu hb hd spectator hs l
    (fibreAssignment C a u) (fibreAssignment C a y) hx
  · intro i hi
    exact fibreAssignment_nonbulk_fixed C a u y i hi
  · exact hout
  · exact href
  · intro i j hij
    apply hinj
    exact (bulkSamples_fibreAssignment C a u i.1 i.2).symm.trans
      (hij.trans (bulkSamples_fibreAssignment C a u j.1 j.2))

end Ostmann.Arithmetic.HistoryBulkPrincipalCollisionError

end

end OAI
