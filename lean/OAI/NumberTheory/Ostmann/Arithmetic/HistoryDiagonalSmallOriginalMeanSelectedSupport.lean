import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMeanDefs
import OAI.NumberTheory.Ostmann.Construction.SourceFrequencyBounds

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMean
open Construction Conclusion Filter HistoryGiantOriginalMeanFactorization

theorem restoringAssignment_mass_eq (sources : SourceFamily) (j : ℕ)
    (T : List SourceSlot) (x : SourceAssignment sources T) :
    (assignmentPrior sources T).mass x =
      (assignmentPrior sources (Template.extracted j T)).mass
        (restoringAssignmentEquiv sources j T x).1 *
      (assignmentPrior sources (Template.remainder j T)).mass
        (restoringAssignmentEquiv sources j T x).2 := by
  simpa only [assignmentWeight_eq_mass, restoringAssignmentEquiv] using
    (restoringSplit sources j T).val.mass x

theorem restoringAssignment_remainder_mass_ne_zero (sources : SourceFamily) (j : ℕ)
    (T : List SourceSlot) (x : SourceAssignment sources T)
    (hx : (assignmentPrior sources T).mass x ≠ 0) :
    (assignmentPrior sources (Template.remainder j T)).mass
      (restoringAssignmentEquiv sources j T x).2 ≠ 0 := by
  rw [restoringAssignment_mass_eq sources j T x] at hx
  exact (mul_ne_zero_iff.mp hx).2

theorem smallAssignment_mass_ne_zero
    {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E)
    (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (hx : (assignmentPrior C.sources _).mass x ≠ 0) :
    (assignmentPrior C.sources _).mass (smallAssignment C x) ≠ 0 :=
  restoringAssignment_remainder_mass_ne_zero C.sources (l+1) _ x hx

theorem selected_small_sources_above_frequencies_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase → C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ l ≤ k, ∀ i : Fin (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l))).length,
        (C.sources ((Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l))).get i).origin).AboveFrequency
          (frequencyBound Bs BD Bz k L l) := by
  filter_upwards [initial_sources_above_frequencies_eventually d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd l hl i
  exact (hL E C hG hcl hcu hb hd l hl).2 _

end Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMean

end

end OAI
