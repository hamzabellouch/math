import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeWindow

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryNarrowGrid
open Finset
noncomputable section

def assignedLength (q r R X p : ℕ) : ℕ :=
  ∑i∈grid q r R,if p∈primeBin i then evenBinLength X i else 0

lemma assigned_length_eq (q r R X : ℕ) (hq : 0<q) {i : ℕ×ℕ}
    (hi : i∈grid q r R) {p : ℕ} (hp : p∈primeBin i) :
    assignedLength q r R X p=evenBinLength X i := by
  unfold assignedLength
  rw [sum_eq_single i]
  · simp only [ite_eq_left hp]
  · intro j hj hji
    have he : p∉primeBin j := fun hjp =>
      Finset.disjoint_left.mp (prime_bins_disjoint q r R hq hi hj hji.symm) hp hjp
    simp only [ite_eq_right he]
  · exact fun hnot => (hnot hi).elim

lemma assigned_length_cutoff (q r R X : ℕ) (hq : 0<q) {p : ℕ}
    (hp : p∈primeWindow q r R) :
    X-(X/q+2*(q*2^(r+R)))≤p*assignedLength q r R X p ∧ p*assignedLength q r R X p≤X := by
  rw [prime_window_bins] at hp
  obtain ⟨i,hi,hp⟩ := mem_biUnion.mp hp
  rw [assigned_length_eq q r R X hq hi hp]
  exact even_bin_cutoff q r R X hq hi hp

lemma prime_window_subset (q r R : ℕ) : primeWindow q r R⊆(q*2^(r+R)).primesLE := by
  intro p hp
  rcases mem_filter.mp hp with ⟨hp,hprime⟩
  exact Nat.mem_primesLE.mpr ⟨(mem_Ioc.mp hp).2,hprime⟩

end
end OrdinaryNarrowGrid

end

end OAI
