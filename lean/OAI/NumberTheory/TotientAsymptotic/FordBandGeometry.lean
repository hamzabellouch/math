import OAI.NumberTheory.TotientAsymptotic.NormalBandAllocation
import OAI.NumberTheory.TotientAsymptotic.BandStates
import OAI.NumberTheory.TotientAsymptotic.LargestPrimeCofactor

namespace OAI

/-! Actual cutoff geometry for the application of Ford's interval sieve. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_cutoff_antitone {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ}
    (h : FordComparisonParameters b y S D r Y U) {j l : ℕ} (hjl : j ≤ l) (hl : l ≤ b) :
    Y l ≤ Y j := by
  have hstep (a : ℕ) (ha : a < b) : Y (a+1) ≤ Y a :=
    ((h.2.2.2.2.1 a (Finset.mem_range.mpr ha)).1.trans (h.2.2.2.2.1 a (Finset.mem_range.mpr ha)).2).le
  induction l, hjl using Nat.le_induction with
  | base => rfl
  | succ l hjl ih => exact (hstep l (by omega)).trans (ih (by omega))

lemma ford_cutoff_ge_S {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ}
    (h : FordComparisonParameters b y S D r Y U) {j : ℕ} (hj : j ≤ b) : S ≤ Y j :=
  h.2.2.2.1.trans (ford_cutoff_antitone h hj le_rfl)

lemma ford_cutoff_le_y {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ}
    (h : FordComparisonParameters b y S D r Y U) {j : ℕ} (hj : j ≤ b) : Y j ≤ y := by
  simpa only [h.2.1] using ford_cutoff_antitone h (Nat.zero_le j) hj

lemma largestPrimeFactor_band {n : ℕ} (hn : 2 ≤ n) {U V : ℝ}
    (hU : U < largestPrimeFactor n) (hV : (largestPrimeFactor n:ℝ) ≤ V) :
    largestPrimeFactor (partBetween n U V)=largestPrimeFactor n := by
  have hmem := largestPrimeFactor_mem hn
  have hp : (largestPrimeFactor n).Prime := Nat.prime_of_mem_primeFactors hmem
  have hnl : n ≠ 0 := by omega
  apply Nat.le_antisymm
  · apply largestPrimeFactor_le_of_prime_divisors (le_max_left _ _)
    intro p hpp hpd _
    exact prime_dvd_le_largest hpp hnl (hpd.trans (partBetween_dvd hnl U V))
  · apply prime_dvd_le_largest hp (partBetween_pos n U V).ne'
    apply (Nat.mem_primeFactorsList_iff_dvd (partBetween_pos n U V).ne' hp).mp
    apply (partBetween_factors n U V).mem_iff.mp
    exact List.mem_filter.mpr ⟨List.mem_toFinset.mp hmem,by simp only [hU,hV,and_self,decide_true]⟩

lemma band_factor_ge_two {n : ℕ} (hn : 2 ≤ n) {U V : ℝ}
    (hU : U < largestPrimeFactor n) (hV : (largestPrimeFactor n:ℝ) ≤ V) :
    2 ≤ partBetween n U V := by
  have hp : (largestPrimeFactor n).Prime := Nat.prime_of_mem_primeFactors (largestPrimeFactor_mem hn)
  have he := largestPrimeFactor_band hn hU hV
  have hm : 2 ≤ partBetween n U V := by
    by_contra h
    have ho : partBetween n U V=1 := by have := partBetween_pos n U V; omega
    rw [ho] at he
    have hp1 : largestPrimeFactor (1:ℕ)=1 := by simp [largestPrimeFactor]
    rw [hp1] at he
    have := hp.two_le
    omega
  exact hm

def fordFactorState {b : ℕ} (t : ShiftedPair b) (V : ℝ) : ShiftedPair b where
  left j := partBelow (t.left j-1) V
  right j := partBelow (t.right j-1) V
  remainder := t.remainder

lemma lower_fordFactorState {b : ℕ} (t : ShiftedPair b) {U V : ℝ} (hUV : U ≤ V) :
    lowerState (fordFactorState t V) U=fordFactorState t U := by
  have hl : (fun j => partBelow (partBelow (t.left j-1) V) U)=
      (fun j => partBelow (t.left j-1) U) := funext (fun j => partBelow_nested _ hUV)
  have hr : (fun j => partBelow (partBelow (t.right j-1) V) U)=
      (fun j => partBelow (t.right j-1) U) := funext (fun j => partBelow_nested _ hUV)
  change ShiftedPair.mk _ _ t.remainder=ShiftedPair.mk _ _ t.remainder
  dsimp only [fordFactorState]
  rw [hl,hr]

lemma stateBand_fordFactorState {b k : ℕ} (hk : k ≤ b) (t : ShiftedPair b)
    {U V W : ℝ} (hVW : V ≤ W) :
    stateBand hk (fordFactorState t W) U V=
      (fun j => partBetween (t.left (Fin.castLE hk j)-1) U V,
       fun j => partBetween (t.right (Fin.castLE hk j)-1) U V) := by
  apply Prod.ext
  · exact funext (fun j => partBetween_below _ hVW)
  · exact funext (fun j => partBetween_below _ hVW)

end TotientAsymptotic

end

end OAI
