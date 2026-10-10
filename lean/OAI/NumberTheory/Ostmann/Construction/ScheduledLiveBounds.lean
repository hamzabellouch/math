import OAI.NumberTheory.Ostmann.Construction.ScheduledPrimeRanges
import OAI.NumberTheory.Ostmann.Arithmetic.MovingLivePrimeDivisors

namespace OAI

/-! # Frequency separation of the actual scheduled harmonic laws -/
namespace Ostmann
open scoped Classical BigOperators

theorem scheduledRegularPrior_support (A B : Set ℕ) (N hi : ℕ) (X : ℝ)
    (D P Qb : Finset ℕ) (top : ℕ) (cs : List ℕ) (n m : ℕ)
    (i : MovingRegularSlot n (scheduledSmallLength cs) m) (p : P)
    (hp : scheduledRegularPrior
      (fun c => primeSubsetPrior P (selectedTailCellPrimes A B N X hi D c))
      (primeSubsetPrior P Qb) top cs n m i p ≠ 0) :
    (p : ℕ) ∈ scheduledRegularPrimeSets (selectedTailCellPrimes A B N X hi D)
      Qb top cs n m i := by
  rw [scheduledRegularPrior_prime] at hp
  exact primeSubsetPrior_support P _ p hp

theorem selected_scheduled_regular_large
    {A B : Set ℕ} {N hi top : ℕ} {a C L X target : ℝ} {D P Qb : Finset ℕ}
    {cs : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L X hi D target top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) cs targets)
    (hL : 0 ≤ L)
    (hlower : ∀ j ∈ initialSmallCellList top cs, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ))
    (hbulk : Qb ⊆ initialRegularPrimeRange L)
    (hbulklower : ∀ p ∈ Qb, Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (p : ℝ))
    (n m j V : ℕ) (hV : (V : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)))
    (i : MovingRegularSlot n (scheduledSmallLength (cs.drop j)) m) (p : P)
    (hp : scheduledRegularPrior
      (fun c => primeSubsetPrior P (selectedTailCellPrimes A B N X hi D c))
      (primeSubsetPrior P Qb) top (cs.drop j) n m i p ≠ 0) : V < (p : ℕ) := by
  have hm := scheduledRegularPrior_support A B N hi X D P Qb top (cs.drop j) n m i p hp
  have hr := scheduledRegularPrimeSets_range htop hcs hL hlower hbulk hbulklower n m j i p hm
  exact_mod_cast hV.trans_le hr.2

theorem selected_scheduled_compensation_large
    {A B : Set ℕ} {N hi top : ℕ} {a C L X target : ℝ} {D P : Finset ℕ}
    {cs : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L X hi D target top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) cs targets)
    (hL : 0 ≤ L)
    (hlower : ∀ j ∈ initialSmallCellList top cs, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ))
    (n V : ℕ) (hV : (V : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)))
    (p : P) (hp : completedCompensationPrior A B N X hi D P top cs n p ≠ 0) : V < (p : ℕ) := by
  have hm := primeSubsetPrior_support P _ p hp
  have hr := (completedCompensationSets_range htop hcs hlower n p hm).2
  have hb : Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤
      Real.exp (Real.exp ((1 / 100 : ℝ) * L)) := by
    apply Real.exp_le_exp.mpr
    apply Real.exp_le_exp.mpr
    nlinarith only [hL]
  exact_mod_cast (hV.trans_le hb).trans_le hr

end Ostmann

end OAI
