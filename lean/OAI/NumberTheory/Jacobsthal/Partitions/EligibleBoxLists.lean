import OAI.NumberTheory.Jacobsthal.Paths.RawBoxRationalWitness

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.EligibleBoxLists
open ActualBinOwners LogarithmicBinScale

attribute [local instance] Classical.propDecidable

noncomputable def eligibleLists {n : ℕ} (Y w Cs : ℝ) (M : Finset (Fin n → ℕ))
    (Q : (Fin n → ℕ) → Finset ℚ) (m : Fin n → ℕ) : Finset ℚ :=
  if m∈M then (Q m).filter (eligible Y w Cs) else ∅

theorem mem_eligibleLists {n : ℕ} (Y w Cs : ℝ) (M : Finset (Fin n → ℕ))
    (Q : (Fin n → ℕ) → Finset ℚ) (m : Fin n → ℕ) (q : ℚ) :
    q∈eligibleLists Y w Cs M Q m ↔ m∈M ∧ q∈Q m ∧ eligible Y w Cs q := by
  by_cases hm : m∈M <;> simp [eligibleLists,hm]

theorem eligibleLists_card {n : ℕ} (Y w Cs : ℝ) (M : Finset (Fin n → ℕ))
    (Q : (Fin n → ℕ) → Finset ℚ) (NQ : ℕ) (hQ : ∀ m∈M,(Q m).card ≤ NQ) :
    ∀ m,(eligibleLists Y w Cs M Q m).card ≤ NQ := by
  intro m
  by_cases hm : m∈M
  · simpa only [eligibleLists,ite_eq_left hm] using (Finset.card_filter_le (Q m) _).trans (hQ m hm)
  · simp [eligibleLists,hm]

theorem eligibleLists_eligible {n : ℕ} (Y w Cs : ℝ) (M : Finset (Fin n → ℕ))
    (Q : (Fin n → ℕ) → Finset ℚ) :
    ∀ m,∀ q∈eligibleLists Y w Cs M Q m,eligible Y w Cs q := by
  intro m q hq
  exact ((mem_eligibleLists Y w Cs M Q m q).mp hq).2.2

theorem soft_witness_in_eligibleLists {n : ℕ} (Y w Cs : ℝ) (M : Finset (Fin n → ℕ))
    (Q : (Fin n → ℕ) → Finset ℚ) (m : Fin n → ℕ) (hm : m∈M) (q : ℚ)
    (hq : q∈Q m) (helig : eligible Y w Cs q) : q∈eligibleLists Y w Cs M Q m :=
  (mem_eligibleLists Y w Cs M Q m q).mpr ⟨hm,hq,helig⟩
end NumberTheoryLean.EligibleBoxLists


end Erdos970

end OAI
