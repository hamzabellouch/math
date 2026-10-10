import OAI.NumberTheory.TotientAsymptotic.TriplePrimeBound

namespace OAI

/-! Restoring small q in the three-form sieve. -/
noncomputable section
namespace TotientAsymptotic

def allPrimeTriples (a b X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun q => q.Prime ∧ (a*q+1).Prime ∧ (b*q+1).Prime)

lemma allPrimeTriples_card_le (a b X : ℕ) : (allPrimeTriples a b X).card ≤ X := by
  have hh := Finset.card_le_card (Finset.filter_subset
    (fun q => q.Prime ∧ (a*q+1).Prime ∧ (b*q+1).Prime) (Finset.Icc 1 X))
  simpa [allPrimeTriples] using hh

lemma allPrimeTriples_cutoff {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (X z : ℕ) :
    (allPrimeTriples a b X).card ≤ (triplePrimeTuples a b X z).card+z := by
  classical
  have hsub : allPrimeTriples a b X ⊆ triplePrimeTuples a b X z ∪ Finset.Icc 1 z := by
    intro q hq
    obtain ⟨hqX,hqp,haq,hbq⟩ := Finset.mem_filter.mp hq
    by_cases hqz : q ≤ z
    · exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hqX).1,hqz⟩)
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      have hqa : q ≤ a*q := by simpa using Nat.mul_le_mul_right q ha
      have hqb : q ≤ b*q := by simpa using Nat.mul_le_mul_right q hb
      exact ⟨hqX,hqp,haq,hbq,by omega,by omega,by omega⟩
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simpa using hh

end TotientAsymptotic

end

end OAI
