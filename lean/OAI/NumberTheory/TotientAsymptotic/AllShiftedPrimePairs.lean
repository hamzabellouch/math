import OAI.NumberTheory.TotientAsymptotic.ShiftedPrimePairBound

namespace OAI

/-! Restoring the small primes removed by the sieve cutoff. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def allShiftedPrimePairs (b X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun q => q.Prime ∧ (b*q+1).Prime)

lemma allShiftedPrimePairs_card_le (b X : ℕ) : (allShiftedPrimePairs b X).card ≤ X := by
  have h := Finset.card_le_card (Finset.filter_subset
    (fun q => q.Prime ∧ (b*q+1).Prime) (Finset.Icc 1 X))
  simpa [allShiftedPrimePairs] using h

lemma allShiftedPrimePairs_cutoff {b : ℕ} (hb : 0<b) (X z : ℕ) :
    (allShiftedPrimePairs b X).card ≤ (shiftedPrimePairs b X z).card+z := by
  classical
  have hsub : allShiftedPrimePairs b X ⊆ shiftedPrimePairs b X z ∪ Finset.Icc 1 z := by
    intro q hq
    obtain ⟨hqX,hqp,hbq⟩ := Finset.mem_filter.mp hq
    by_cases hqz : q≤z
    · exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hqX).1,hqz⟩)
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨hqX,hqp,hbq,by omega,?_⟩
      have hq : q≤b*q := by simpa using Nat.mul_le_mul_right q hb
      omega
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simpa using h

lemma totient_ratio_one_le {b : ℕ} (hb : 0<b) : (1:ℝ)≤(b:ℝ)/b.totient := by
  have hφ : (0:ℝ)<b.totient := by exact_mod_cast Nat.totient_pos.mpr hb
  apply (le_div_iff₀ hφ).mpr
  simpa using (show (b.totient:ℝ)≤b by exact_mod_cast Nat.totient_le b)

end TotientAsymptotic

end

end OAI
