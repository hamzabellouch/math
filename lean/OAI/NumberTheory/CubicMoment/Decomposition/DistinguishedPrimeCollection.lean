import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedPrimeGeometry

namespace OAI

/-! Exact finite collection of the distinguished-coordinate conditions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedDistinguishedPrimeSet_subset (B ρ a b : ℝ) (j j₀ k h : ℕ)
    (Z Q : ℝ) (early : Bool) (c d e : Eisenstein) :
    stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e ⊆ primeCutoff B := by
  intro p hp
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1

theorem distinguished_prime_collection (B ρ a b : ℝ) (j j₀ k h : ℕ)
    (Z Q : ℝ) (early : Bool) (c d e : Eisenstein)
    (hc : primary c) (hd : primary d) (F : Eisenstein → ℂ) :
    (∑ p ∈ primeCutoff B,
      if Squarefree ((c*p)*d) ∧ IsCoprime ((c*p)*d) e ∧
        (a < norm ((c*p)*d) ∧ norm ((c*p)*d) ≤ b) ∧
        stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
          j₀ k h Z Q early (c*p) d ∧ geometricPrimeBin ρ B p = j ∧
        largestPrimeChoice ((c*p)*d) = p then F p else 0) =
    if Squarefree (c*d) ∧ IsCoprime (c*d) e then
      ∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e)), F p
    else 0 := by
  calc
    _ = ∑ p ∈ primeCutoff B,
        if Squarefree (c*d) ∧ IsCoprime (c*d) e ∧
          p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e))
        then F p else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact if_congr (distinguished_prime_row_conditions hc hd hp) rfl rfl
    _ = _ := by
      by_cases hcd : Squarefree (c*d) ∧ IsCoprime (c*d) e
      · rw [ite_eq_left hcd]
        have he (p : Eisenstein) :
            (Squarefree (c*d) ∧ IsCoprime (c*d) e ∧
              p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e))) ↔
            p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d (c*(d*e)) := by
          constructor
          · exact fun hp => hp.2.2
          · exact fun hp => ⟨hcd.1,hcd.2,hp⟩
        simp_rw [if_congr (he _) rfl rfl]
        rw [←Finset.sum_filter,Finset.filter_mem_eq_of_subset
          (stoppedDistinguishedPrimeSet_subset B ρ a b j j₀ k h Z Q early c d (c*(d*e)))]
      · rw [ite_eq_right hcd]
        apply Finset.sum_eq_zero
        intro p hp
        exact ite_eq_right (fun hpred => hcd ⟨hpred.1,hpred.2.1⟩)

end CubicFirstMoment

end

end OAI
