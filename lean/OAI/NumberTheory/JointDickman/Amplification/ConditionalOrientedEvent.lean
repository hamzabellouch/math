import OAI.NumberTheory.JointDickman.Amplification.RetainedRatioTest
import OAI.NumberTheory.JointDickman.Probability.ConditionalCoinSupport

namespace OAI

/-! # Conditional oriented bounds for a specified native ratio event -/

namespace JointDickman
open Finset

open Classical in
theorem conditional_oriented_event_bound {B L i : ℕ} {τ C T : ℝ} {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B)
    (E : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Prop)
    (hE : ∀ I ⊆ A, ∀ J ⊆ D, ∀ R ⊆ auxiliaryPrimes B, ∀ Q ⊆ auxiliaryPrimes B,
      ∀ U ⊆ R, ∀ V ⊆ Q, Disjoint A R → Disjoint D Q → E R Q I J U V →
      RegularPrimeSet B L τ C R ∧ RegularPrimeSet B L τ C Q ∧
      (∀ p ∈ symmDiff A (I ∪ U), Real.log p ≤ primeTailEndpoint B i) ∧
      (∀ p ∈ symmDiff D (J ∪ V), Real.log p ≤ primeTailEndpoint B i) ∧
      T * (∏ p ∈ J ∪ V, p : ℕ) ≤ (∏ p ∈ I ∪ U, p : ℕ) ∧
      (∏ p ∈ I ∪ U, p : ℕ) ≤ 2 * (T * (∏ p ∈ J ∪ V, p : ℕ)) ∧
      ∃ p ∈ (I ∪ U) \ A, primeTailEndpoint B i / 2 < Real.log p) :
    conditionalCoinAverage (auxiliaryPrimes B) A D
      (fun R Q I J U V => if E R Q I J U V then 1 else 0) ≤
      orientedSplitMass B A D (primeTailEndpoint B i) C T := by
  rw [orientedSplitMass_expansion B A D (primeTailEndpoint B i) C T hA hD]
  change conditionalCoinAverage _ _ _ _ ≤ conditionalCoinAverage _ _ _ _
  apply conditionalCoinAverage_le_on_support (auxiliaryPrimes_prime B)
  intro I hI J hJ R hR Q hQ U hU V hV hAR hDQ
  by_cases he : E R Q I J U V
  · obtain ⟨hr, hq, hnA, hnD, hlo, hhi, hadd⟩ := hE I hI J hJ R hR Q hQ U hU V hV hAR hDQ he
    obtain ⟨hi, hu⟩ := retained_high_projection hA hR hAR hI hU hnA
    obtain ⟨hj, hv⟩ := retained_high_projection hD hQ hDQ hJ hV hnD
    have hi' : I ∩ (A ∩ upperAdditionPrimes B (primeTailEndpoint B i)) =
        A ∩ upperAdditionPrimes B (primeTailEndpoint B i) := by
      rw [← inter_assoc, inter_eq_left.mpr hI, hi]
    have hj' : J ∩ (D ∩ upperAdditionPrimes B (primeTailEndpoint B i)) =
        D ∩ upperAdditionPrimes B (primeTailEndpoint B i) := by
      rw [← inter_assoc, inter_eq_left.mpr hJ, hj]
    have hr' : (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C ≤
        ((R ∩ upperAdditionPrimes B (primeTailEndpoint B i)).card : ℝ) := by
      rw [selected_upperAdditionPrimes hR]
      exact hr.2 i
    have hq' : (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C ≤
        ((Q ∩ upperAdditionPrimes B (primeTailEndpoint B i)).card : ℝ) := by
      rw [selected_upperAdditionPrimes hQ]
      exact hq.2 i
    have ht := retained_ratio_test hA hD hR hQ hAR hDQ hI hJ hU hV hnA hnD hlo hhi hadd
    simp only [he, hi', hj', hq', hv, hr', hu, and_self, ite_true, ht, le_refl]
  · simp only [he, ite_false]
    split_ifs
    · unfold additionRatioTest
      split_ifs <;> norm_num
    · exact le_rfl

end JointDickman

end OAI
