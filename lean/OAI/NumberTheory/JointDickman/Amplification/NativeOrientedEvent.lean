import OAI.NumberTheory.JointDickman.Probability.ConditionalCoinAverage
import OAI.NumberTheory.JointDickman.Probability.SplitProjectionSupport

namespace OAI

/-! # Domination of the actual oriented event by the conditional operator -/

namespace JointDickman
open Finset

def nativeOrientedEvent (B L T : ℕ) (τ C Y : ℝ)
    (A D R Q I J U V : Finset ℕ) : Prop :=
  Disjoint A R ∧ Disjoint D Q ∧ U ⊆ R ∧ V ⊆ Q ∧
  RegularPrimeSet B L τ C R ∧ RegularPrimeSet B L τ C Q ∧
  (∀ p ∈ symmDiff A (I ∪ U), Real.log p ≤ Y) ∧
  (∀ p ∈ symmDiff D (J ∪ V), Real.log p ≤ Y) ∧
  (∏ p ∈ I ∪ U, p, ∏ p ∈ J ∪ V, p) ∈ amplificationCoefficientPairs B T ∧
  ∃ p ∈ (I ∪ U) \ A, Y / 2 < Real.log p

open Classical in
noncomputable def nativeOrientedMass (B L T : ℕ) (τ C Y : ℝ) (A D : Finset ℕ) : ℝ :=
  conditionalCoinAverage (auxiliaryPrimes B) A D
    (fun R Q I J U V => if nativeOrientedEvent B L T τ C Y A D R Q I J U V then 1 else 0)

/-- The native event forces all four high-prime restrictions and the exact
low-prime ratio test. Its two regular remaining sets supply the tail counts. -/
theorem nativeOrientedMass_le {B L T i : ℕ} {τ C : ℝ} {A D : Finset ℕ}
    (hB : 0 < B) (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    nativeOrientedMass B L T τ C (primeTailEndpoint B i) A D ≤
      orientedSplitMass B A D (primeTailEndpoint B i) C T := by
  classical
  rw [orientedSplitMass_expansion B A D (primeTailEndpoint B i) C T hA hD]
  change conditionalCoinAverage _ _ _ _ ≤ conditionalCoinAverage _ _ _ _
  apply conditionalCoinAverage_mono (auxiliaryPrimes_prime B)
  intro I hI J hJ R hR Q hQ U _ V _
  by_cases he : nativeOrientedEvent B L T τ C (primeTailEndpoint B i) A D R Q I J U V
  · have he' := he
    obtain ⟨hAR, hDQ, hU, hV, hRreg, hQreg, hnoA, hnoD, hpair, hadd⟩ := he
    obtain ⟨hi, hu⟩ := retained_high_projection hA hR hAR hI hU hnoA
    obtain ⟨hj, hv⟩ := retained_high_projection hD hQ hDQ hJ hV hnoD
    have hi' : I ∩ (A ∩ upperAdditionPrimes B (primeTailEndpoint B i)) =
        A ∩ upperAdditionPrimes B (primeTailEndpoint B i) := by
      rw [← inter_assoc, inter_eq_left.mpr hI, hi]
    have hj' : J ∩ (D ∩ upperAdditionPrimes B (primeTailEndpoint B i)) =
        D ∩ upperAdditionPrimes B (primeTailEndpoint B i) := by
      rw [← inter_assoc, inter_eq_left.mpr hJ, hj]
    have hr : (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C ≤
        ((R ∩ upperAdditionPrimes B (primeTailEndpoint B i)).card : ℝ) := by
      rw [selected_upperAdditionPrimes hR]
      exact hRreg.2 i
    have hq : (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C ≤
        ((Q ∩ upperAdditionPrimes B (primeTailEndpoint B i)).card : ℝ) := by
      rw [selected_upperAdditionPrimes hQ]
      exact hQreg.2 i
    have ht := native_oriented_ratio_test hB hA hD hR hQ hAR hDQ hI hJ hU hV
      hnoA hnoD hpair hadd
    simp only [he', hi', hj', hq, hv, hr, hu, and_self, ite_true, ht, le_refl]
  · simp only [ite_eq_right he]
    split_ifs
    · unfold additionRatioTest
      split_ifs <;> norm_num
    · exact le_rfl

end JointDickman

end OAI
