import OAI.NumberTheory.JointDickman.Probability.SplitProjectionSupport

namespace OAI

/-! # Low-prime tests for either direction of a coefficient ratio -/

namespace JointDickman
open Finset

theorem retained_ratio_test {B : ℕ} {Y T : ℝ} {A D R Q I J U V : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B)
    (hR : R ⊆ auxiliaryPrimes B) (hQ : Q ⊆ auxiliaryPrimes B)
    (hAR : Disjoint A R) (hDQ : Disjoint D Q)
    (hI : I ⊆ A) (hJ : J ⊆ D) (hU : U ⊆ R) (hV : V ⊆ Q)
    (hnoA : ∀ p ∈ symmDiff A (I ∪ U), Real.log p ≤ Y)
    (hnoD : ∀ p ∈ symmDiff D (J ∪ V), Real.log p ≤ Y)
    (hlo : T * (∏ p ∈ J ∪ V, p : ℕ) ≤ (∏ p ∈ I ∪ U, p : ℕ))
    (hhi : (∏ p ∈ I ∪ U, p : ℕ) ≤ 2 * (T * (∏ p ∈ J ∪ V, p : ℕ)))
    (hadd : ∃ p ∈ (I ∪ U) \ A, Y / 2 < Real.log p) :
    additionRatioTest Y T
      (∏ p ∈ (I ∩ (A ∩ additionPrimes B Y)) ∪ (A ∩ upperAdditionPrimes B Y), p : ℕ)
      (∏ p ∈ (J ∩ (D ∩ additionPrimes B Y)) ∪ (D ∩ upperAdditionPrimes B Y), p : ℕ)
      (U ∩ additionPrimes B Y) (V ∩ additionPrimes B Y) = 1 := by
  classical
  obtain ⟨hIA, hUhi⟩ := retained_high_projection hA hR hAR hI hU hnoA
  obtain ⟨hJD, hVhi⟩ := retained_high_projection hD hQ hDQ hJ hV hnoD
  rw [retained_low_high_union hA hI hIA, retained_low_high_union hD hJ hJD,
    added_low_projection (hU.trans hR) hUhi, added_low_projection (hV.trans hQ) hVhi]
  have hIU : Disjoint I U := hAR.mono hI hU
  have hJV : Disjoint J V := hDQ.mono hJ hV
  rw [prod_union hIU, prod_union hJV, Nat.cast_mul, Nat.cast_mul] at hlo hhi
  have hlarge := addition_product_log_large (auxiliaryPrimes_prime B) (hU.trans hR) hadd hI
  exact ite_eq_left ⟨hlo, hhi, hlarge.le⟩

theorem reciprocal_ratio_bounds {T a c : ℝ} (hT : 0 < T)
    (hlo : T * c ≤ a) (hhi : a ≤ 2 * (T * c)) :
    (1 / (2 * T)) * a ≤ c ∧ c ≤ 2 * ((1 / (2 * T)) * a) := by
  constructor
  · calc
      _ = a / (2 * T) := by ring
      _ ≤ c := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hhi])
  · calc
      c ≤ a / T := (le_div_iff₀ hT).mpr (by nlinarith only [hlo])
      _ = _ := by field_simp

end JointDickman

end OAI
