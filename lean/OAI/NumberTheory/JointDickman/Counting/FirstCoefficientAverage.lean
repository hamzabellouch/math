import OAI.NumberTheory.JointDickman.Amplification.OrientedProbabilityBound
import OAI.NumberTheory.JointDickman.Arithmetic.PrimePairPushforward

namespace OAI

/-! # Averaging conditional estimates over the first coefficient event -/

namespace JointDickman
open Finset

open Classical in
noncomputable def firstCoefficientAverage (B L T : ℕ) (τ C : ℝ)
    (F : Finset ℕ → Finset ℕ → ℝ) : ℝ :=
  ∑ A ∈ (auxiliaryPrimes B).powerset,
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
  ∑ D ∈ (auxiliaryPrimes B).powerset,
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) D *
    (if firstCoefficientGood B L T τ C A D then F A D else 0)

theorem auxiliaryHalfSubsetMass_nonneg {B : ℕ} {A : Finset ℕ} (hA : A ⊆ auxiliaryPrimes B) :
    0 ≤ bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A := by
  apply bernoulliSubsetMass_nonneg hA
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
  exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩

open Classical in
theorem firstCoefficientAverage_le {B L T : ℕ} {τ C K : ℝ}
    (hK : 0 ≤ K) (F : Finset ℕ → Finset ℕ → ℝ)
    (hF : ∀ A ⊆ auxiliaryPrimes B, ∀ D ⊆ auxiliaryPrimes B,
      firstCoefficientGood B L T τ C A D → F A D ≤ K) :
    firstCoefficientAverage B L T τ C F ≤ K *
      ∑ ac ∈ amplificationCoefficientPairs B T,
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2 := by
  rw [primeProductPair_sum_event]
  simp only [mul_sum]
  unfold firstCoefficientAverage
  apply sum_le_sum
  intro A hA
  rw [mul_sum]
  apply sum_le_sum
  intro D hD
  have ha := auxiliaryHalfSubsetMass_nonneg (mem_powerset.mp hA)
  have hd := auxiliaryHalfSubsetMass_nonneg (mem_powerset.mp hD)
  by_cases hg : firstCoefficientGood B L T τ C A D
  · have hm := hg.1
    simp only [hg, hm, ite_true]
    calc
      _ ≤ bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
          (bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) D * K) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (hF A (mem_powerset.mp hA) D (mem_powerset.mp hD) hg) hd) ha
      _ = _ := by ring
  · simp only [hg, ite_false, mul_zero]
    split_ifs
    · exact mul_nonneg hK (mul_nonneg ha hd)
    · simp only [mul_zero, le_refl]

open Classical in
theorem firstCoefficientAverage_sum (B L T : ℕ) (τ C : ℝ) (S : Finset ℕ)
    (F : ℕ → Finset ℕ → Finset ℕ → ℝ) :
    (∑ i ∈ S, firstCoefficientAverage B L T τ C (F i)) =
      firstCoefficientAverage B L T τ C (fun A D => ∑ i ∈ S, F i A D) := by
  unfold firstCoefficientAverage
  rw [sum_comm]
  apply sum_congr rfl
  intro A _
  simp only [← mul_sum]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro D _
  simp only [← mul_sum]
  congr 1
  by_cases hg : firstCoefficientGood B L T τ C A D <;> simp [hg]

end JointDickman

end OAI
