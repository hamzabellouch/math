import OAI.NumberTheory.Ostmann.Construction.ConstituentAmplitudeEnergy
import OAI.NumberTheory.Ostmann.Construction.FinalHistoryCount
import OAI.NumberTheory.Ostmann.Arithmetic.RecursiveFrequencySupport

namespace OAI

/-! # Explicit exponential energy cost for the final scheduled coefficient -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem history_energy_rate (S : Finset ℤ) (n : ℕ) (F m d C K H : ℝ)
    (hF : 0 ≤ F) (hm : 0 ≤ m) (hS : (S.card : ℝ) ≤ Real.exp (F * m))
    (hH : C + 2 * K ≤ H * m) :
    (Fintype.card (FrequencyTree S n) : ℝ) ^ 2 *
        Real.exp (-(2 ^ n : ℕ) * (d * m) + (2 ^ n : ℕ) * (C + 2 * K)) ≤
      Real.exp ((4 * F - d + H) * (2 ^ n : ℕ) * m) := by
  have hk : 2 * (2 ^ (n + 1) - 1) ≤ 4 * 2 ^ n := by
    rw [pow_succ]
    omega
  have hkr : ((2 * (2 ^ (n + 1) - 1) : ℕ) : ℝ) ≤ 4 * (2 ^ n : ℕ) := by
    exact_mod_cast hk
  have hc := mul_le_mul_of_nonneg_right hkr (mul_nonneg hF hm)
  have hb := mul_le_mul_of_nonneg_left hH (show (0 : ℝ) ≤ (2 ^ n : ℕ) by positivity)
  have hcount : (Fintype.card (FrequencyTree S n) : ℝ) ^ 2 ≤
      Real.exp (((2 * (2 ^ (n + 1) - 1) : ℕ) : ℝ) * F * m) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using frequency_history_pair_card_bound S n F m hS
  calc
    _ ≤ Real.exp (((2 * (2 ^ (n + 1) - 1) : ℕ) : ℝ) * F * m) *
        Real.exp (-(2 ^ n : ℕ) * (d * m) + (2 ^ n : ℕ) * (C + 2 * K)) :=
      mul_le_mul_of_nonneg_right hcount
        (Real.exp_pos _).le
    _ = Real.exp (((2 * (2 ^ (n + 1) - 1) : ℕ) : ℝ) * F * m -
        (2 ^ n : ℕ) * (d * m) + (2 ^ n : ℕ) * (C + 2 * K)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      calc
        _ = (((2 * (2 ^ (n + 1) - 1) : ℕ) : ℝ) * (F * m)) +
            (2 ^ n : ℕ) * (-(d * m) + (C + 2 * K)) := by ring
        _ ≤ 4 * (2 ^ n : ℕ) * (F * m) + (2 ^ n : ℕ) * (-(d * m) + H * m) := by
          linarith
        _ = _ := by ring

theorem constituent_final_energy_rate {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
    (pivot : ℕ → (Σ i, Fin (size i))) (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : (Σ i, Fin (size i)) → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi d C K F H m : ℝ) (hX : 0 < X)
    (hlo : Real.exp (d * m - C) ≤ lo)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (S : Finset ℤ) (hF : 0 ≤ F) (hm : 0 ≤ m)
    (hS : (S.card : ℝ) ≤ Real.exp (F * m)) (hH : C + 2 * K ≤ H * m)
    (center : ∀ p : ℕ, ZMod p) :
    (∑ q : SurvivingConstituent role size n → P,
      (∏ i, primeSubsetPrior P (Q (copyScheduleOrigin n i.val)) (q i)) *
        ‖constituentPrimeCoefficient role size χ κ pivot n P hP childBound pivotBound ranges
          (scheduleFourierLeaf role ψ X lo hi) (frequencyTreeMap (fun v : S => (v : ℤ)) n) center q‖ ^ 2) ≤
      Real.exp ((4 * F - d + H) * (2 ^ n : ℕ) * m) := by
  exact (constituentPrimeCoefficient_mean_energy role size χ κ hκ pivot n P hP Q hQP hQ
    childBound pivotBound ranges ψ X lo hi (d * m) C K hX hlo hψ
    (frequencyTreeMap (fun v : S => (v : ℤ)) n) center).trans
    (history_energy_rate S n F m d C K H hF hm hS hH)

end Ostmann

end OAI
