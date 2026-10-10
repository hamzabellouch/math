import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternFinite
import OAI.NumberTheory.Ostmann.Arithmetic.MovingInternalProductError

namespace OAI

/-! # Prime-square exclusions under the original pattern priors -/

namespace Ostmann
open scoped Classical BigOperators

/-- The relative square error for the actual class-indexed collection of
internal primes. Every class has a proved occurrence in the history pair. -/
theorem movingRepresentativeProduct_error {σ C : Type*} [Fintype C]
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hlevels : ∀ b, (T b).Levels tier)
    (rep : C → σ) (base : ∀ c, MovingPairRepresentativeOccurrences T (rep c))
    (hf : ∀ c b, (T b).Frequencies (fun s => (s : ZMod (value (rep c))) ≠ 0))
    (V : ℝ) (hsize : ∀ c, Real.exp V ≤ value (rep c)) :
    letI : ∀ c, Fact (value (rep c)).Prime := fun _ => ⟨hprime _⟩
    ‖(∏ c, movingInternalHaarAverage value T (value (rep c))) -
      ∏ c, (movingInternalLineProbability value T (value (rep c)) : ℂ)‖ ≤
        ((2 * (2 ^ n - 1 : ℕ)) * Fintype.card C * Real.exp (-V)) *
          ∏ c, (value (rep c) : ℝ)⁻¹ := by
  let _ : ∀ c, Fact (value (rep c)).Prime := fun _ => ⟨hprime _⟩
  have hprob (c) : 0 ≤ movingInternalLineProbability value T (value (rep c)) :=
    movingInternalLineProbability_nonneg value T _
  have hline (c) : movingInternalLineProbability value T (value (rep c)) ≤
      (value (rep c) : ℝ)⁻¹ := by
    let j : MovingPrimeOccurrences value T (value (rep c)) :=
      ⟨(base c).1, ⟨(base c).2.val, ⟨rep c, (base c).2.property, rfl⟩⟩⟩
    exact movingInternalLineProbability_le_inv tier value hprime hdisjoint T hlevels _ (hf c) j
  have hs : (∑ c, (value (rep c) : ℝ)⁻¹) ≤ (Fintype.card C : ℝ) * Real.exp (-V) := by
    calc
      _ ≤ ∑ _c : C, Real.exp (-V) := by
        apply Finset.sum_le_sum
        intro c _
        simpa only [Real.exp_neg] using inv_anti₀ (Real.exp_pos V) (hsize c)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h := finite_relative_product_error (Finset.univ : Finset C)
    (fun c => movingInternalHaarAverage value T (value (rep c)))
    (fun c => (movingInternalLineProbability value T (value (rep c)) : ℂ))
    (fun c => movingInternalLineProbability value T (value (rep c)))
    (fun c => 2 * (2 ^ n - 1 : ℕ) / (value (rep c) : ℝ))
    (fun c _ => hprob c) (fun c _ => by positivity)
    (fun c _ => movingInternalPairFactor_probability_norm_le value T _)
    (fun c _ => by rw [Complex.norm_real, Real.norm_of_nonneg (hprob c)])
    (fun c _ => movingInternalPairFactor_probability_error tier value hprime hdisjoint T hlevels _ (hf c))
  have hp : (∏ c, movingInternalLineProbability value T (value (rep c))) ≤
      ∏ c, (value (rep c) : ℝ)⁻¹ :=
    Finset.prod_le_prod₀ (fun c _ => hprob c) (fun c _ => hline c)
  have hk : (∑ c, 2 * (2 ^ n - 1 : ℕ) / (value (rep c) : ℝ)) ≤
      (2 * (2 ^ n - 1 : ℕ)) * Fintype.card C * Real.exp (-V) := by
    simp only [div_eq_mul_inv, ← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring)
  exact h.trans (mul_le_mul hk hp (Finset.prod_nonneg (fun c _ => hprob c)) (by positivity))

/-- Integrating a relative local error uses the original normalized prior,
not a conditioned law. The retained scale may include every internal class. -/
theorem productPrior_relative_error {A : Type*} [Fintype A] {N : ℕ}
    (μ : Fin N → A → ℝ) (hmass : ∀ i, ∑ a, μ i a = 1)
    (weight err : (Fin N → A) → ℂ) (scale : (Fin N → A) → ℝ)
    (B K : ℝ) (hK : 0 ≤ K)
    (hweight : ∀ x, ‖weight x‖ * scale x ≤ B * productPrior μ x)
    (herr : ∀ x, weight x ≠ 0 → ‖err x‖ ≤ K * scale x) :
    ‖∑ x, weight x * err x‖ ≤ B * K := by
  calc
    _ ≤ ∑ x, ‖weight x * err x‖ := norm_sum_le _ _
    _ ≤ ∑ x, K * (B * productPrior μ x) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hz : weight x = 0
      · have hb := hweight x
        rw [hz, norm_zero, zero_mul] at hb
        simpa only [hz, zero_mul, norm_zero] using mul_nonneg hK hb
      · rw [norm_mul]
        calc
          _ ≤ ‖weight x‖ * (K * scale x) :=
            mul_le_mul_of_nonneg_left (herr x hz) (norm_nonneg _)
          _ = K * (‖weight x‖ * scale x) := by ring
          _ ≤ K * (B * productPrior μ x) := mul_le_mul_of_nonneg_left (hweight x) hK
    _ = B * K := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, productPrior_mass μ hmass]
      ring

end Ostmann

end OAI
