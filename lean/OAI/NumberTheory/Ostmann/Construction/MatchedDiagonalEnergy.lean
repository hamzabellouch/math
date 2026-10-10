import OAI.NumberTheory.Ostmann.Construction.MatchedHarmonicPrior
import OAI.NumberTheory.Ostmann.Construction.TransferHistoryEnergy

namespace OAI

/-! # Retaining one branch's original prior in the matched diagonal -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

private theorem matched_energy_point (a b A₀ x y : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (haA₀ : a ≤ A₀) (hbA₀ : b ≤ A₀) :
    a * b * x * y ≤ A₀ / 2 * (a * x ^ 2 + b * y ^ 2) := by
  have hsq := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))
  have hx := mul_le_mul_of_nonneg_left hbA₀ (mul_nonneg ha (sq_nonneg x))
  have hy := mul_le_mul_of_nonneg_left haA₀ (mul_nonneg hb (sq_nonneg y))
  nlinarith only [hsq, hx, hy]

/-- The other branch's point weight is bounded only on simultaneous support.
Each resulting square retains its own original sampling law. -/
theorem matched_diagonal_energy {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (μ : A → ℝ) (ν : B → ℝ) (W : A → ℂ) (Z : B → ℂ)
    (θ : A → ℂ) (A₀ : ℝ) (hA₀ : 0 ≤ A₀)
    (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b) (hθ : ∀ a, ‖θ a‖ ≤ 1)
    (hpoint : ∀ a, W a ≠ 0 → Z (e a) ≠ 0 → μ a ≤ A₀ ∧ ν (e a) ≤ A₀) :
    ‖∑ a, ((μ a * ν (e a) : ℝ) : ℂ) * W a * conj (Z (e a)) * θ a‖ ≤
      A₀ / 2 * ((∑ a, μ a * ‖W a‖ ^ 2) + ∑ b, ν b * ‖Z b‖ ^ 2) := by
  have hp (a : A) : μ a * ν (e a) * ‖W a‖ * ‖Z (e a)‖ ≤
      A₀ / 2 * (μ a * ‖W a‖ ^ 2 + ν (e a) * ‖Z (e a)‖ ^ 2) := by
    have hμa := hμ a
    have hνa := hν (e a)
    by_cases hW : W a = 0
    · simp only [hW, norm_zero, mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), zero_add]
      positivity
    by_cases hZ : Z (e a) = 0
    · simp only [hZ, norm_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
      positivity
    exact matched_energy_point _ _ _ _ _ (hμ a) (hν (e a))
      (hpoint a hW hZ).1 (hpoint a hW hZ).2
  calc
    _ ≤ ∑ a, ‖((μ a * ν (e a) : ℝ) : ℂ) * W a * conj (Z (e a)) * θ a‖ := norm_sum_le _ _
    _ ≤ ∑ a, μ a * ν (e a) * ‖W a‖ * ‖Z (e a)‖ := by
      apply Finset.sum_le_sum
      intro a _
      simp only [norm_mul, Complex.norm_conj, Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg (hμ a) (hν (e a)))]
      exact mul_le_of_le_one_right
        (mul_nonneg (mul_nonneg (mul_nonneg (hμ a) (hν (e a))) (norm_nonneg _))
          (norm_nonneg _)) (hθ a)
    _ ≤ ∑ a, A₀ / 2 * (μ a * ‖W a‖ ^ 2 + ν (e a) * ‖Z (e a)‖ ^ 2) :=
      Finset.sum_le_sum fun a _ => hp a
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, e.sum_comp (fun b => ν b * ‖Z b‖ ^ 2)]

/-- The external-integer count is canceled only after extracting the
counterpart's reciprocal scale. -/
theorem external_pivot_normalization {P : Type*} [Fintype P]
    (F : P → ℂ) (C E T Δ κ : ℝ) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hcard : (Fintype.card P : ℝ) ≤ Real.exp (T + κ))
    (hF : ∀ p, ‖F p‖ ≤ C * Real.exp (-(T + Δ)) * E) :
    ‖∑ p, F p‖ ≤ C * Real.exp (κ - Δ) * E := by
  calc
    _ ≤ ∑ p, ‖F p‖ := norm_sum_le _ _
    _ ≤ ∑ _p : P, C * Real.exp (-(T + Δ)) * E := Finset.sum_le_sum fun p _ => hF p
    _ = (Fintype.card P : ℝ) * (C * Real.exp (-(T + Δ)) * E) := by simp
    _ ≤ Real.exp (T + κ) * (C * Real.exp (-(T + Δ)) * E) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      have he : Real.exp (T + κ) * Real.exp (-(T + Δ)) = Real.exp (κ - Δ) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = C * (Real.exp (T + κ) * Real.exp (-(T + Δ))) * E := by ring
        _ = _ := by rw [he]

end Ostmann

end OAI
