import OAI.NumberTheory.Ostmann.Quadratic.QuadraticRootDivisor

namespace OAI

/-! # A uniform comparison for every positive second-transform parameter -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_positive_root_gauss_bound (ρ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M N D : ℕ) (X : ℕ → ℕ → ℝ), 0 < N →
      (∀ d ∈ Finset.Ioc D (2 * D), ∀ m ∈ oddSquarefreeRange M, 0 < X d m) →
      ∀ (a b : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℝ), 0 ≤ T →
      (∀ n < N, a n = 0) → (∀ n < N, b n = 0) →
      (∀ i ≤ Nat.log 2 (2 * N), 0 ≤ K₁ i) →
      (∀ j ≤ Nat.log 2 (2 * N), 0 ≤ K₂ j) →
      (∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound M (2 * N / 2 ^ i) (K₁ i)) →
      (∀ j ≤ Nat.log 2 (2 * N), QuadraticSieveBound M (2 * N / 2 ^ j) (K₂ j)) →
      (∀ i ≤ Nat.log 2 (2 * N), ∀ j ≤ Nat.log 2 (2 * N),
        D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
        Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment (2 * N) a) *
          Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment (2 * N) b) ≤ T) →
      (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticRootGaussDivisor ρ (X d m) N d a b m‖) ≤
          C * ((((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ)) ^ 2 * T) := by
  obtain ⟨C, hC, hc⟩ := quadratic_varying_root_gauss_bound ρ 0
  refine ⟨C, hC, ?_⟩
  intro M N D X hN hX a b K₁ K₂ T hT ha hb hK₁ hK₂ h₁ h₂ hcost
  let F := (Finset.Ioc D (2 * D)).product (oddSquarefreeRange M)
  by_cases hF : F.Nonempty
  · obtain ⟨z, hz, hmin⟩ := F.exists_min_image (fun z => X z.1 z.2) hF
    obtain ⟨hzd, hzm⟩ := Finset.mem_product.mp hz
    have hY : 0 < X z.1 z.2 := hX z.1 hzd z.2 hzm
    have hYX : ∀ d ∈ Finset.Ioc D (2 * D), ∀ m ∈ oddSquarefreeRange M,
        X z.1 z.2 ≤ X d m := by
      intro d hd m hm
      exact hmin (d, m) (Finset.mem_product.mpr ⟨hd, hm⟩)
    simpa only [pow_zero, div_one, min_self, mul_one] using
      hc M N D X (X z.1 z.2) hN hY hYX a b K₁ K₂ T hT ha hb hK₁ hK₂ h₁ h₂ hcost
  · have hf : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    have hz : (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticRootGaussDivisor ρ (X d m) N d a b m‖) = 0 := by
      calc
        _ = ∑ z ∈ F, ‖quadraticRootGaussDivisor ρ (X z.1 z.2) N z.1 a b z.2‖ := by
          dsimp only [F]
          rw [Finset.product_eq_sprod, Finset.sum_product]
        _ = 0 := by rw [hf, Finset.sum_empty]
    rw [hz]
    positivity

end Ostmann

end OAI
