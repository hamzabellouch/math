import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGaussBilinear

namespace OAI

/-! # The divisor-one block, retained separately from positive dyadic intervals -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_unit_divisor_bound (M N₁ N₂ : ℕ) (K₁ K₂ : ℝ)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M N₁ K₁) (h₂ : QuadraticSieveBound M N₂ K₂)
    (a b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M, ‖quadraticDivisorBilinear N₁ N₂ 1 a b m‖) ≤
      Real.sqrt (2 * K₁ * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ * quadraticDivisorMoment N₂ b) := by
  have hshape : ∀ s ∈ ({1} : Finset ℕ), Squarefree s ∧ Odd s := by
    intro s hs
    have he : s = 1 := Finset.mem_singleton.mp hs
    subst s
    norm_num
  have hcut₁ : ∀ s ∈ ({1} : Finset ℕ), QuadraticSieveBound M (N₁ / s) K₁ := by
    intro s hs
    simpa only [Finset.mem_singleton.mp hs, Nat.div_one] using h₁
  have hcut₂ : ∀ s ∈ ({1} : Finset ℕ), QuadraticSieveBound M (N₂ / s) K₂ := by
    intro s hs
    simpa only [Finset.mem_singleton.mp hs, Nat.div_one] using h₂
  have h := quadratic_divisor_family_bound M N₁ N₂ {1} {1} K₁ K₂
    hK₁ hK₂ hshape hshape hcut₁ hcut₂ a b
  have he (m : ℤ) : quadraticDivisorBilinear N₁ N₂ 1 a b m =
      quadraticCoprimeBilinear N₁ N₂ a b m := by
    simp only [quadraticDivisorBilinear, quadraticCoprimeBilinear, one_dvd, and_true]
  simpa only [he, Finset.sum_singleton, one_dvd, ite_true,
    Finset.card_singleton, Nat.cast_one, mul_one] using h

theorem quadratic_gauss_unit_divisor_bound (M N₁ N₂ : ℕ) (K₁ K₂ : ℝ)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M N₁ K₁) (h₂ : QuadraticSieveBound M N₂ K₂)
    (a b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M, ‖quadraticGaussDivisorBilinear N₁ N₂ 1 a b m‖) ≤
      3 * (Real.sqrt (2 * K₁ * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ * quadraticDivisorMoment N₂ b)) := by
  have hleft := quadratic_unit_divisor_bound M N₁ N₂ K₁ K₂ hK₁ hK₂ h₁ h₂
    (quadraticGaussLeft a) (quadraticGaussRight b)
  simp only [quadraticDivisorMoment_gaussLeft, quadraticDivisorMoment_gaussRight] at hleft
  have hright := quadratic_unit_divisor_bound M N₁ N₂ K₁ K₂ hK₁ hK₂ h₁ h₂
    (quadraticThreeClass (quadraticGaussLeft a)) (quadraticThreeClass (quadraticGaussRight b))
  have hright' : (∑ m ∈ oddSquarefreeRange M,
      ‖quadraticDivisorBilinear N₁ N₂ 1 (quadraticThreeClass (quadraticGaussLeft a))
        (quadraticThreeClass (quadraticGaussRight b)) m‖) ≤
      Real.sqrt (2 * K₁ * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ * quadraticDivisorMoment N₂ b) := by
    apply hright.trans
    apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [quadraticDivisorMoment_gaussLeft] using
        quadraticDivisorMoment_threeClass N₁ (quadraticGaussLeft a)
    · apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [quadraticDivisorMoment_gaussRight] using
        quadraticDivisorMoment_threeClass N₂ (quadraticGaussRight b)
  calc
    _ ≤ ∑ m ∈ oddSquarefreeRange M,
        (‖quadraticDivisorBilinear N₁ N₂ 1 (quadraticGaussLeft a) (quadraticGaussRight b) m‖ +
        2 * ‖quadraticDivisorBilinear N₁ N₂ 1 (quadraticThreeClass (quadraticGaussLeft a))
          (quadraticThreeClass (quadraticGaussRight b)) m‖) := by
      apply Finset.sum_le_sum
      intro m _
      rw [quadratic_gauss_divisor_bilinear_split]
      exact (norm_sub_le _ _).trans (by norm_num [norm_mul])
    _ = (∑ m ∈ oddSquarefreeRange M,
        ‖quadraticDivisorBilinear N₁ N₂ 1 (quadraticGaussLeft a) (quadraticGaussRight b) m‖) +
        2 * ∑ m ∈ oddSquarefreeRange M,
          ‖quadraticDivisorBilinear N₁ N₂ 1 (quadraticThreeClass (quadraticGaussLeft a))
            (quadraticThreeClass (quadraticGaussRight b)) m‖ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := by linarith

end Ostmann

end OAI
