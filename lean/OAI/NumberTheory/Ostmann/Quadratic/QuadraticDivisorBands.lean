import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDivisorMomentBound

namespace OAI

/-! # Concrete divisor intervals and the shortened matrix ranges -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticDivisorBand (D : ℕ) : Finset ℕ :=
  (oddSquarefreeRange (2 * D)).filter (fun s => D < s)

 theorem quadraticDivisorBand_card (D : ℕ) : (quadraticDivisorBand D).card ≤ D := by
  have hs : quadraticDivisorBand D ⊆ Finset.Ioc D (2 * D) := by
    intro s hs
    obtain ⟨hr, hD⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_Ioc.mpr ⟨hD, (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).2⟩
  calc
    _ ≤ (Finset.Ioc D (2 * D)).card := Finset.card_le_card hs
    _ = D := by simp; omega

 theorem quadratic_divisor_band_bound (M N₁ N₂ D₁ D₂ : ℕ)
    (hD₁ : 0 < D₁) (hD₂ : 0 < D₂) (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M (N₁ / D₁) K₁)
    (h₂ : QuadraticSieveBound M (N₂ / D₂) K₂) (a b : ℕ → ℂ) :
    (∑ s₁ ∈ quadraticDivisorBand D₁, ∑ s₂ ∈ quadraticDivisorBand D₂,
      ∑ m ∈ oddSquarefreeRange M, ‖quadraticCoprimeBilinear N₁ N₂
        (fun n => if s₁ ∣ n then a n else 0)
        (fun n => if s₂ ∣ n then b n else 0) m‖) ≤
      Real.sqrt (2 * K₁ * D₁ * quadraticDivisorMoment N₁ a) *
      Real.sqrt (2 * K₂ * D₂ * quadraticDivisorMoment N₂ b) := by
  have hs (D : ℕ) (s : ℕ) (h : s ∈ quadraticDivisorBand D) :
      Squarefree s ∧ Odd s := by
    obtain ⟨hr, _⟩ := Finset.mem_filter.mp h
    exact ⟨(Finset.mem_filter.mp hr).2.2, (Finset.mem_filter.mp hr).2.1⟩
  have hcut₁ : ∀ s ∈ quadraticDivisorBand D₁, QuadraticSieveBound M (N₁ / s) K₁ := by
    intro s hs'
    exact QuadraticSieveBound.mono_second
      (Nat.div_le_div_left (Finset.mem_filter.mp hs').2.le hD₁) h₁
  have hcut₂ : ∀ s ∈ quadraticDivisorBand D₂, QuadraticSieveBound M (N₂ / s) K₂ := by
    intro s hs'
    exact QuadraticSieveBound.mono_second
      (Nat.div_le_div_left (Finset.mem_filter.mp hs').2.le hD₂) h₂
  apply (quadratic_divisor_family_bound M N₁ N₂ _ _ K₁ K₂ hK₁ hK₂
    (hs D₁) (hs D₂) hcut₁ hcut₂ a b).trans
  apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast quadraticDivisorBand_card D₁)
        (by positivity)) (quadraticDivisorMoment_nonneg N₁ a)
  · apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast quadraticDivisorBand_card D₂)
        (by positivity)) (quadraticDivisorMoment_nonneg N₂ b)

end Ostmann

end OAI
