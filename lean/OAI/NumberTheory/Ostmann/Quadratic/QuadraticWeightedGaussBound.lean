import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGaussBilinear
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticWeightedBilinearBound

namespace OAI

/-! # Smooth divisor comparison with the actual quadratic Gauss coefficient -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

noncomputable def quadraticLogWeightedGaussDivisor (f : 𝓢(ℝ, ℂ)) (N₁ N₂ d : ℕ)
    (a b : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ s ∈ oddSquarefreeRange N₁, ∑ t ∈ oddSquarefreeRange N₂,
    (if s.Coprime t ∧ d ∣ s * t then (1 : ℂ) else 0) *
      a s * conj (b t) * quadraticGaussMultiplier (s * t) *
      (jacobiSym m s : ℂ) * (jacobiSym m t : ℂ) * f (Real.log s + Real.log t)

 theorem quadratic_log_weighted_gauss_split (f : 𝓢(ℝ, ℂ)) (N₁ N₂ d : ℕ)
    (a b : ℕ → ℂ) (m : ℤ) :
    quadraticLogWeightedGaussDivisor f N₁ N₂ d a b m =
      quadraticLogWeightedDivisor f N₁ N₂ d (quadraticGaussLeft a) (quadraticGaussRight b) m -
      2 * quadraticLogWeightedDivisor f N₁ N₂ d
        (quadraticThreeClass (quadraticGaussLeft a))
        (quadraticThreeClass (quadraticGaussRight b)) m := by
  unfold quadraticLogWeightedGaussDivisor quadraticLogWeightedDivisor
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨_, hos, hss⟩ := Finset.mem_filter.mp hs
  obtain ⟨_, hot, hst⟩ := Finset.mem_filter.mp ht
  by_cases hc : s.Coprime t ∧ d ∣ s * t
  · rw [ite_eq_left hc, quadraticGaussMultiplier_mul hc.1 hss hst hos hot]
    simp only [quadraticGaussLeft, quadraticGaussRight, quadraticThreeClass,
      map_mul, starRingEnd_self_apply]
    by_cases hs3 : s % 4 = 3 <;> by_cases ht3 : t % 4 = 3 <;>
      simp only [hs3, ht3, and_self, and_false, false_and, ite_true, ite_false,
        map_zero, map_mul, starRingEnd_self_apply, mul_zero, zero_mul, sub_zero, one_mul] <;> ring
  · simp [hc]

 theorem quadratic_weighted_gauss_bound (f : 𝓢(ℝ, ℂ)) (M N₁ N₂ D : ℕ)
    (a b : ℕ → ℂ) (K₁ K₂ : ℕ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hK₁ : ∀ i ≤ Nat.log 2 N₁, 0 ≤ K₁ i)
    (hK₂ : ∀ j ≤ Nat.log 2 N₂, 0 ≤ K₂ j)
    (h₁ : ∀ i ≤ Nat.log 2 N₁, QuadraticSieveBound M (N₁ / 2 ^ i) (K₁ i))
    (h₂ : ∀ j ≤ Nat.log 2 N₂, QuadraticSieveBound M (N₂ / 2 ^ j) (K₂ j))
    (hcost : ∀ i ≤ Nat.log 2 N₁, ∀ j ≤ Nat.log 2 N₂,
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b) ≤ T) :
    (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticLogWeightedGaussDivisor f N₁ N₂ d a b m‖) ≤
      3 * (∫ u : ℝ, ‖𝓕 f u‖) *
        (((Nat.log 2 N₁ + 1 : ℕ) : ℝ) * (Nat.log 2 N₂ + 1) * T) := by
  have hc₁ : ∀ i ≤ Nat.log 2 N₁, ∀ j ≤ Nat.log 2 N₂,
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ (quadraticGaussLeft a)) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ (quadraticGaussRight b)) ≤ T := by
    simpa only [quadraticDivisorMoment_gaussLeft, quadraticDivisorMoment_gaussRight] using hcost
  have hc₂ : ∀ i ≤ Nat.log 2 N₁, ∀ j ≤ Nat.log 2 N₂,
      D < 4 * (2 ^ i * 2 ^ j) → 2 ^ i * 2 ^ j ≤ 2 * D →
      Real.sqrt (2 * K₁ i * (2 ^ i : ℕ) * quadraticDivisorMoment N₁
        (quadraticThreeClass (quadraticGaussLeft a))) *
        Real.sqrt (2 * K₂ j * (2 ^ j : ℕ) * quadraticDivisorMoment N₂
          (quadraticThreeClass (quadraticGaussRight b))) ≤ T := by
    intro i hi j hj hlo hhi
    apply le_trans _ (hc₁ i hi j hj hlo hhi)
    gcongr
    · have := hK₁ i hi
      positivity
    · exact quadraticDivisorMoment_threeClass _ _
    · have := hK₂ j hj
      positivity
    · exact quadraticDivisorMoment_threeClass _ _
  have hb₁ := quadratic_weighted_bilinear_bound f M N₁ N₂ D
    (quadraticGaussLeft a) (quadraticGaussRight b) K₁ K₂ T hT hK₁ hK₂ h₁ h₂ hc₁
  have hb₂ := quadratic_weighted_bilinear_bound f M N₁ N₂ D
    (quadraticThreeClass (quadraticGaussLeft a))
    (quadraticThreeClass (quadraticGaussRight b)) K₁ K₂ T hT hK₁ hK₂ h₁ h₂ hc₂
  calc
    _ ≤ ∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        (‖quadraticLogWeightedDivisor f N₁ N₂ d (quadraticGaussLeft a) (quadraticGaussRight b) m‖ +
        2 * ‖quadraticLogWeightedDivisor f N₁ N₂ d
          (quadraticThreeClass (quadraticGaussLeft a))
          (quadraticThreeClass (quadraticGaussRight b)) m‖) := by
      apply Finset.sum_le_sum
      intro d _
      apply Finset.sum_le_sum
      intro m _
      rw [quadratic_log_weighted_gauss_split]
      exact (norm_sub_le _ _).trans (by norm_num [norm_mul])
    _ = (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
        ‖quadraticLogWeightedDivisor f N₁ N₂ d (quadraticGaussLeft a) (quadraticGaussRight b) m‖) +
        2 * (∑ d ∈ Finset.Ioc D (2 * D), ∑ m ∈ oddSquarefreeRange M,
          ‖quadraticLogWeightedDivisor f N₁ N₂ d
          (quadraticThreeClass (quadraticGaussLeft a))
          (quadraticThreeClass (quadraticGaussRight b)) m‖) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := by nlinarith [hb₁, hb₂]

end Ostmann

end OAI
