import OAI.NumberTheory.Ostmann.Quadratic.QuadraticUnitDivisor
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticWeightedGaussBound

namespace OAI

/-! # The divisor-one boundary in the smooth matrix estimates -/

namespace Ostmann

open MeasureTheory
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem quadratic_unit_weighted_bound (f : 𝓢(ℝ, ℂ)) (M N₁ N₂ : ℕ)
    (v w : ℕ → ℂ) (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M N₁ K₁) (h₂ : QuadraticSieveBound M N₂ K₂) :
    (∑ m ∈ oddSquarefreeRange M, ‖quadraticLogWeightedDivisor f N₁ N₂ 1 v w m‖) ≤
      (∫ u : ℝ, ‖𝓕 f u‖) *
        (Real.sqrt (2 * K₁ * quadraticDivisorMoment N₁ v) *
          Real.sqrt (2 * K₂ * quadraticDivisorMoment N₂ w)) := by
  let G (m : ℕ) (u : ℝ) := ‖𝓕 f u‖ *
    ‖quadraticDivisorBilinear N₁ N₂ 1 (quadraticLogModulate u v) (quadraticLogModulate (-u) w) m‖
  let T := Real.sqrt (2 * K₁ * quadraticDivisorMoment N₁ v) *
    Real.sqrt (2 * K₂ * quadraticDivisorMoment N₂ w)
  have hI (m : ℕ) : Integrable (G m) := by
    simpa only [G, norm_mul] using (quadratic_log_integrand_integrable f N₁ N₂ 1 v w m).norm
  have hsum : Integrable (fun u : ℝ => ∑ m ∈ oddSquarefreeRange M, G m u) :=
    integrable_finsetSum _ (fun m _ => hI m)
  have hb (u : ℝ) : (∑ m ∈ oddSquarefreeRange M, G m u) ≤ ‖𝓕 f u‖ * T := by
    simp only [G, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa only [T, quadraticDivisorMoment_logModulate] using
      quadratic_unit_divisor_bound M N₁ N₂ K₁ K₂ hK₁ hK₂ h₁ h₂
        (quadraticLogModulate u v) (quadraticLogModulate (-u) w)
  calc
    _ ≤ ∑ m ∈ oddSquarefreeRange M, ∫ u : ℝ, G m u :=
      Finset.sum_le_sum (fun m _ => quadratic_log_weighted_norm f N₁ N₂ 1 v w m)
    _ = ∫ u : ℝ, ∑ m ∈ oddSquarefreeRange M, G m u :=
      (integral_finsetSum _ (fun m _ => hI m)).symm
    _ ≤ ∫ u : ℝ, ‖𝓕 f u‖ * T :=
      integral_mono hsum ((𝓕 f : 𝓢(ℝ, ℂ)).integrable.norm.mul_const T) hb
    _ = _ := integral_mul_const T _

theorem quadratic_unit_weighted_gauss_bound (f : 𝓢(ℝ, ℂ)) (M N₁ N₂ : ℕ)
    (v w : ℕ → ℂ) (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M N₁ K₁) (h₂ : QuadraticSieveBound M N₂ K₂) :
    (∑ m ∈ oddSquarefreeRange M, ‖quadraticLogWeightedGaussDivisor f N₁ N₂ 1 v w m‖) ≤
      3 * (∫ u : ℝ, ‖𝓕 f u‖) *
        (Real.sqrt (2 * K₁ * quadraticDivisorMoment N₁ v) *
          Real.sqrt (2 * K₂ * quadraticDivisorMoment N₂ w)) := by
  have hleft := quadratic_unit_weighted_bound f M N₁ N₂
    (quadraticGaussLeft v) (quadraticGaussRight w) K₁ K₂ hK₁ hK₂ h₁ h₂
  simp only [quadraticDivisorMoment_gaussLeft, quadraticDivisorMoment_gaussRight] at hleft
  have hright := quadratic_unit_weighted_bound f M N₁ N₂
    (quadraticThreeClass (quadraticGaussLeft v))
    (quadraticThreeClass (quadraticGaussRight w)) K₁ K₂ hK₁ hK₂ h₁ h₂
  have hright' : (∑ m ∈ oddSquarefreeRange M,
      ‖quadraticLogWeightedDivisor f N₁ N₂ 1
        (quadraticThreeClass (quadraticGaussLeft v))
        (quadraticThreeClass (quadraticGaussRight w)) m‖) ≤
      (∫ u : ℝ, ‖𝓕 f u‖) *
        (Real.sqrt (2 * K₁ * quadraticDivisorMoment N₁ v) *
          Real.sqrt (2 * K₂ * quadraticDivisorMoment N₂ w)) := by
    apply hright.trans
    apply mul_le_mul_of_nonneg_left _ (integral_nonneg fun _ => norm_nonneg _)
    apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [quadraticDivisorMoment_gaussLeft] using
        quadraticDivisorMoment_threeClass N₁ (quadraticGaussLeft v)
    · apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [quadraticDivisorMoment_gaussRight] using
        quadraticDivisorMoment_threeClass N₂ (quadraticGaussRight w)
  calc
    _ ≤ ∑ m ∈ oddSquarefreeRange M,
        (‖quadraticLogWeightedDivisor f N₁ N₂ 1 (quadraticGaussLeft v) (quadraticGaussRight w) m‖ +
        2 * ‖quadraticLogWeightedDivisor f N₁ N₂ 1
          (quadraticThreeClass (quadraticGaussLeft v))
          (quadraticThreeClass (quadraticGaussRight w)) m‖) := by
      apply Finset.sum_le_sum
      intro m _
      rw [quadratic_log_weighted_gauss_split]
      exact (norm_sub_le _ _).trans (by norm_num [norm_mul])
    _ = (∑ m ∈ oddSquarefreeRange M,
        ‖quadraticLogWeightedDivisor f N₁ N₂ 1 (quadraticGaussLeft v) (quadraticGaussRight w) m‖) +
        2 * ∑ m ∈ oddSquarefreeRange M, ‖quadraticLogWeightedDivisor f N₁ N₂ 1
          (quadraticThreeClass (quadraticGaussLeft v))
          (quadraticThreeClass (quadraticGaussRight w)) m‖ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := by nlinarith [hleft, hright']

end Ostmann

end OAI
