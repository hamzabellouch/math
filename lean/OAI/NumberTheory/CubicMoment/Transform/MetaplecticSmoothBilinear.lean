import OAI.NumberTheory.CubicMoment.Transform.MetaplecticSquarefreeBilinear
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTrivialSum

namespace OAI

/-! The cubic-sieve bound applied to the original smooth angular Gauss
sums, with the actual compact support and coefficient energies. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplectic_angular_bilinear_identity (A : Finset Eisenstein)
    (α : Eisenstein → ℂ) (W : Eisenstein → ℝ → ℂ) (ℓ : ℤ)
    {U B : ℝ} (hU : 0 < U) (hcut : ∀ r ∈ A, ∀ x : ℝ, B < x → W r x = 0) :
    (∑ r ∈ A, α r*metaplecticAngularSmoothSum r ℓ (W r) U 0) =
      ∑ r ∈ A, ∑ u ∈ primaryElementBall (B*U),
        (α r*theta ℓ r)*theta ℓ u*gauss (r*u)*W r (norm u/U) := by
  apply Finset.sum_congr rfl
  intro r hr
  rw [metaplecticAngularSmoothSum_finite r ℓ (W r) hU (le_refl (B*U)) (hcut r hr) 0,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [theta_mul]
  simp only [mellinPhase,zero_mul,Complex.ofReal_zero,Complex.exp_zero,mul_one]
  ring

theorem UniformLogWeights.metaplectic_smooth_bilinear
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : Eisenstein → γ) (A : Finset Eisenstein) (N U B : ℝ),
      1 ≤ N → 0 < U → 1 ≤ B*U →
      (∀ r ∈ A, primary r ∧ norm r ≤ N) →
      (∀ r ∈ A, ∀ x : ℝ, B < x → W (w r) x = 0) →
      ∀ (α : Eisenstein → ℂ) (ℓ : ℤ),
      ‖∑ r ∈ A, α r*metaplecticAngularSmoothSum r ℓ (W (w r)) U 0‖^2 ≤
        K*(N*(B*U))^ε*(B*U)*(N+B*U+(N*(B*U))^(2/3:ℝ))*
          (∑ r ∈ A, ‖α r‖^2) := by
  obtain ⟨K,hK,hbound⟩ := hW.metaplectic_unrestricted_bilinear hε
  refine ⟨18*K,by positivity,?_⟩
  intro w A N U B hN hU hBU hA hcut α ℓ
  rw [metaplectic_angular_bilinear_identity A α (fun r => W (w r)) ℓ hU hcut]
  have heα : (∑ r ∈ A, ‖α r*theta ℓ r‖^2) = ∑ r ∈ A, ‖α r‖^2 := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [norm_mul,norm_theta (primary_ne_zero (hA r hr).1),mul_one]
  have heβ : (∑ u ∈ primaryElementBall (B*U), ‖theta ℓ u‖^2) =
      ((primaryElementBall (B*U)).card:ℝ) := by
    calc
      _ = ∑ _u ∈ primaryElementBall (B*U), (1:ℝ) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [norm_theta (primary_ne_zero (mem_primaryElementBall.mp hu).1),one_pow]
      _ = _ := by simp
  have hb := hbound w A (primaryElementBall (B*U)) N (B*U) U hN hBU hU hA
    (fun u hu => mem_primaryElementBall.mp hu) (fun r => α r*theta ℓ r) (theta ℓ)
  rw [heα,heβ] at hb
  apply hb.trans
  calc
    _ ≤ K*(N*(B*U))^ε*(N+B*U+(N*(B*U))^(2/3:ℝ))*
        (∑ r ∈ A, ‖α r‖^2)*(18*(B*U)) := by
      apply mul_le_mul_of_nonneg_left
        (primaryElementBall_card_le (zero_lt_one.trans_le hBU).le)
      positivity
    _ = _ := by ring

lemma metaplecticAngularSmoothSum_small (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U B : ℝ} (hU : 0 < U) (hBU : B*U < 1)
    (hcut : ∀ x : ℝ, B < x → W x = 0) :
    metaplecticAngularSmoothSum r ℓ W U 0 = 0 := by
  rw [metaplecticAngularSmoothSum_finite r ℓ W hU (le_refl (B*U)) hcut 0]
  apply Finset.sum_eq_zero
  intro u hu
  have hn := one_le_norm (primary_ne_zero (mem_primaryElementBall.mp hu).1)
  exact False.elim ((not_lt_of_ge hn) ((mem_primaryElementBall.mp hu).2.trans_lt hBU))

theorem UniformLogWeights.metaplectic_smooth_bilinear_all_lengths
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : Eisenstein → γ) (A : Finset Eisenstein) (N U B : ℝ),
      1 ≤ N → 0 < U → 0 ≤ B →
      (∀ r ∈ A, primary r ∧ norm r ≤ N) →
      (∀ r ∈ A, ∀ x : ℝ, B < x → W (w r) x = 0) →
      ∀ (α : Eisenstein → ℂ) (ℓ : ℤ),
      ‖∑ r ∈ A, α r*metaplecticAngularSmoothSum r ℓ (W (w r)) U 0‖^2 ≤
        K*(N*(B*U))^ε*(B*U)*(N+B*U+(N*(B*U))^(2/3:ℝ))*
          (∑ r ∈ A, ‖α r‖^2) := by
  obtain ⟨K,hK,hbound⟩ := hW.metaplectic_smooth_bilinear hε
  refine ⟨K,hK,?_⟩
  intro w A N U B hN hU hB hA hcut α ℓ
  by_cases hBU : 1 ≤ B*U
  · exact hbound w A N U B hN hU hBU hA hcut α ℓ
  · have hz : (∑ r ∈ A, α r*metaplecticAngularSmoothSum r ℓ (W (w r)) U 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      rw [metaplecticAngularSmoothSum_small r ℓ (W (w r)) hU (lt_of_not_ge hBU) (hcut r hr),mul_zero]
    rw [hz,norm_zero,zero_pow (by decide : 2 ≠ 0)]
    positivity

end CubicFirstMoment

end

end OAI
