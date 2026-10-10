import OAI.NumberTheory.CubicMoment.Transform.MetaplecticSmoothBilinear
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTailLevel

namespace OAI

/-! The cubic-sieve estimate for the literal fixed-e long completion
term, including its coprimality restriction and every angular phase. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem UniformLogWeights.metaplectic_tail_level_sieve
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : Eisenstein → γ) (A : Finset Eisenstein) (N U B C F : ℝ),
      1 ≤ N → 0 < U → 0 ≤ B →
      (∀ r ∈ A, primary r ∧ norm r ≤ N) →
      (∀ r ∈ A, ∀ x : ℝ, B < x → W (w r) x = 0) →
      ∀ (α : Eisenstein → ℂ) (ℓ : ℤ) (e : Eisenstein), primary e →
      ‖∑ r ∈ A, α r*metaplecticTailCoefficient r ℓ C F e*
        metaplecticAngularSmoothSum r ℓ (W (w r)) (U/norm e^3) 0‖^2 ≤
        K*norm e^(1+2*ε)*(N*(B*(U/norm e^3)))^ε*(B*(U/norm e^3))*
          (N+B*(U/norm e^3)+(N*(B*(U/norm e^3)))^(2/3:ℝ))*
          (∑ r ∈ A, ‖α r‖^2) := by
  obtain ⟨K,hK,hbound⟩ := hW.metaplectic_smooth_bilinear_all_lengths hε
  obtain ⟨D,hD,hscalar⟩ := metaplecticTailScalar_bound hε
  refine ⟨D^2*K,by positivity,?_⟩
  intro w A N U B C F hN hU hB hA hcut α ℓ e he
  have hn : 0 < norm e := norm_pos_of_ne_zero (primary_ne_zero he)
  let V := U/norm e^3
  have hV : 0 < V := div_pos hU (pow_pos hn 3)
  have hs := hbound w A N V B hN hV hB hA hcut (metaplecticTailOuter e α) ℓ
  have hs' : ‖∑ r ∈ A, metaplecticTailOuter e α r*
      metaplecticAngularSmoothSum r ℓ (W (w r)) V 0‖^2 ≤
      K*(N*(B*V))^ε*(B*V)*(N+B*V+(N*(B*V))^(2/3:ℝ))*(∑ r ∈ A, ‖α r‖^2) :=
    hs.trans (mul_le_mul_of_nonneg_left (metaplecticTailOuter_energy_le A e α) (by positivity))
  rw [metaplectic_tail_level_factor A α ℓ C F e
    (fun r => metaplecticAngularSmoothSum r ℓ (W (w r)) (U/norm e^3) 0),norm_mul,mul_pow]
  calc
    _ ≤ (D*norm e^(1/2+ε))^2*
        (K*(N*(B*V))^ε*(B*V)*(N+B*V+(N*(B*V))^(2/3:ℝ))*(∑ r ∈ A, ‖α r‖^2)) :=
      mul_le_mul (pow_le_pow_left₀ (_root_.norm_nonneg _) (hscalar ℓ C F e he) 2) hs'
        (sq_nonneg _) (sq_nonneg _)
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast hn.le]
      norm_num only [Nat.cast_ofNat]
      rw [show (1/2+ε)*(2:ℝ) = 1+2*ε by ring]
      dsimp [V]
      ring

end CubicFirstMoment

end

end OAI
