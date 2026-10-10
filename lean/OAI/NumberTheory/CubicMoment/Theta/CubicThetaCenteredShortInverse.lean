import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompletedLow
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticShortInverse
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCenteredLow

namespace OAI

/-! Actual centered short inverse-completion bound, including the radial mode. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem UniformLogWeights.cubicTheta_centered_short_completion_error
    {ι : Type*} {W : ι → ℝ → ℂ} (hW : UniformLogWeights W) (ℓ : ℤ)
    {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, primary r → Squarefree r →
      ∀ Y U C : ℝ, 1 ≤ Y → Y^(-B) ≤ U → U ≤ Y^B →
      0 ≤ C → C ≤ Y^B → norm r ≤ Y^B →
      ‖metaplecticShortCompletionError r ℓ (W i) U C‖ ≤
        K*Y^ε*Real.sqrt (norm r)*C^(3/2:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := uniform_cubicTheta_centered_subpower hW ℓ hε
    (show 0 ≤ 4*B by positivity)
  refine ⟨18*K,by positivity,?_⟩
  intro i r hr hsr Y U C hY hUlo hUhi hC hChi hrhi
  have hrbig : norm r ≤ Y^(4*B) := hrhi.trans
    (Real.rpow_le_rpow_of_exponent_le hY (by linarith))
  have hc (c : Eisenstein) (hc : c ∈ primaryElementBall C) :
      ‖((idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ 0 c)*
        (metaplecticCompleted r ℓ (W i) (U/norm c^3)-
          metaplecticMain r ℓ (W i) (U/norm c^3))‖ ≤
          Real.sqrt (norm c)*(K*Y^ε*Real.sqrt (norm r)) := by
    obtain ⟨hcp,hcn⟩ := mem_primaryElementBall.mp hc
    obtain ⟨hpos,hlo,_⟩ := metaplectic_inverse_length_range hY hB hUlo hUhi
      (one_le_norm (primary_ne_zero hcp)) (hcn.trans hChi)
    rw [norm_mul]
    exact mul_le_mul (norm_metaplectic_inverse_weight r ℓ 0 hcp)
      (hbound i r hr hsr Y _ hY hpos hrbig hlo) (_root_.norm_nonneg _) (Real.sqrt_nonneg _)
  unfold metaplecticShortCompletionError
  calc
    _ ≤ ∑ c ∈ primaryElementBall C,
        Real.sqrt (norm c)*(K*Y^ε*Real.sqrt (norm r)) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hc)
    _ = (∑ c ∈ primaryElementBall C, Real.sqrt (norm c))*(K*Y^ε*Real.sqrt (norm r)) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (18*C^(3/2:ℝ))*(K*Y^ε*Real.sqrt (norm r)) :=
      mul_le_mul_of_nonneg_right (primary_sqrt_norm_mass hC) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
