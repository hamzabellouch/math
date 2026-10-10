import OAI.NumberTheory.CubicMoment.Transform.MetaplecticActualInverse

namespace OAI

/-! Exact forward completion over a finite primary box. This identity
allows the long inverse divisors to be collected by their actual product. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_forward_completion (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) :
    metaplecticCompleted r ℓ W U =
      ∑ d ∈ primaryElementBall F, metaplecticCompletionWeight r ℓ 0 d*
        metaplecticAngularSmoothSum r ℓ W (U/norm d^3) 0 := by
  rw [←metaplecticHeightCompleted_zero r ℓ W U,
    metaplecticHeightCompleted_box r ℓ W hU hBF hW 0]
  apply Finset.sum_congr rfl
  intro d hd
  have hdp := (mem_primaryElementBall.mp hd).1
  have hNd : 0 < norm d := norm_pos_of_ne_zero (primary_ne_zero hdp)
  have hV : 0 < U/norm d^3 := div_pos hU (pow_pos hNd 3)
  have hVU : U/norm d^3 ≤ U := div_le_self hU.le
    (one_le_pow₀ (one_le_norm (primary_ne_zero hdp)))
  have hBV : B*(U/norm d^3) ≤ F := (mul_le_mul_of_nonneg_left hVU hB).trans hBF
  rw [metaplecticAngularSmoothSum_finite r ℓ W hV hBV hW 0,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hup := (mem_primaryElementBall.mp hu).1
  have hf := metaplectic_completion_factor r ℓ 0 hdp hup
  have hw := metaplectic_primal_weight_factor r ℓ W U 0 d u
  simp only [mellinPhase,zero_mul,Complex.ofReal_zero,Complex.exp_zero,mul_one] at hf hw ⊢
  have hn : norm (d^3*u)/U = norm u/(U/norm d^3) := by
    rw [norm_mul_eq,eisenstein_norm_pow]
    field_simp
  rw [hn,←hf] at hw
  rw [←hw]
  ring

end CubicFirstMoment

end

end OAI
