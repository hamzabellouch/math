import OAI.NumberTheory.CubicMoment.Transform.MetaplecticForwardCompletion
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTailCoefficient

namespace OAI

/-! The actual long inverse-completion sum, collected by e=cd.
The resulting weight is the proved tail coefficient, not an arbitrary
divisor-bounded replacement. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticLongCompletion (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (U C F : ℝ) : ℂ :=
  ∑ c ∈ primaryElementBall F, if C < norm c then
    ((idealMoebius c:ℂ)*metaplecticCompletionWeight r ℓ 0 c)*
      metaplecticCompleted r ℓ W (U/norm c^3) else 0

theorem metaplectic_long_completion_collect (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {U B F : ℝ} (hU : 0 < U) (hB : 0 ≤ B) (hBF : B*U ≤ F)
    (hW : ∀ x : ℝ, B < x → W x = 0) (C : ℝ) :
    metaplecticLongCompletion r ℓ W U C F =
      ∑ e ∈ ((primaryElementBall F).product (primaryElementBall F)).image
        (fun cd => cd.1*cd.2), metaplecticTailCoefficient r ℓ C F e*
          metaplecticAngularSmoothSum r ℓ W (U/norm e^3) 0 := by
  rw [←metaplecticTailCoefficient_collect]
  unfold metaplecticLongCompletion
  apply Finset.sum_congr rfl
  intro c hc
  have hcp := (mem_primaryElementBall.mp hc).1
  have hNc := norm_pos_of_ne_zero (primary_ne_zero hcp)
  have hV : 0 < U/norm c^3 := div_pos hU (pow_pos hNc 3)
  have hVU : U/norm c^3 ≤ U := div_le_self hU.le
    (one_le_pow₀ (one_le_norm (primary_ne_zero hcp)))
  have hBV : B*(U/norm c^3) ≤ F := (mul_le_mul_of_nonneg_left hVU hB).trans hBF
  by_cases hC : C < norm c
  · rw [ite_eq_left hC,metaplectic_forward_completion r ℓ W hV hB hBV hW,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [ite_eq_left hC]
    have he : U/norm c^3/norm d^3 = U/norm (c*d)^3 := by
      rw [norm_mul_eq,mul_pow]
      field_simp
    rw [he]
    ring
  · simp only [hC,ite_false,zero_mul,Finset.sum_const_zero]

end CubicFirstMoment

end

end OAI
