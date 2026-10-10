import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTailCoefficient
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticActualInverse

namespace OAI

/-! The long completion coefficient separates exactly into one fixed
factor and a coprimality restriction on the original outer coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticTailScalar (ℓ : ℤ) (C F : ℝ) (e : Eisenstein) : ℂ :=
  (Real.sqrt (norm e):ℂ)*theta (3*ℓ) e*metaplecticTailMoebius C F e

def metaplecticTailOuter (e : Eisenstein) (α : Eisenstein → ℂ) (r : Eisenstein) : ℂ :=
  if IsCoprime e r then α r else 0

lemma metaplectic_tail_level_factor (A : Finset Eisenstein) (α : Eisenstein → ℂ)
    (ℓ : ℤ) (C F : ℝ) (e : Eisenstein) (f : Eisenstein → ℂ) :
    (∑ r ∈ A, α r*metaplecticTailCoefficient r ℓ C F e*f r) =
      metaplecticTailScalar ℓ C F e*(∑ r ∈ A, metaplecticTailOuter e α r*f r) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [metaplecticTailCoefficient_factor]
  unfold metaplecticTailScalar metaplecticTailOuter metaplecticCompletionWeight
  by_cases hc : IsCoprime e r
  · simp only [hc,ite_true,mul_zero,Complex.ofReal_zero,zero_mul,Complex.cpow_zero,mul_one]
    ring
  · simp only [hc,ite_false,zero_mul,mul_zero]

lemma metaplecticTailOuter_energy_le (A : Finset Eisenstein) (e : Eisenstein)
    (α : Eisenstein → ℂ) :
    (∑ r ∈ A, ‖metaplecticTailOuter e α r‖^2) ≤ ∑ r ∈ A, ‖α r‖^2 := by
  apply Finset.sum_le_sum
  intro r _
  unfold metaplecticTailOuter
  split_ifs
  · exact le_rfl
  · simp only [norm_zero,zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _

theorem metaplecticTailScalar_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (ℓ : ℤ) (C F : ℝ) (e : Eisenstein), primary e →
      ‖metaplecticTailScalar ℓ C F e‖ ≤ D*norm e^(1/2+δ) := by
  obtain ⟨D,hD,hbound⟩ := metaplecticTailMoebius_bound hδ
  refine ⟨D,hD,?_⟩
  intro ℓ C F e he
  rw [metaplecticTailScalar,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),norm_theta (primary_ne_zero he),mul_one]
  calc
    _ ≤ Real.sqrt (norm e)*(D*norm e^δ) :=
      mul_le_mul_of_nonneg_left (hbound C F e he) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_eq_rpow,Real.rpow_add (norm_pos_of_ne_zero (primary_ne_zero he))]
      ring

end CubicFirstMoment

end

end OAI
