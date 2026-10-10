import OAI.NumberTheory.CubicMoment.Transform.MetaplecticInverseSplit
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRadialDensity
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRadialEulerTail

namespace OAI

/-! The short inverse residue is exactly the same finite Möbius density
as the radial squarefree lattice main term. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_inverse_residue_scale {U N : ℝ} (hU : 0 < U) (hN : 0 < N) :
    Real.sqrt N*(U/N^3)^(5/6:ℝ) = U^(5/6:ℝ)*N^(-2:ℝ) := by
  rw [Real.sqrt_eq_rpow,Real.div_rpow hU.le (pow_nonneg hN.le _),
    ←Real.rpow_natCast N 3,←Real.rpow_mul hN.le]
  have he : ((3:ℕ):ℝ)*(5/6) = 5/2 := by norm_num
  rw [he]
  calc
    _ = U^(5/6:ℝ)*(N^(1/2:ℝ)/N^(5/2:ℝ)) := by ring
    _ = _ := by rw [←Real.rpow_sub hN]; norm_num

lemma metaplectic_short_residue_eq (r : Eisenstein) (W : ℝ → ℂ)
    {U : ℝ} (hU : 0 < U) (C : ℝ) :
    (∑ c ∈ primaryElementBall C,
      ((idealMoebius c:ℂ)*metaplecticCompletionWeight r 0 0 c)*
        metaplecticMain r 0 W (U/norm c^3)) =
      (((metaplecticA0*U^(5/6:ℝ)*metaplecticTotient r*norm r^(-7/6:ℝ):ℝ):ℂ)*
        mellin W (5/6))*metaplecticRadialEulerPartial r C := by
  rw [metaplecticRadialEulerPartial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  have hNc := norm_pos_of_ne_zero (primary_ne_zero (mem_primaryElementBall.mp hc).1)
  have hcop : IsCoprime c r ↔ IsCoprime r c := isCoprime_comm
  by_cases hrc : IsCoprime r c
  · simp only [metaplecticCompletionWeight,hcop,hrc,ite_true,mul_zero,
      Complex.ofReal_zero,zero_mul,Complex.cpow_zero,theta,zpow_zero,mul_one,
      metaplecticMain,ite_true]
    have hs := metaplectic_inverse_residue_scale hU hNc
    push_cast
    calc
      _ = (idealMoebius c:ℂ)*((Real.sqrt (norm c)*(U/norm c^3)^(5/6:ℝ):ℝ):ℂ)*
          ((metaplecticA0*metaplecticTotient r*norm r^(-7/6:ℝ):ℝ):ℂ)*mellin W (5/6) := by
            push_cast
            ring
      _ = _ := by rw [hs]; push_cast; ring
  · simp [metaplecticCompletionWeight,hcop,hrc]

end CubicFirstMoment

end

end OAI
