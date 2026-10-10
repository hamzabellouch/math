import OAI.NumberTheory.CubicMoment.Transform.MetaplecticSquarefreeRadial
import OAI.NumberTheory.CubicMoment.Estimates.CubeRieszMellin
import OAI.NumberTheory.CubicMoment.Angular.AngularPowerWeights

namespace OAI

/-! The literal squarefree mass occurring in the corrected model,
written in the radial lattice normalization. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def squarefreeModelMass (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑' a : Eisenstein, if primary a then (idealMoebius a:ℂ)^2*
    W (norm a/A)*((norm a^(-1/3:ℝ):ℝ):ℂ) else 0

lemma squarefreeModelMass_eq_radial {A : ℝ} (hA : 0 < A) (W : ℝ → ℂ) :
    squarefreeModelMass W A = ((A^(-1/3:ℝ):ℝ):ℂ)*
      squarefreeCoprimeAngularLattice 1 0 (fun x => ((x^(-1/3:ℝ):ℝ):ℂ)*W x) A := by
  rw [squarefreeModelMass,squarefreeCoprimeAngularLattice,←tsum_mul_left]
  apply tsum_congr
  intro a
  by_cases ha : primary a
  · have hp : norm a^(-1/3:ℝ) = A^(-1/3:ℝ)*(norm a/A)^(-1/3:ℝ) := by
      rw [←Real.mul_rpow hA.le (div_nonneg (norm_nonneg a) hA.le),
        mul_div_cancel₀ _ hA.ne']
    simp only [ha,isCoprime_one_left,and_self,ite_true,theta_zero,hp]
    push_cast
    ring
  · simp only [ha,false_and,ite_false,mul_zero]

lemma squarefreeRadialMain_one_scaled (W : ℝ → ℂ) {A : ℝ} (hA : 0 < A) (B : ℝ) :
    ((A^(-1/3:ℝ):ℝ):ℂ)*
      squarefreeCoprimeRadialMain 1 (fun x => ((x^(-1/3:ℝ):ℝ):ℂ)*W x) A B =
    ((A^(2/3:ℝ)*(2*Real.pi/(9*Real.sqrt 3)):ℝ):ℂ)*mellin W (2/3)*
      metaplecticRadialEulerPartial 1 (Real.sqrt (B*A)) := by
  have hφ : metaplecticTotient 1 = 1 := by
    simpa using metaplecticTotient_prod (∅ : Finset Eisenstein) (by simp)
  have hp : A^(-1/3:ℝ)*A = A^(2/3:ℝ) := by
    calc
      _ = A^(-1/3:ℝ)*A^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hA]; norm_num
  rw [squarefreeCoprimeRadialMain_eq primary_one squarefree_one,
    integral_radial_third_weight,hφ,norm_one_eq]
  simp only [div_one,mul_one]
  push_cast
  calc
    _ = ((A^(-1/3:ℝ)*A:ℝ):ℂ)*(2*Real.pi/(9*Real.sqrt 3))*mellin W (2/3)*
        metaplecticRadialEulerPartial 1 (Real.sqrt (B*A)) := by push_cast; ring
    _ = _ := by rw [hp]

theorem UniformLogWeights.squarefreeModelMass_finite_error
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 < K ∧ ∀ i A, 0 < A →
      ‖squarefreeModelMass (W i) A-
        ((A^(2/3:ℝ)*(2*Real.pi/(9*Real.sqrt 3)):ℝ):ℂ)*mellin (W i) (2/3)*
          metaplecticRadialEulerPartial 1
            (Real.sqrt (Real.exp (h.realPower (-1/3)).radius*A))‖ ≤ K*A^(1/6:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := (h.realPower (-1/3)).squarefreeCoprimeRadialLattice_centered
    (show (0:ℝ) < 1 by norm_num)
  refine ⟨K,hK,?_⟩
  intro i A hA
  rw [squarefreeModelMass_eq_radial hA,
    ←squarefreeRadialMain_one_scaled (W i) hA,←mul_sub,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hA _)]
  calc
    _ ≤ A^(-1/3:ℝ)*(K*norm (1:Eisenstein)^(1:ℝ)*Real.sqrt A) :=
      mul_le_mul_of_nonneg_left (hbound i 1 primary_one squarefree_one A hA)
        (Real.rpow_nonneg hA.le _)
    _ = K*A^(1/6:ℝ) := by
      rw [norm_one_eq,Real.one_rpow,mul_one,Real.sqrt_eq_rpow]
      calc
        _ = K*(A^(-1/3:ℝ)*A^(1/2:ℝ)) := by ring
        _ = _ := by rw [←Real.rpow_add hA]; norm_num

end CubicFirstMoment

end

end OAI
