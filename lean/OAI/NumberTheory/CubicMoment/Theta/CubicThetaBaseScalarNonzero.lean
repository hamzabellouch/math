import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticModelSection

namespace OAI

/-! The actual common nonconstant coefficient is nonzero. Otherwise
global automorphy would force a pure height power to be invariant. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

theorem cubicThetaArithmeticBaseScalar_ne_zero : cubicThetaArithmeticBaseScalar≠0 := by
  intro hB
  let p : CubicThetaPoint := ⟨(0,1),by norm_num⟩
  let g₀ : SL(2,Eisenstein) := ⟨!![1,0;3,1],by simp [Matrix.det_fin_two]⟩
  have hg : g₀∈cubicThetaPrincipalGroup :=
    (cubicThetaPrincipalGroup_mem_iff g₀).mpr
      ⟨primary_one,dvd_zero _,dvd_refl _,primary_one⟩
  let g : cubicThetaPrincipalGroup := ⟨g₀,hg⟩
  have hp : (g • p).val.2=(1/10:ℝ) := by
    change (cubicThetaMobius (cubicThetaPrincipalComplex g) (0,1)).2=(1/10:ℝ)
    norm_num [cubicThetaMobius,cubicThetaMobiusDenominator,
      cubicThetaPrincipalComplex_apply,g,g₀]
    change (1+Complex.normSq (3:ℂ))⁻¹=(1/10:ℝ)
    norm_num [Complex.normSq_apply]
  have hC : 0<cubicThetaConstant := by unfold cubicThetaConstant; positivity
  have hnorm (q : CubicThetaPoint) :
      ‖cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar q.val‖=
        cubicThetaConstant*q.val.2^(2/3:ℝ) := by
    rw [cubicThetaArithmeticModel,hB,zero_mul,add_zero,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (mul_pos hC (Real.rpow_pos_of_pos q.property _))]
  have he := congrArg (fun z : ℂ => ‖z‖) (cubicThetaArithmeticModel_automorphy g p)
  rw [norm_mul,cubicThetaKubotaValue_norm,one_mul,hnorm,hnorm,hp] at he
  change cubicThetaConstant*(1/10:ℝ)^(2/3:ℝ)=cubicThetaConstant*1^(2/3:ℝ) at he
  have hlt : (1/10:ℝ)^(2/3:ℝ)<1 := by
    simpa using Real.rpow_lt_rpow (by norm_num : (0:ℝ)≤1/10)
      (by norm_num : (1/10:ℝ)<1) (by norm_num : (0:ℝ)<2/3)
  rw [Real.one_rpow] at he
  have he' := (mul_left_cancel₀ hC.ne' he)
  exact (ne_of_lt hlt) he'

end CubicFirstMoment

end

end OAI
