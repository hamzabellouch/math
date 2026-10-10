import OAI.NumberTheory.CubicMoment.Theta.CubicThetaJacobian

namespace OAI

/-! The normalized differential of an actual Mobius transformation is
an orthogonal automorphism of the three-dimensional real tangent space. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

abbrev CubicThetaTangent := WithLp 2 (ℂ × ℝ)

def cubicThetaTangentCoordinates : CubicThetaTangent ≃L[ℝ] ℂ × ℝ :=
  (WithLp.linearEquiv 2 ℝ (ℂ × ℝ)).toContinuousLinearEquiv

lemma cubicThetaTangent_norm_sq (u : CubicThetaTangent) :
    ‖u‖^2=cubicThetaRadius (cubicThetaTangentCoordinates u) := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [cubicThetaRadius,cubicThetaTangentCoordinates,
    Complex.normSq_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  rfl

def cubicThetaTangentDerivative (g : SL(2,ℂ)) (p : ℂ × ℝ) :
    CubicThetaTangent →L[ℝ] CubicThetaTangent :=
  cubicThetaTangentCoordinates.symm.toContinuousLinearMap.comp
    ((fderiv ℝ (cubicThetaMobius g) p).comp
      cubicThetaTangentCoordinates.toContinuousLinearMap)

lemma cubicThetaTangentDerivative_norm (g : SL(2,ℂ)) {p : ℂ × ℝ}
    (hp : 0<p.2) (u : CubicThetaTangent) :
    ‖cubicThetaTangentDerivative g p u‖=
      ((cubicThetaMobius g p).2/p.2)*‖u‖ := by
  have hs := cubicThetaMobius_derivative_scale g hp (cubicThetaTangentCoordinates u)
  have hA : cubicThetaRadius (fderiv ℝ (cubicThetaMobius g) p
      (cubicThetaTangentCoordinates u))=‖cubicThetaTangentDerivative g p u‖^2 := by
    rw [cubicThetaTangent_norm_sq]
    simp only [cubicThetaTangentDerivative,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply]
  rw [hA,← cubicThetaTangent_norm_sq] at hs
  have he : (‖cubicThetaTangentDerivative g p u‖*p.2)^2=
      (‖u‖*(cubicThetaMobius g p).2)^2 := by nlinarith [hs]
  have he' := (sq_eq_sq₀
    (mul_nonneg (_root_.norm_nonneg _) hp.le)
    (mul_nonneg (_root_.norm_nonneg _) (cubicThetaMobius_height_pos g hp).le)).mp he
  calc
    _ = (‖u‖*(cubicThetaMobius g p).2)/p.2 := (eq_div_iff hp.ne').mpr he'
    _ = _ := by ring

def cubicThetaTangentIsometry (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2) :
    CubicThetaTangent ≃ₗᵢ[ℝ] CubicThetaTangent := by
  let k := (cubicThetaMobius g p).2/p.2
  have hk : 0<k := div_pos (cubicThetaMobius_height_pos g hp) hp
  let J : CubicThetaTangent →ₗᵢ[ℝ] CubicThetaTangent :=
    { toLinearMap := k⁻¹ • (cubicThetaTangentDerivative g p).toLinearMap
      norm_map' := by
        intro u
        change ‖k⁻¹ • cubicThetaTangentDerivative g p u‖=‖u‖
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hk),
          cubicThetaTangentDerivative_norm g hp]
        change k⁻¹*(k*‖u‖)=‖u‖
        rw [← mul_assoc,inv_mul_cancel₀ hk.ne',one_mul] }
  exact LinearIsometryEquiv.ofSurjective J
    (LinearMap.surjective_of_injective J.injective)

lemma cubicThetaTangentDerivative_eq (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2)
    (u : CubicThetaTangent) :
    cubicThetaTangentDerivative g p u=
      ((cubicThetaMobius g p).2/p.2) • cubicThetaTangentIsometry g hp u := by
  change _= ((cubicThetaMobius g p).2/p.2) •
    (((cubicThetaMobius g p).2/p.2)⁻¹ • cubicThetaTangentDerivative g p u)
  rw [smul_smul,mul_inv_cancel₀
    (div_pos (cubicThetaMobius_height_pos g hp) hp).ne',one_smul]

end CubicFirstMoment

end

end OAI
