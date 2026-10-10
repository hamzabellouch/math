import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMetricPairing
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.NormDet

namespace OAI

/-! The actual Mobius Jacobian has absolute determinant equal to the cube
of the height ratio. Thus the hyperbolic volume density is invariant. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

private abbrev TangentL2 := WithLp 2 (ℂ × ℝ)
private def tangentCoordinates : TangentL2 ≃ₗ[ℝ] ℂ × ℝ := WithLp.linearEquiv 2 ℝ (ℂ × ℝ)

private lemma tangent_norm_sq (u : TangentL2) : ‖u‖^2=cubicThetaRadius (tangentCoordinates u) := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [cubicThetaRadius,tangentCoordinates,WithLp.coe_linearEquiv,Complex.normSq_eq_norm_sq,
    Real.norm_eq_abs,sq_abs]
  rfl

private lemma tangent_finrank : Module.finrank ℝ TangentL2=3 := by
  rw [tangentCoordinates.finrank_eq,Module.finrank_prod,Complex.finrank_real_complex,
    Module.finrank_self]

lemma cubicThetaMobius_abs_det (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2) :
    |(fderiv ℝ (cubicThetaMobius g) p).toLinearMap.det|=
      ((cubicThetaMobius g p).2/p.2)^3 := by
  let L := (fderiv ℝ (cubicThetaMobius g) p).toLinearMap
  let A : TangentL2 →ₗ[ℝ] TangentL2 :=
    tangentCoordinates.symm.toLinearMap.comp (L.comp tangentCoordinates.toLinearMap)
  let k := (cubicThetaMobius g p).2/p.2
  have hk : 0<k := div_pos (cubicThetaMobius_height_pos g hp) hp
  have hnorm (u : TangentL2) : ‖A u‖=k*‖u‖ := by
    have hs := cubicThetaMobius_derivative_scale g hp (tangentCoordinates u)
    have hA : cubicThetaRadius (fderiv ℝ (cubicThetaMobius g) p (tangentCoordinates u))=‖A u‖^2 := by
      rw [tangent_norm_sq]
      simp only [A,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,L]
      rfl
    rw [hA,← tangent_norm_sq] at hs
    have he : (‖A u‖*p.2)^2=(‖u‖*(cubicThetaMobius g p).2)^2 := by nlinarith [hs]
    have he' := (sq_eq_sq₀ (mul_nonneg (_root_.norm_nonneg (A u)) hp.le)
      (mul_nonneg (_root_.norm_nonneg u) (cubicThetaMobius_height_pos g hp).le)).mp he
    calc
      ‖A u‖=(‖u‖*(cubicThetaMobius g p).2)/p.2 := (eq_div_iff hp.ne').mpr he'
      _ = k*‖u‖ := by dsimp [k]; ring
  let J : TangentL2 →ₗᵢ[ℝ] TangentL2 :=
    { toLinearMap := k⁻¹ • A
      norm_map' := by
        intro u
        change ‖k⁻¹ • A u‖=‖u‖
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hk),hnorm]
        field_simp }
  have hJ := J.normDet_eq_one
  change (k⁻¹ • A).normDet=1 at hJ
  rw [LinearMap.normDet_smul,tangent_finrank,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hk)] at hJ
  have hA : A.normDet=k^3 := by
    calc
      A.normDet=(k^3*(k⁻¹)^3)*A.normDet := by field_simp
      _ = k^3 := by rw [mul_assoc,hJ,mul_one]
  rw [LinearMap.normDet_eq_abs_det] at hA
  have hdet : A.det=L.det := LinearMap.det_conj L tangentCoordinates.symm
  rw [hdet] at hA
  exact hA

lemma cubicThetaMobius_volume_density (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2) :
    |(fderiv ℝ (cubicThetaMobius g) p).toLinearMap.det|/
      (cubicThetaMobius g p).2^3=1/p.2^3 := by
  rw [cubicThetaMobius_abs_det g hp]
  field_simp [(cubicThetaMobius_height_pos g hp).ne',hp.ne']

end CubicFirstMoment

end

end OAI
