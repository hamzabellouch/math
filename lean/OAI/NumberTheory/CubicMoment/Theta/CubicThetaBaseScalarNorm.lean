import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRankinRadialMass

namespace OAI

/-! The actual global norm and the arithmetic coefficient pole determine
precisely the magnitude of the Fourier normalization. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaConstant_square : cubicThetaConstant^2=243/4 := by
  rw [cubicThetaConstant,div_pow,←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
  norm_num

theorem cubicThetaArithmeticBaseScalar_norm_sq : ‖cubicThetaArithmeticBaseScalar‖^2=1 := by
  have hmath := cubicThetaRankinRadialEnergy_residue.const_mul ((9*Real.sqrt 3/2:ℝ):ℂ)
  have hsecond : Tendsto (fun σ : ℝ => (σ:ℂ)*cubicThetaArithmeticRankinMass σ)
      (𝓝[>] 0) (𝓝 (((9*Real.sqrt 3/2:ℝ):ℂ)*
        ((‖cubicThetaArithmeticBaseScalar‖^2:ℝ)*(243/8:ℂ)))) := by
    apply hmath.congr'
    filter_upwards [cubicThetaArithmeticRankinMass_unfold] with σ hσ
    rw [hσ.2,cubicThetaScalarEnergySeed_radial hσ.1]
    ring
  have he := tendsto_nhds_unique cubicThetaArithmeticRankinMass_residue hsecond
  have hr : (9*Real.sqrt 3/4)*cubicThetaConstant^2=
      (9*Real.sqrt 3/2)*(‖cubicThetaArithmeticBaseScalar‖^2*(243/8)) := by
    apply Complex.ofReal_injective
    push_cast at he ⊢
    exact he
  rw [cubicThetaConstant_square] at hr
  have h3 : 0<Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hz : Real.sqrt 3*(‖cubicThetaArithmeticBaseScalar‖^2-1)=0 := by nlinarith [hr]
  have h := (mul_eq_zero.mp hz).resolve_left h3.ne'
  linarith

theorem cubicThetaArithmeticBaseScalar_norm : ‖cubicThetaArithmeticBaseScalar‖=1 := by
  have h := cubicThetaArithmeticBaseScalar_norm_sq
  have hn := _root_.norm_nonneg cubicThetaArithmeticBaseScalar
  nlinarith

end CubicFirstMoment

end

end OAI
