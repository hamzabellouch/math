import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateSectionNorm
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticCuspEnergy

namespace OAI

/-! Uniform C1 control on one compact positive-height chart controls
the exact norm of the periodized value-gradient data. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaCoordinateEnergy_density_bound {g : ℂ × ℝ → ℂ} {ε : ℝ}
    (_hε : 0≤ε) (hv : ∀ y, ‖g y‖≤ε) (hd : ∀ y, ‖fderiv ℝ g y‖≤ε)
    {y : ℂ × ℝ} (hy : 0<y.2) :
    (‖g y‖^2+y.2^2*cubicThetaFunctionEnergy g y)/y.2^3≤
      ((y.2^3)⁻¹+(Module.finrank ℝ CubicThetaTangent:ℝ)/y.2)*ε^2 := by
  have hv2 : ‖g y‖^2≤ε^2 := pow_le_pow_left₀ (_root_.norm_nonneg _) (hv y) 2
  have hd2 : ‖fderiv ℝ g y‖^2≤ε^2 := pow_le_pow_left₀ (_root_.norm_nonneg _) (hd y) 2
  have he : cubicThetaFunctionEnergy g y≤(Module.finrank ℝ CubicThetaTangent:ℝ)*ε^2 :=
    (cubicThetaTangentEnergy_coordinate_bound (fderiv ℝ g y)).trans
      (mul_le_mul_of_nonneg_left hd2 (Nat.cast_nonneg _))
  calc
    _ = ‖g y‖^2/y.2^3+cubicThetaFunctionEnergy g y/y.2 := by field_simp [hy.ne']
    _ ≤ ε^2/y.2^3+((Module.finrank ℝ CubicThetaTangent:ℝ)*ε^2)/y.2 :=
      add_le_add (div_le_div_of_nonneg_right hv2 (pow_nonneg hy.le 3))
        (div_le_div_of_nonneg_right he hy.le)
    _ = _ := by ring

lemma cubicThetaCoordinateEnergy_integral_bound {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : K⊆{y : ℂ × ℝ | 0<y.2}) :
    ∃ C≥0, ∀ (g : ℂ × ℝ → ℂ), ContDiff ℝ 1 g → ∀ ε : ℝ, 0≤ε →
      (∀ y, ‖g y‖≤ε) → (∀ y, ‖fderiv ℝ g y‖≤ε) →
      (∫ y in K, (‖g y‖^2+y.2^2*cubicThetaFunctionEnergy g y)/y.2^3)≤C*ε^2 := by
  let a := fun y : ℂ × ℝ => (y.2^3)⁻¹+(Module.finrank ℝ CubicThetaTangent:ℝ)/y.2
  have ha : ContinuousOn a K :=
    (((continuous_snd.pow 3).continuousOn).inv₀ (fun y hy => pow_ne_zero 3 (hpos hy).ne')).add
      (continuousOn_const.div continuous_snd.continuousOn (fun y hy => (hpos hy).ne'))
  have hai := ha.integrableOn_compact (μ:=volume) hK
  refine ⟨∫ y in K, a y,?_,fun g hg ε hε hv hd => ?_⟩
  · apply setIntegral_nonneg hK.measurableSet
    intro y hy
    exact add_nonneg (inv_nonneg.mpr (pow_nonneg (hpos hy).le 3))
      (div_nonneg (Nat.cast_nonneg _) (hpos hy).le)
  · have hcont : ContinuousOn
        (fun y => (‖g y‖^2+y.2^2*cubicThetaFunctionEnergy g y)/y.2^3) K :=
      (((hg.continuous.norm.pow 2).continuousOn.add
        ((continuous_snd.pow 2).mul (cubicThetaFunctionEnergy_continuous hg)).continuousOn)).div
          (continuous_snd.pow 3).continuousOn (fun y hy => pow_ne_zero 3 (hpos hy).ne')
    calc
      _ ≤ ∫ y in K, a y*ε^2 :=
        setIntegral_mono_on (hcont.integrableOn_compact hK) (hai.mul_const _) hK.measurableSet
          (fun y hy => cubicThetaCoordinateEnergy_density_bound hε hv hd (hpos hy))
      _ = _ := integral_mul_const _ _

end CubicFirstMoment

end

end OAI
