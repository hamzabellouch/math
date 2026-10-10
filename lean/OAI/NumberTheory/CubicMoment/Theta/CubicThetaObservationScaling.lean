import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueNormalization
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowFrequencyScaling

namespace OAI

/-! The geometric normalization of the actual Whittaker observation
under multiplication of its arithmetic frequency. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPoleWeight_mul {u h : Eisenstein} (hu : u≠0) (hh : h≠0) :
    2*(cubicThetaRowHeatScale (u*h))^(1/6:ℝ)/‖cubicThetaRowFrequency (u*h)‖=
      (norm u)^(-(1/3:ℝ))*(2*(cubicThetaRowHeatScale h)^(1/6:ℝ)/‖cubicThetaRowFrequency h‖) := by
  have he := cubicThetaPoleFactor_mul hu hh
  have hn : (norm u)^(-(1/3:ℝ))=‖(u:ℂ)‖^(-(2/3:ℝ)) := by
    rw [show norm u=‖(u:ℂ)‖^2 from Complex.normSq_eq_norm_sq _,
      ←Real.rpow_natCast ‖(u:ℂ)‖ 2,←Real.rpow_mul (_root_.norm_nonneg _)]
    norm_num
  simpa only [←hn] using he

lemma cubicThetaPoleWeight_cube_mul {p h : Eisenstein} (hp : p≠0) (hh : h≠0) :
    2*(cubicThetaRowHeatScale (p^3*h))^(1/6:ℝ)/‖cubicThetaRowFrequency (p^3*h)‖=
      (norm p)⁻¹*(2*(cubicThetaRowHeatScale h)^(1/6:ℝ)/‖cubicThetaRowFrequency h‖) := by
  rw [cubicThetaPoleWeight_mul (pow_ne_zero 3 hp) hh,eisenstein_norm_pow,
    ← Real.rpow_natCast (norm p) 3,← Real.rpow_mul (norm_nonneg p)]
  norm_num [Real.rpow_neg_one]

def cubicThetaNormalizedObservedCoefficient (h : Eisenstein) : ℂ :=
  cubicThetaResidueScale*cubicThetaObservedWhittakerCoefficient h/
    ((9*Real.sqrt 3/2:ℝ):ℂ)

theorem cubicThetaNormalizedArithmeticResidue_observation {h : Eisenstein} (hh : h≠0)
    (W : CompactlySupportedContinuousMap ℝ ℂ) :
    inner ℂ (cubicThetaCuspFourierTest h W)
      (cubicThetaCuspRestriction cubicThetaNormalizedArithmeticResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicThetaNormalizedObservedCoefficient h*
        ∫ v in Set.Ioi (2:ℝ), star (W v)*
          cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*v)/(v:ℂ)^3 := by
  have hJ : ((9*Real.sqrt 3/2:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  rw [cubicThetaNormalizedArithmeticResidue,map_smul,inner_smul_right,
    cubicThetaResidue_whittaker_observation hh]
  unfold cubicThetaNormalizedObservedCoefficient
  field_simp

end CubicFirstMoment

end

end OAI
