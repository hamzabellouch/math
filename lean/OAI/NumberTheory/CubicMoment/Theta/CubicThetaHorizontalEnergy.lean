import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticModelEnergy

namespace OAI

/-! The normalized Fourier energy is the literal squared modulus integrated
over the physical level-three horizontal cell, with its exact area. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment
local instance cubicThetaHorizontalEnergyMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cubicThetaHorizontalEnergyProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma cubicThetaTorus_norm_square_integral (F : C(UnitAddTorus (Fin 2),ℂ)) :
    (∫ t, (‖F t‖^2:ℂ))=(‖ContinuousMap.toLp 2 volume ℂ F‖^2:ℂ) := by
  have hr : (∫ t,‖F t‖^2)=‖ContinuousMap.toLp 2 volume ℂ F‖^2 := by
    rw [cubicTheta_l2_norm_sq_measure]
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℂ) volume F] with t ht
    rw [ht]
  have hc := congrArg Complex.ofReal hr
  rw [←integral_complex_ofReal] at hc
  simpa only [Complex.ofReal_pow] using hc

lemma cubicThetaArithmeticModel_horizontal_energy (A : ℂ) {v : ℝ} (hv : 0<v) :
    (∫ z in cubicThetaHorizontalCell,(‖cubicThetaArithmeticModel A (z,v)‖^2:ℂ))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*
        (((cubicThetaConstant*v^(2/3:ℝ))^2:ℝ)+
          ‖A‖^2*cubicThetaArithmeticFourierEnergy v) := by
  let G : C(UnitAddTorus (Fin 2),ℂ) :=
    ⟨fun t => (‖cubicThetaArithmeticModelTorus A v t‖^2:ℂ),by fun_prop⟩
  have he := cubicThetaHorizontalCoefficient
    (fun z => (‖cubicThetaArithmeticModel A (z,v)‖^2:ℂ)) G 0
    (fun x => by change _=(‖cubicThetaArithmeticModelTorus A v _‖^2:ℂ)
                 rw [cubicThetaArithmeticModelTorus_real A hv])
  have hzero (z : ℂ) :
      (Real.fourierChar (tracePair z (cubicThetaRowFrequency 0)):ℂ)=1 := by
    simp [cubicThetaRowFrequency,tracePair]
  simp_rw [hzero,star_one,one_mul] at he
  rw [he,cubicThetaTorusCoefficient_integral]
  simp only [cubicThetaTorusFourier_zero,ContinuousMap.one_apply,star_one,one_mul]
  change _ • (∫ t,(‖cubicThetaArithmeticModelTorus A v t‖^2:ℂ))=_
  rw [cubicThetaTorus_norm_square_integral]
  rw [←Complex.ofReal_pow,cubicThetaArithmeticModelTorus_energy A hv]
  simp only [Complex.real_smul,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow]

end CubicFirstMoment

end

end OAI
