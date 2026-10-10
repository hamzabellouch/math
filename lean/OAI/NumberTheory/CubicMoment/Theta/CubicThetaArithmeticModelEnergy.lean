import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticModelIdentity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoefficientEnergy

namespace OAI

/-! The exact horizontal energy of the arithmetic residue model.
This retains the common scalar for its remaining normalization. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment
local instance cubicThetaArithmeticModelEnergyMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cubicThetaArithmeticModelEnergyProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def cubicThetaArithmeticFourierEnergy (v : ℝ) : ℝ :=
  ∑' h : Eisenstein,‖cubicThetaArithmeticRowTerm 0 v h‖^2

lemma cubicThetaTorusCoefficient_inner (F : CubicThetaTorusL2) (h : Eisenstein) :
    cubicThetaTorusCoefficient F h=inner ℂ (cubicThetaTorusBasis h) F := by
  unfold cubicThetaTorusCoefficient cubicThetaTorusBasis
  rw [←UnitAddTorus.mFourierBasis_repr,HilbertBasis.repr_apply_apply]

lemma cubicThetaArithmeticModelRemainder_energy {v : ℝ} (hv : 0<v) :
    ‖ContinuousMap.toLp 2 volume ℂ (cubicThetaArithmeticModelRemainder v)‖^2=
      cubicThetaArithmeticFourierEnergy v := by
  rw [←cubicThetaTorus_parseval]
  simp only [cubicThetaArithmeticModelRemainder_coefficient hv,cubicThetaArithmeticFourierEnergy]

lemma cubicThetaArithmeticFourierEnergy_summable {v : ℝ} (hv : 0<v) :
    Summable (fun h : Eisenstein => ‖cubicThetaArithmeticRowTerm 0 v h‖^2) := by
  simpa only [cubicThetaArithmeticModelRemainder_coefficient hv] using
    cubicThetaTorus_coefficients_summable
      (ContinuousMap.toLp 2 volume ℂ (cubicThetaArithmeticModelRemainder v))

theorem cubicThetaArithmeticModelTorus_energy (A : ℂ) {v : ℝ} (hv : 0<v) :
    ‖ContinuousMap.toLp 2 volume ℂ (cubicThetaArithmeticModelTorus A v)‖^2=
      (cubicThetaConstant*v^(2/3:ℝ))^2+
        ‖A‖^2*cubicThetaArithmeticFourierEnergy v := by
  let L : C(UnitAddTorus (Fin 2),ℂ) →L[ℂ] CubicThetaTorusL2 :=
    ContinuousMap.toLp 2 volume ℂ
  let R := L (cubicThetaArithmeticModelRemainder v)
  have hz : inner ℂ (cubicThetaTorusBasis 0) R=0 := by
    rw [←cubicThetaTorusCoefficient_inner,cubicThetaArithmeticModelRemainder_coefficient hv]
    simp [cubicThetaArithmeticRowTerm]
  have hb : ‖cubicThetaTorusBasis 0‖=1 :=
    UnitAddTorus.mFourierBasis.orthonormal.norm_eq_one _
  change ‖L (cubicThetaArithmeticModelTorus A v)‖^2=_
  rw [cubicThetaArithmeticModelTorus,map_add,map_smul,map_smul,
    cubicThetaTorusFourier_toLp]
  have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜:=ℂ)
    (((cubicThetaConstant*v^(2/3:ℝ):ℝ):ℂ) • cubicThetaTorusBasis 0) (A • R)
    (by rw [inner_smul_left,inner_smul_right,hz,mul_zero,mul_zero])
  simp only [←sq] at he
  rw [he]
  rw [norm_smul,norm_smul,hb,mul_one,mul_pow,cubicThetaArithmeticModelRemainder_energy hv,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]

end CubicFirstMoment

end

end OAI
