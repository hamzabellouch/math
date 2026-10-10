import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedCoefficientPointwise
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueWhittaker

namespace OAI

/-! The actual translated-cusp coefficients in the fixed Whittaker normalization. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaShiftedPoleHeat_whittaker {h : Eisenstein} (hh : h≠0)
    {v : ℝ} (hv : 0<v) :
    (v:ℂ)^(4/3:ℂ)*(∫ t in Ioi (0:ℝ), cubicThetaDualHeat v (4/3) (cubicThetaShiftedRowHeatScale h) t)=
      ((2*(cubicThetaShiftedRowHeatScale h)^(1/6:ℝ)/‖cubicThetaShiftedRowFrequency h‖:ℝ):ℂ)*
        cubicThetaWhittaker (‖cubicThetaShiftedRowFrequency h‖*v) := by
  let A := cubicThetaShiftedRowHeatScale h
  let q := ‖cubicThetaShiftedRowFrequency h‖
  have hA : 0<A := cubicThetaShiftedRowHeatScale_pos hh
  have hq : 0<q := norm_pos_iff.mpr (by
    change (h:ℂ)/(9*traceLambda)≠0
    exact div_ne_zero (fun hz => hh (Subtype.ext hz)) (mul_ne_zero (by norm_num) traceLambda_ne_zero))
  have hI : (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v (4/3) A t)=
      ((A^(1/3:ℝ)/(A*v^2)^(1/6:ℝ):ℝ):ℂ)*(cubicBesselKernel (A*v^2):ℂ) := by
    rw [← cubicTheta_cubicPole_heat hA hv]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 0<t at ht
    dsimp only [cubicThetaDualHeat]
    rw [show (4/3:ℂ)-2=((-2/3:ℝ):ℂ) by norm_num,← Complex.ofReal_cpow ht.le]
  have hx : (2*Real.pi*(q*v))^2=A*v^2 := by
    dsimp [A,q,cubicThetaShiftedRowHeatScale]
    rw [Complex.normSq_eq_norm_sq]
    ring
  have hd : (A*v^2)^(1/6:ℝ)=A^(1/6:ℝ)*v^(1/3:ℝ) := by
    rw [Real.mul_rpow hA.le (sq_nonneg v),← Real.rpow_natCast v 2,← Real.rpow_mul hv.le]
    norm_num
  have ha : A^(1/3:ℝ)=A^(1/6:ℝ)*A^(1/6:ℝ) := by
    rw [← Real.rpow_add hA]
    norm_num
  have hpow : v^(4/3:ℝ)=v*v^(1/3:ℝ) := by
    rw [show (4/3:ℝ)=1+1/3 by norm_num,Real.rpow_add hv,Real.rpow_one]
  have hr : v^(4/3:ℝ)*(A^(1/3:ℝ)/(A*v^2)^(1/6:ℝ))=
      (2*A^(1/6:ℝ)/q)*(q*v/2) := by
    rw [hd,ha,hpow]
    field_simp
  change (v:ℂ)^(4/3:ℂ)*(∫ t in Ioi (0:ℝ), cubicThetaDualHeat v (4/3) A t)=_
  rw [hI,show (4/3:ℂ)=((4/3:ℝ):ℂ) by norm_num,← Complex.ofReal_cpow hv.le]
  change _=((2*A^(1/6:ℝ)/q:ℝ):ℂ)*cubicThetaWhittaker (q*v)
  rw [cubicThetaWhittaker,hx]
  rw [← mul_assoc, ← Complex.ofReal_mul, hr]
  push_cast
  ring

lemma cubicThetaShiftedCoefficient_whittaker (m n : ℤ) {h : Eisenstein} (hh : h≠0)
    {v : ℝ} (hv : 1<v) :
    cubicThetaShiftedModelHorizontal ((m:Eisenstein)+n*omegaE) h v=
      (cubicThetaShiftedResidueFactor n h*
        ((2*(cubicThetaShiftedRowHeatScale h)^(1/6:ℝ)/‖cubicThetaShiftedRowFrequency h‖:ℝ):ℂ))*
        cubicThetaWhittaker (‖cubicThetaShiftedRowFrequency h‖*v) := by
  rw [cubicThetaShiftedCoefficient_pointwise m n hh hv,cubicThetaShiftedPoleRadial,
    cubicThetaShiftedPoleHeat_whittaker hh (by linarith)]
  ring

end CubicFirstMoment

end

end OAI
