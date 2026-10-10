import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFrequencyResidue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierBessel

namespace OAI

/-! The actual spectral residue observations have the same fixed
Whittaker kernel as the explicit arithmetic theta expansion. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPoleHeat_whittaker {h : Eisenstein} (hh : h≠0)
    {v : ℝ} (hv : 0<v) :
    (v:ℂ)^(4/3:ℂ)*(∫ t in Ioi (0:ℝ), cubicThetaDualHeat v (4/3) (cubicThetaRowHeatScale h) t)=
      ((2*(cubicThetaRowHeatScale h)^(1/6:ℝ)/‖cubicThetaRowFrequency h‖:ℝ):ℂ)*
        cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*v) := by
  let A := cubicThetaRowHeatScale h
  let q := ‖cubicThetaRowFrequency h‖
  have hA : 0<A := cubicThetaRowHeatScale_pos hh
  have hq : 0<q := norm_pos_iff.mpr (by
    change (h:ℂ)/(3*traceLambda)≠0
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
    dsimp [A,q,cubicThetaRowHeatScale]
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

lemma cubicThetaPoleRadialTest_whittaker {h : Eisenstein} (hh : h≠0) (W : C_c(ℝ,ℂ)) :
    cubicThetaFourierRadialTest h W (4/3)=
      ((2*(cubicThetaRowHeatScale h)^(1/6:ℝ)/‖cubicThetaRowFrequency h‖:ℝ):ℂ)*
        ∫ v in Ioi (2:ℝ), star (W v)*cubicThetaWhittaker (‖cubicThetaRowFrequency h‖*v)/(v:ℂ)^3 := by
  rw [cubicThetaFourierRadialTest,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  change 2<v at hv
  dsimp only
  rw [show star (W v)*(v:ℂ)^(4/3:ℂ)*
      (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v (4/3) (cubicThetaRowHeatScale h) t)/(v:ℂ)^3=
      star (W v)*((v:ℂ)^(4/3:ℂ)*
        (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v (4/3) (cubicThetaRowHeatScale h) t))/(v:ℂ)^3 by ring,
    cubicThetaPoleHeat_whittaker hh (by linarith)]
  ring

end CubicFirstMoment

end

end OAI
