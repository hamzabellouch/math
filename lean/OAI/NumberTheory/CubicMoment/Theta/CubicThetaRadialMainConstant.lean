import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialRawVoronoi

namespace OAI

/-! Exact comparison of the constructed radial residue with the printed
main-term constant. The remaining arithmetic normalization is explicit. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRadial_uncompletion_pole {r : Eisenstein} (hr : primary r) :
    cubicThetaAngularUncompletion r 0 (5/6)=
      ((4*cubicThetaLevelScale r^(2/3:ℝ)*(2*Real.pi)^(5/3:ℝ)/Real.Gamma (2/3:ℝ):ℝ):ℂ) := by
  unfold cubicThetaAngularUncompletion
  norm_num only [Nat.cast_zero,zero_div,add_zero,
    show 2*(5/6:ℂ)-1=2/3 by norm_num,
    show 2*(5/6:ℂ)=5/3 by norm_num,
    show (5/6:ℂ)+1/6=1 by norm_num,
    show (5/6:ℂ)-1/6=2/3 by norm_num,
    Complex.Gamma_one,inv_one,mul_one]
  rw [show (2/3:ℂ)=((2/3:ℝ):ℂ) by norm_num,
    show (5/3:ℂ)=((5/3:ℝ):ℂ) by norm_num,
    ←Complex.ofReal_cpow (cubicThetaLevelScale_pos hr).le,
    ←Complex.ofReal_cpow (by positivity : (0:ℝ)≤2*Real.pi),Complex.Gamma_ofReal]
  push_cast
  ring

lemma cubicThetaRadial_level_pole_power {r : Eisenstein} (hr : primary r) :
    cubicThetaLevelScale r^(2/3:ℝ)*cubicThetaLevelScale r^(2/3:ℝ)/Real.sqrt (norm r)=
      norm r^(-7/6:ℝ) := by
  have hN := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hS := Real.sqrt_pos.mpr hN
  rw [←Real.rpow_add (cubicThetaLevelScale_pos hr)]
  norm_num only [show (2/3:ℝ)+2/3=4/3 by norm_num]
  unfold cubicThetaLevelScale
  rw [Real.inv_rpow hS.le,div_eq_mul_inv,←Real.rpow_neg hS.le,
    ←Real.rpow_neg_one,←Real.rpow_add hS,
    Real.sqrt_eq_rpow,←Real.rpow_mul hN.le]
  congr 1
  norm_num

lemma cubicThetaSeriesConstant_mul_base :
    star cubicThetaSeriesConstant*star cubicThetaArithmeticBaseScalar=(cubicThetaConstant:ℂ) := by
  rw [←star_mul,cubicThetaSeriesConstant,mul_div_cancel₀ _ cubicThetaArithmeticBaseScalar_ne_zero]
  exact Complex.conj_ofReal _

lemma cubicThetaRadial_scale_pole {X : ℝ} (hX : 0<X) :
    (X/27)^(5/6:ℝ)=X^(5/6:ℝ)/(3:ℝ)^(5/2:ℝ) := by
  rw [Real.div_rpow hX.le (by norm_num)]
  congr 1
  calc
    (27:ℝ)^(5/6:ℝ)=((3:ℝ)^(3:ℝ))^(5/6:ℝ) := by norm_num
    _ = (3:ℝ)^((3:ℝ)*(5/6)) := (Real.rpow_mul (by norm_num) _ _).symm
    _ = _ := by norm_num

lemma cubicThetaRadial_real_main {r : Eisenstein} (hr : primary r) {X : ℝ} (hX : 0<X) :
    (4*cubicThetaLevelScale r^(2/3:ℝ)*(2*Real.pi)^(5/3:ℝ)/Real.Gamma (2/3:ℝ))/2*
      (metaplecticTotient r*(cubicThetaConstant/3))*cubicThetaLevelScale r^(2/3:ℝ)/
      ((3:ℝ)^(5/2:ℝ)*Real.sqrt (norm r))*(X/27)^(5/6:ℝ)=
      metaplecticA0*X^(5/6:ℝ)*metaplecticTotient r*norm r^(-7/6:ℝ) := by
  have hthree : (3:ℝ)^(7/2:ℝ)=3*(3:ℝ)^(5/2:ℝ) := by
    rw [show (7/2:ℝ)=1+5/2 by norm_num,Real.rpow_add (by norm_num),Real.rpow_one]
  have h35 : (3:ℝ)^(5/2:ℝ)≠0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hG : Real.Gamma (2/3:ℝ)≠0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  calc
    _ = (2*cubicThetaConstant/(3*(3:ℝ)^(5/2:ℝ)))*
        (cubicThetaLevelScale r^(2/3:ℝ)*cubicThetaLevelScale r^(2/3:ℝ)/Real.sqrt (norm r))*
        ((2*Real.pi)^(5/3:ℝ)/Real.Gamma (2/3:ℝ))*metaplecticTotient r*(X/27)^(5/6:ℝ) := by ring
    _ = _ := by
      rw [cubicThetaRadial_level_pole_power hr,cubicThetaRadial_scale_pole hX]
      unfold cubicThetaConstant metaplecticA0
      rw [hthree]
      field_simp

/-- This comparison isolates the exact outstanding normalization: the
constructed main term times the conjugate base scalar is the printed one. -/
theorem cubicThetaActualCompletedRadialMain_mul_base {r : Eisenstein} (hr : primary r)
    (W : ℝ→ℂ) {X : ℝ} (hX : 0<X) :
    cubicThetaActualCompletedRadialMain r W X*star cubicThetaArithmeticBaseScalar=
      metaplecticMain r 0 W X := by
  rw [cubicThetaActualCompletedRadialMain,cubicThetaResidueRadialPole,
    cubicThetaRadial_uncompletion_pole hr]
  have hX27 : 0≤X/27 := (div_pos hX (by norm_num)).le
  rw [show (5/6:ℂ)=((5/6:ℝ):ℂ) by norm_num,←Complex.ofReal_cpow hX27]
  calc
    _ = ((4*cubicThetaLevelScale r^(2/3:ℝ)*(2*Real.pi)^(5/3:ℝ)/Real.Gamma (2/3:ℝ):ℝ):ℂ)/2*
        ((Nat.card (Residues r)ˣ:ℂ)*((star cubicThetaSeriesConstant*star cubicThetaArithmeticBaseScalar)/3))*
        ((cubicThetaLevelScale r^(2/3:ℝ):ℝ):ℂ)/
        (((3^(5/2:ℝ):ℝ):ℂ)*(Real.sqrt (norm r):ℂ))*
        (((X/27)^(5/6:ℝ):ℝ):ℂ)*mellin W (5/6) := by
      push_cast
      ring
    _ = _ := by
      rw [cubicThetaSeriesConstant_mul_base]
      have he := congrArg (fun q : ℝ => (q:ℂ)*mellin W (5/6)) (cubicThetaRadial_real_main hr hX)
      simpa only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat,
        metaplecticMain,ite_true,metaplecticTotient,Complex.ofReal_natCast,mul_assoc] using he

end CubicFirstMoment

end

end OAI
