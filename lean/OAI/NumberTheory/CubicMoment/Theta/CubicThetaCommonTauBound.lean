import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCommonCoefficientBound
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCubeCancellation

namespace OAI

/-! The actual unnormalized dual coefficient has the ramified growth and
square-root cube-factor bound required for the local summation formula. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_coordinate_norm (e : Eisensteinˣ) (k : ℕ) (c d : Eisenstein) :
    ‖cubicThetaFrequency ((e:Eisenstein)*lambdaE^k*(c*d^3))‖=
      (Real.sqrt 3)^k*Real.sqrt (norm c)*(Real.sqrt (norm d))^3/9 := by
  have hr (a : Eisenstein) : Real.sqrt (norm a)=‖(a:ℂ)‖ := by
    rw [norm,Complex.normSq_eq_norm_sq,Real.sqrt_sq (_root_.norm_nonneg _)]
  have hl : Real.sqrt (norm lambdaE)=Real.sqrt 3 := by
    rw [norm,lambdaE_coe,traceLambda_normSq]
  rw [cubicThetaFrequency_div_nine,norm_div,Complex.norm_ofNat]
  simp only [Subalgebra.coe_mul,Subalgebra.coe_pow,norm_mul,norm_pow,
    cubicTheta_unit_norm,one_mul]
  rw [←hr lambdaE,←hr c,←hr d,hl]
  ring

lemma cubicTheta_coordinate_amplitude_product (k : ℕ) {c d : Eisenstein}
    (hc : primary c) (hd : primary d) :
    ((Real.sqrt 3)^k*Real.sqrt (norm c)*(Real.sqrt (norm d))^3/9)*
      (3^(4-((k/3:ℕ):ℝ))/(Real.sqrt (norm c)*norm d))=
        9*3^((k:ℝ)/2-((k/3:ℕ):ℝ))*Real.sqrt (norm d) := by
  have hc0 := (Real.sqrt_pos.mpr (norm_pos_of_ne_zero (primary_ne_zero hc))).ne'
  have hd0 := (norm_pos_of_ne_zero (primary_ne_zero hd)).ne'
  have hp : (Real.sqrt 3)^k*3^(4-((k/3:ℕ):ℝ))/9=
      9*3^((k:ℝ)/2-((k/3:ℕ):ℝ)) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3),
      ←Real.rpow_add (by norm_num : (0:ℝ)<3)]
    calc
      _ = 3^((1/2:ℝ)*k+(4-((k/3:ℕ):ℝ)))/3^(2:ℝ) := by rw [Real.rpow_two]; norm_num
      _ = 3^((1/2:ℝ)*k+(4-((k/3:ℕ):ℝ))-2) :=
        (Real.rpow_sub (by norm_num : (0:ℝ)<3) _ _).symm
      _ = _ := by
        rw [show (1/2:ℝ)*k+(4-((k/3:ℕ):ℝ))-2=
          2+((k:ℝ)/2-((k/3:ℕ):ℝ)) by ring,
          Real.rpow_add (by norm_num : (0:ℝ)<3),Real.rpow_two]
        norm_num
  calc
    _ = ((Real.sqrt 3)^k*3^(4-((k/3:ℕ):ℝ))/9)*Real.sqrt (norm d) := by
      field_simp
      rw [show (Real.sqrt (norm d))^3=Real.sqrt (norm d)*(Real.sqrt (norm d))^2 by ring,
        Real.sq_sqrt (norm_nonneg d)]
    _ = _ := by rw [hp]

lemma cubicTheta_ramified_growth_exponent (k : ℕ) :
    (k:ℝ)/2-((k/3:ℕ):ℝ) ≤ ((max ((k:ℤ)-1) 0:ℤ):ℝ)/3+1 := by
  have hq : k≤3*(k/3)+2 := by omega
  have hq' : (k:ℝ)≤3*((k/3:ℕ):ℝ)+2 := by exact_mod_cast hq
  have hm : (k:ℝ)-1≤((max ((k:ℤ)-1) 0:ℤ):ℝ) := by
    exact_mod_cast (le_max_left ((k:ℤ)-1) 0)
  have hk : 0≤(k:ℝ) := Nat.cast_nonneg k
  linarith

theorem cubicThetaCommonTau_coordinate_bound (e : Eisensteinˣ) (k : ℕ)
    {c d : Eisenstein} (hc : primary c) (hd : primary d) (hs : Squarefree c) :
    ‖cubicThetaCommonTau ((e:Eisenstein)*lambdaE^k*(c*d^3))‖≤
      27*3^(((max ((k:ℤ)-1) 0:ℤ):ℝ)/3)*Real.sqrt (norm d) := by
  unfold cubicThetaCommonTau
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _)]
  calc
    _ ≤ ‖cubicThetaFrequency ((e:Eisenstein)*lambdaE^k*(c*d^3))‖*
        (3^(4-((k/3:ℕ):ℝ))/(Real.sqrt (norm c)*norm d)) :=
      mul_le_mul_of_nonneg_left (cubicThetaCommon_coordinate_bound e k hc hd hs)
        (_root_.norm_nonneg _)
    _ = 9*3^((k:ℝ)/2-((k/3:ℕ):ℝ))*Real.sqrt (norm d) := by
      rw [cubicThetaFrequency_coordinate_norm,cubicTheta_coordinate_amplitude_product k hc hd]
    _ ≤ 9*3^(((max ((k:ℤ)-1) 0:ℤ):ℝ)/3+1)*Real.sqrt (norm d) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
            (cubicTheta_ramified_growth_exponent k)) (by norm_num))
        (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.rpow_add (by norm_num : (0:ℝ)<3),Real.rpow_one]
      ring

end CubicFirstMoment

end

end OAI
