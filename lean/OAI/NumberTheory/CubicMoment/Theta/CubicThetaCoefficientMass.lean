import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticModelEnergy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCommonIndex

namespace OAI

/-! The exact Dirichlet mass of the literal theta coefficients. The
unit, ramified, squarefree and cube factors are kept separate. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaCoefficientMassTerm (σ : ℝ) (n : Eisenstein) : ℝ :=
  ‖cubicThetaArithmeticCoefficient n‖^2 * (norm n)^(-σ)

def cubicThetaCoefficientMass (σ : ℝ) : ℝ :=
  ∑' n : Eisenstein, cubicThetaCoefficientMassTerm σ n

lemma cubicThetaCoefficientMass_reindex (σ : ℝ) :
    cubicThetaCoefficientMass σ = ∑' x : CubicThetaCommonIndex,
      cubicThetaCoefficientMassTerm σ (cubicThetaCommonNumerator x) := by
  unfold cubicThetaCoefficientMass
  apply (cubicThetaCommonNumerator_injective.tsum_eq ?_).symm
  intro n hn
  apply (cubicThetaCommonNumerator_range n).mpr
  by_contra he
  exact hn (by simp [cubicThetaCoefficientMassTerm,cubicThetaArithmeticCoefficient,he])

lemma cubicThetaCoordinates_norm {n : Eisenstein} (R : CubicThetaCoordinates n) :
    norm n = 3^R.order * norm R.squarefreePart * (norm R.cubePart)^3 := by
  conv_lhs => rw [R.numerator_eq]
  rw [norm_mul_eq,norm_mul_eq,norm_mul_eq,eisenstein_norm_pow,eisenstein_norm_pow]
  have hu : norm (R.unit:Eisenstein) = 1 := norm_of_isUnit R.unit.isUnit
  have hLam : norm lambdaE = 3 := traceLambda_normSq
  rw [hu,hLam,one_mul]
  ring

lemma CubicThetaCoordinates.mass_term {n : Eisenstein} (R : CubicThetaCoordinates n)
    (σ : ℝ) :
    cubicThetaCoefficientMassTerm σ n =
      (if R.order%3=0 ∧ 3 ≤ R.order then (1:ℝ)
       else if R.order%3=1 ∧ ((R.unit:Eisenstein)=1 ∨ (R.unit:Eisenstein)=-1)
         then 1 else 0) *
      3^(8-2*((R.order/3:ℕ):ℝ)-(R.order:ℝ)*σ) *
      (norm R.squarefreePart)^(-(1+σ)) *
      (norm R.cubePart)^(-(2+3*σ)) := by
  have hc := norm_pos_of_ne_zero (primary_ne_zero R.squarefree_primary)
  have hd := norm_pos_of_ne_zero (primary_ne_zero R.cube_primary)
  have hpow : (norm n)^(-σ) =
      3^(-(R.order:ℝ)*σ) * (norm R.squarefreePart)^(-σ) *
        (norm R.cubePart)^(-3*σ) := by
    rw [cubicThetaCoordinates_norm R,
      Real.mul_rpow (mul_nonneg (by positivity) hc.le) (pow_nonneg hd.le 3),
      Real.mul_rpow (by positivity) hc.le,
      ←Real.rpow_natCast (3:ℝ) R.order,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),
      ←Real.rpow_natCast (norm R.cubePart) 3,←Real.rpow_mul hd.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (R.order:ℝ)*(-σ) = -(R.order:ℝ)*σ by ring,
      show (3:ℝ)*(-σ) = -3*σ by ring]
  have ha : R.amplitude^2 * (norm n)^(-σ) =
      3^(8-2*((R.order/3:ℕ):ℝ)-(R.order:ℝ)*σ) *
      (norm R.squarefreePart)^(-(1+σ)) *
      (norm R.cubePart)^(-(2+3*σ)) := by
    have h3 : (3:ℝ)^(8-2*((R.order/3:ℕ):ℝ)) * 3^(-(R.order:ℝ)*σ) =
        3^(8-2*((R.order/3:ℕ):ℝ)-(R.order:ℝ)*σ) := by
      rw [←Real.rpow_add (by norm_num : (0:ℝ) < 3)]
      congr 1
      ring
    have hce : (norm R.squarefreePart)^(-σ) / norm R.squarefreePart =
        (norm R.squarefreePart)^(-(1+σ)) := by
      rw [div_eq_mul_inv,←Real.rpow_neg_one,←Real.rpow_add hc]
      congr 1
      ring
    have hde : (norm R.cubePart)^(-3*σ) / (norm R.cubePart)^2 =
        (norm R.cubePart)^(-(2+3*σ)) := by
      rw [div_eq_mul_inv,←Real.rpow_two,←Real.rpow_neg hd.le,←Real.rpow_add hd]
      congr 1
      ring
    rw [R.amplitude_sq,hpow]
    calc
      _ = (3^(8-2*((R.order/3:ℕ):ℝ))*3^(-(R.order:ℝ)*σ)) *
          ((norm R.squarefreePart)^(-σ)/norm R.squarefreePart) *
          ((norm R.cubePart)^(-3*σ)/(norm R.cubePart)^2) := by
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      _ = _ := by rw [h3,hce,hde]
  rw [cubicThetaCoefficientMassTerm,cubicThetaArithmeticCoefficient_formula R,R.coefficient_norm]
  split_ifs <;> simp_all only [one_mul,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul]

end CubicFirstMoment

end

end OAI
