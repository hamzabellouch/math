import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedCoordinates
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaUpperMellin

namespace OAI

/-! The normalized arithmetic coefficient of DR v3 (5.7), indexed on the
common cusp lattice lambda^-4 Z[omega]. The coefficient used in the
Whittaker series is tau(mu)/|mu|. No modular transformation is asserted. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

@[ext] structure CubicThetaCoordinates (n : Eisenstein) where
  unit : Eisensteinˣ
  order : ℕ
  squarefreePart : Eisenstein
  cubePart : Eisenstein
  squarefree_primary : primary squarefreePart
  cube_primary : primary cubePart
  squarefree : Squarefree squarefreePart
  numerator_eq : n = (unit:Eisenstein)*lambdaE^order*(squarefreePart*cubePart^3)

lemma CubicThetaCoordinates.ne_zero {n : Eisenstein} (R : CubicThetaCoordinates n) : n ≠ 0 := by
  rw [R.numerator_eq]
  exact mul_ne_zero (mul_ne_zero R.unit.ne_zero (pow_ne_zero _ lambdaE_prime.ne_zero))
    (mul_ne_zero (primary_ne_zero R.squarefree_primary) (pow_ne_zero _ (primary_ne_zero R.cube_primary)))

lemma CubicThetaCoordinates.unique {n : Eisenstein} (R S : CubicThetaCoordinates n) : R = S := by
  have hpow (d : Eisenstein) (hd : primary d) : primary (d^3) := by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
      primary_mul hd (primary_mul hd hd)
  have hcpR := primary_mul R.squarefree_primary (hpow R.cubePart R.cube_primary)
  have hcpS := primary_mul S.squarefree_primary (hpow S.cubePart S.cube_primary)
  have h := unit_ramified_primary_unique hcpR hcpS (R.numerator_eq.symm.trans S.numerator_eq)
  have hc := primary_squarefree_cube_unique R.squarefree_primary R.cube_primary
    S.squarefree_primary S.cube_primary R.squarefree S.squarefree h.2.2
  exact CubicThetaCoordinates.ext h.1 h.2.1 hc.1 hc.2

/-- Unit phases in the first three cases of (5.7). Raising a sixth root
of unity to the fourth power removes its sign. -/
def cubicThetaUnitPhase (u : Eisensteinˣ) : ℂ :=
  if (u:Eisenstein)^4 = 1 then 1
  else if (u:Eisenstein)^4 = omegaE then (Real.fourierChar (-1/9) : ℂ)
  else (Real.fourierChar (1/9) : ℂ)

lemma cubicThetaUnitPhase_norm (u : Eisensteinˣ) : ‖cubicThetaUnitPhase u‖ = 1 := by
  unfold cubicThetaUnitPhase
  split_ifs <;> simp

/-- The normalized Gauss sum at an invertible additive frequency. -/
def cubicThetaTwistedGauss (c α : Eisenstein) : ℂ := star (cubicSymbol c α)*gauss c

lemma cubicThetaTwistedGauss_norm_le {c : Eisenstein} (hc : primary c) (hs : Squarefree c)
    (α : Eisenstein) : ‖cubicThetaTwistedGauss c α‖ ≤ 1 := by
  rw [cubicThetaTwistedGauss,norm_mul,norm_star,norm_gauss_of_squarefree hc hs,mul_one]
  exact norm_cubicSymbol_le_one hc α

def CubicThetaCoordinates.amplitude {n : Eisenstein} (R : CubicThetaCoordinates n) : ℝ :=
  3^(4-((R.order/3:ℕ):ℝ))/(Real.sqrt (norm R.squarefreePart)*norm R.cubePart)

lemma CubicThetaCoordinates.amplitude_nonneg {n : Eisenstein} (R : CubicThetaCoordinates n) :
    0 ≤ R.amplitude := by
  unfold amplitude
  exact div_nonneg (by positivity) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))

lemma CubicThetaCoordinates.amplitude_le {n : Eisenstein} (R : CubicThetaCoordinates n) :
    R.amplitude ≤ 81 := by
  have hcs := one_le_norm (primary_ne_zero R.squarefree_primary)
  have hd := one_le_norm (primary_ne_zero R.cube_primary)
  have hc : 1 ≤ Real.sqrt (norm R.squarefreePart) := by
    simpa using Real.sqrt_le_sqrt hcs
  have hden : 1 ≤ Real.sqrt (norm R.squarefreePart)*norm R.cubePart :=
    one_le_mul_of_one_le_of_one_le hc hd
  have hpow : (3:ℝ)^(4-((R.order/3:ℕ):ℝ)) ≤ 81 := by
    calc
      _ ≤ (3:ℝ)^(4:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by have h := Nat.cast_nonneg (R.order/3) (α := ℝ); linarith)
      _ = 81 := by norm_num
  exact (div_le_self (by positivity) hden).trans hpow

def CubicThetaCoordinates.coefficient {n : Eisenstein} (R : CubicThetaCoordinates n) : ℂ :=
  if R.order % 3 = 0 ∧ 3 ≤ R.order then
    (R.amplitude:ℂ)*cubicThetaUnitPhase R.unit*
      star (cubicThetaTwistedGauss R.squarefreePart ((R.unit:Eisenstein)^4*lambdaE^2))
  else if R.order % 3 = 1 ∧ ((R.unit:Eisenstein)=1 ∨ (R.unit:Eisenstein) = -1) then
    (R.amplitude:ℂ)*star (gauss R.squarefreePart)
  else 0

lemma CubicThetaCoordinates.coefficient_norm_le {n : Eisenstein} (R : CubicThetaCoordinates n) :
    ‖R.coefficient‖ ≤ 81 := by
  unfold coefficient
  split_ifs
  · rw [norm_mul,norm_mul,norm_star,cubicThetaUnitPhase_norm,mul_one,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg R.amplitude_nonneg]
    exact (mul_le_of_le_one_right R.amplitude_nonneg
      (cubicThetaTwistedGauss_norm_le R.squarefree_primary R.squarefree _)).trans R.amplitude_le
  · rw [norm_mul,norm_star,norm_gauss_of_squarefree R.squarefree_primary R.squarefree,
      mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg R.amplitude_nonneg]
    exact R.amplitude_le
  · norm_num

def cubicThetaArithmeticCoefficient (n : Eisenstein) : ℂ :=
  if h : Nonempty (CubicThetaCoordinates n) then (Classical.choice h).coefficient else 0

/-- Uniqueness makes the explicit formula independent of the chosen
coordinate witness. -/
lemma cubicThetaArithmeticCoefficient_formula {n : Eisenstein} (R : CubicThetaCoordinates n) :
    cubicThetaArithmeticCoefficient n = R.coefficient := by
  unfold cubicThetaArithmeticCoefficient
  rw [dite_eq_left (show Nonempty (CubicThetaCoordinates n) from ⟨R⟩),(Classical.choice (show Nonempty (CubicThetaCoordinates n) from ⟨R⟩)).unique R]

lemma cubicThetaArithmeticCoefficient_norm_le (n : Eisenstein) :
    ‖cubicThetaArithmeticCoefficient n‖ ≤ 81 := by
  unfold cubicThetaArithmeticCoefficient
  split_ifs with h
  · exact (Classical.choice h).coefficient_norm_le
  · norm_num

lemma cubicThetaArithmeticCoefficient_bound (n : Eisenstein) (hn : n ≠ 0) :
    ‖cubicThetaArithmeticCoefficient n‖ ≤ 81*norm n :=
  (cubicThetaArithmeticCoefficient_norm_le n).trans
    (le_mul_of_one_le_right (by norm_num) (one_le_norm hn))

/-- Absolute convergence for the literal normalized arithmetic coefficients. -/
theorem cubicThetaArithmetic_summable {v : ℝ} (hv : 0 < v) (z : ℂ) :
    Summable (cubicThetaSeriesTerm cubicThetaArithmeticCoefficient z v) :=
  cubicThetaSeries_summable (by norm_num : (0:ℝ) ≤ 81) cubicThetaArithmeticCoefficient_bound hv z

end CubicFirstMoment

end

end OAI
