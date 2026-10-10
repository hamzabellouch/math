import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGaussTwist

namespace OAI

/-! The two additional arithmetic families in DR v3 (5.13)--(5.14),
normalized by |mu| on the common lambda^-4 frequency lattice. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicTheta_unit_norm (u : Eisensteinˣ) : ‖((u:Eisenstein):ℂ)‖ = 1 := by
  have h := norm_of_isUnit u.isUnit
  change Complex.normSq ((u:Eisenstein):ℂ) = 1 at h
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [_root_.norm_nonneg ((u:Eisenstein):ℂ)]

def CubicThetaCoordinates.cuspCoefficient {n : Eisenstein}
    (R : CubicThetaCoordinates n) (j : Fin 3) : ℂ :=
  if j = 0 then R.coefficient
  else if R.order = 0 ∧ ((j = 1 ∧ (R.unit:Eisenstein)^3 = 1) ∨
      (j = 2 ∧ (R.unit:Eisenstein)^3 = -1)) then
    (R.amplitude:ℂ)*omega^(j:ℕ)*((R.unit:Eisenstein):ℂ)^4*cubicThetaUnitPhase R.unit*
      star (cubicThetaTwistedGauss R.squarefreePart ((R.unit:Eisenstein)^4*lambdaE^2))
  else 0

lemma CubicThetaCoordinates.cuspCoefficient_norm_le {n : Eisenstein}
    (R : CubicThetaCoordinates n) (j : Fin 3) : ‖R.cuspCoefficient j‖ ≤ 81 := by
  unfold cuspCoefficient
  split_ifs
  · exact R.coefficient_norm_le
  · simp only [norm_mul,norm_pow,cubicTheta_unit_norm,cubicThetaUnitPhase_norm,
      one_pow,mul_one,norm_star]
    have hω : ‖omega‖ = 1 := by
      have h := cubicTheta_unit_norm (Units.mkOfMulEqOne omegaE (omegaE^2) (by
        rw [mul_comm,←pow_succ,omegaE_cube]))
      exact h
    rw [hω,one_pow,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg R.amplitude_nonneg]
    exact (mul_le_of_le_one_right R.amplitude_nonneg
      (cubicThetaTwistedGauss_norm_le R.squarefree_primary R.squarefree _)).trans R.amplitude_le
  · norm_num

def cubicThetaCuspCoefficient (j : Fin 3) (n : Eisenstein) : ℂ :=
  if h : Nonempty (CubicThetaCoordinates n) then (Classical.choice h).cuspCoefficient j else 0

lemma cubicThetaCuspCoefficient_formula {n : Eisenstein} (R : CubicThetaCoordinates n) (j : Fin 3) :
    cubicThetaCuspCoefficient j n = R.cuspCoefficient j := by
  unfold cubicThetaCuspCoefficient
  rw [dite_eq_left (show Nonempty (CubicThetaCoordinates n) from ⟨R⟩),
    (Classical.choice (show Nonempty (CubicThetaCoordinates n) from ⟨R⟩)).unique R]

lemma cubicThetaCuspCoefficient_zero : cubicThetaCuspCoefficient 0 = cubicThetaArithmeticCoefficient := by
  funext n
  unfold cubicThetaCuspCoefficient cubicThetaArithmeticCoefficient
  split_ifs <;> simp [CubicThetaCoordinates.cuspCoefficient]

lemma cubicThetaCuspCoefficient_norm_le (j : Fin 3) (n : Eisenstein) :
    ‖cubicThetaCuspCoefficient j n‖ ≤ 81 := by
  unfold cubicThetaCuspCoefficient
  split_ifs with h
  · exact (Classical.choice h).cuspCoefficient_norm_le j
  · norm_num

lemma cubicThetaCuspCoefficient_bound (j : Fin 3) (n : Eisenstein) (hn : n ≠ 0) :
    ‖cubicThetaCuspCoefficient j n‖ ≤ 81*norm n :=
  (cubicThetaCuspCoefficient_norm_le j n).trans
    (le_mul_of_one_le_right (by norm_num) (one_le_norm hn))

/-- All three literal arithmetic coefficient families define convergent
Fourier expansions in the upper half-space. -/
theorem cubicThetaCusp_summable (j : Fin 3) {v : ℝ} (hv : 0 < v) (z : ℂ) :
    Summable (cubicThetaSeriesTerm (cubicThetaCuspCoefficient j) z v) :=
  cubicThetaSeries_summable (by norm_num : (0:ℝ) ≤ 81) (cubicThetaCuspCoefficient_bound j) hv z

end CubicFirstMoment

end

end OAI
