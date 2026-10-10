import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexAnalyticValue
import OAI.LinearAlgebra.MatrixMultiplication.Rectangular.ComplexASI

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

noncomputable section

namespace MatrixMultiplication.Foundation

structure FiniteMMRealization where
  occurrences : ℕ
  multiplicity : ℕ
  auxiliaryRank : ℕ
  rows : ℕ
  inner : ℕ
  columns : ℕ
  occurrences_pos : 0 < occurrences
  multiplicity_pos : 0 < multiplicity
  auxiliaryRank_pos : 0 < auxiliaryRank
  rows_pos : 0 < rows
  inner_pos : 0 < inner
  columns_pos : 0 < columns
  order : ℕ
  degree : ℕ
  approximation : Tensor.PolynomialApproximation
    (Tensor.directSum (fun _ : Fin multiplicity =>
      Tensor.matrixMultiplication rows inner columns))
    (3 ^ occurrences * auxiliaryRank) order degree

namespace FiniteMMRealization

def rates (W : FiniteMMRealization) : FiniteConstructionRates where
  occurrences := W.occurrences
  multiplicity := W.multiplicity
  auxiliaryRank := W.auxiliaryRank
  volume := W.rows * W.inner * W.columns
  occurrences_pos := W.occurrences_pos
  multiplicity_pos := W.multiplicity_pos
  auxiliaryRank_pos := W.auxiliaryRank_pos
  volume_pos := Nat.mul_pos (Nat.mul_pos W.rows_pos W.inner_pos) W.columns_pos

theorem score_mono (W : FiniteMMRealization) {β γ : ℝ} (hβγ : β ≤ γ) :
    W.rates.score β ≤ W.rates.score γ := by
  have hN : (0 : ℝ) < W.rates.occurrences := by
    exact_mod_cast W.rates.occurrences_pos
  have hv : (1 : ℝ) ≤ W.rates.volume := by
    exact_mod_cast (Nat.succ_le_iff.mpr W.rates.volume_pos)
  have hlog := Real.log_nonneg hv
  dsimp [FiniteConstructionRates.score]
  apply (div_le_div_iff_of_pos_right hN).2
  nlinarith

theorem score_omega_le_log_three (W : FiniteMMRealization) :
    W.rates.score Arithmetic.omega ≤ Real.log 3 := by
  have h := Arithmetic.equalRectangular_inequality_of_polynomialApproximation
    (Nat.succ_le_iff.mpr W.rows_pos) (Nat.succ_le_iff.mpr W.inner_pos)
    (Nat.succ_le_iff.mpr W.columns_pos) W.approximation
  have hL : (0 : ℝ) < W.multiplicity := by exact_mod_cast W.multiplicity_pos
  have hR : (0 : ℝ) < W.auxiliaryRank := by exact_mod_cast W.auxiliaryRank_pos
  have hN : (0 : ℝ) < W.occurrences := by exact_mod_cast W.occurrences_pos
  have hv : (0 : ℝ) < W.rates.volume := by exact_mod_cast W.rates.volume_pos
  have hp : (0 : ℝ) < (W.rates.volume : ℝ) ^ (Arithmetic.omega / 3) :=
    Real.rpow_pos_of_pos hv _
  change (W.multiplicity : ℝ) * (W.rates.volume : ℝ) ^ (Arithmetic.omega / 3) ≤
    ((3 ^ W.occurrences * W.auxiliaryRank : ℕ) : ℝ) at h
  have hlog := Real.log_le_log (mul_pos hL hp) h
  rw [Real.log_mul (ne_of_gt hL) (ne_of_gt hp), Real.log_rpow hv] at hlog
  have hcost :
      Real.log ((3 ^ W.occurrences * W.auxiliaryRank : ℕ) : ℝ) =
        (W.occurrences : ℝ) * Real.log 3 + Real.log W.auxiliaryRank := by
    push_cast
    rw [Real.log_mul (pow_ne_zero _ (by norm_num)) (ne_of_gt hR), Real.log_pow]
  rw [hcost] at hlog
  change (Real.log W.multiplicity - Real.log W.auxiliaryRank +
    Arithmetic.omega / 3 * Real.log W.rates.volume) / W.occurrences ≤ Real.log 3
  apply (div_le_iff₀ hN).2
  nlinarith

theorem omega_lt_of_score_gt (W : FiniteMMRealization) {β : ℝ}
    (hscore : Real.log 3 < W.rates.score β) : Arithmetic.omega < β := by
  by_contra h
  have hmono := W.score_mono (le_of_not_gt h)
  exact (not_lt_of_ge (hmono.trans W.score_omega_le_log_three)) hscore

end FiniteMMRealization

def realizedFamily {C X : Type*} (β : ℝ) (law : C → X)
    (realization : C → FiniteMMRealization) : AttainableFamily C X :=
  finiteConstructionFamily β law (fun c => (realization c).rates)

theorem omega_lt_of_realized_value_gt {C X : Type*} [TopologicalSpace X]
    (β : ℝ) (law : C → X) (realization : C → FiniteMMRealization) (x : X)
    (hne : ((realizedFamily β law realization).fiber x).Nonempty)
    (hgap : Real.log 3 < (realizedFamily β law realization).value x) :
    Arithmetic.omega < β := by
  obtain ⟨c, hc⟩ := (realizedFamily β law realization).exists_finite_gt hne hgap
  exact (realization c).omega_lt_of_score_gt hc

end MatrixMultiplication.Foundation

end

end OAI
