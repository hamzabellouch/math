import OAI.Probability.InvariantIsing.Pressure.PressureMean

namespace OAI

/-! Exact factorization of the Ising reference at zero interaction. -/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

lemma sum_exp_fieldEnergy {N : ℕ} (c : Fin N → ℝ) :
    (∑ σ : Spin N, Real.exp (fieldEnergy c σ)) = ∏ i, 2 * Real.cosh (c i) := by
  simp only [fieldEnergy, Real.exp_sum]
  rw [← Fintype.prod_sum (fun (i : Fin N) (b : Bool) => Real.exp (c i * spinValue b))]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fintype.sum_bool]
  norm_num [spinValue, Real.cosh_eq]
  ring

/-- The site factorization used before the backward Gaussian cascade recursion. -/
theorem logPartition_fieldEnergy {N : ℕ} (c : Fin N → ℝ) :
    logPartition (fieldEnergy c) = ∑ i, Real.log (Real.cosh (c i)) := by
  have hcard : (Fintype.card (Spin N) : ℝ) = ∏ _ : Fin N, (2 : ℝ) := by
    simp [Spin]
  have hc : (Fintype.card (Spin N) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [logPartition, sum_exp_fieldEnergy, Finset.prod_mul_distrib, ← hcard,
    ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  exact Real.log_prod (fun i _ => (Real.cosh_pos (c i)).ne')

theorem noninteractingPressure_eq_logCosh {N : ℕ} (c : Fin N → ℝ) :
    noninteractingPressure c = (N : ℝ)⁻¹ * ∑ i, Real.log (Real.cosh (c i)) := by
  rw [noninteractingPressure, logPartition_fieldEnergy]

end InvariantIsing

end

end OAI
