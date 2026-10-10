import OAI.Analysis.FiniteFactor.CrossedProduct.StageOperator

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal
noncomputable section

/-- Both source widths, derived from the stages already constructed. -/
def sourceWidth (s : ℕ) : Fin 2 → ℝ :=
  ![(sourceStageState s).G/(sourceBlockSize s : ℝ), (sourceBlockSize s : ℝ)^(-19/20 : ℝ)]

theorem sourceWidth_bounds (s : ℕ) (w : Fin 2) :
    1/(sourceBlockSize s : ℝ) ≤ sourceWidth s w ∧ sourceWidth s w ≤ 1/4 := by
  have hm : (100 : ℝ) ≤ sourceBlockSize s := by exact_mod_cast (sourceStage s).m_ge_100
  have hm0 := sourceBlockSize_pos s
  fin_cases w
  · simp only [sourceWidth]
    constructor
    · exact div_le_div_of_nonneg_right (sourceStageState s).G_ge hm0.le
    · apply (div_le_iff₀ hm0).mpr
      have hh := (sourceStage s).m_ge_G
      change 4*(sourceStageState s).G ≤ (sourceBlockSize s : ℝ) at hh
      linarith
  · simp only [sourceWidth]
    constructor
    · rw [one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    · have hsqrt : (4 : ℝ) ≤ Real.sqrt (sourceBlockSize s : ℝ) := by
        apply (Real.le_sqrt (by norm_num) hm0.le).mpr
        nlinarith
      have hpow : Real.sqrt (sourceBlockSize s : ℝ) ≤ (sourceBlockSize s : ℝ)^(19/20 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) (hsqrt.trans hpow)
      rw [show (-19/20 : ℝ) = -(19/20) by ring, Real.rpow_neg hm0.le]
      simpa [one_div] using hh

/-- The source coupling parameters now have all width and scale hypotheses
discharged by the recursive construction. j is the unique tagged block. -/
def stagedCouplingParameters (j s : ℕ) : CouplingParameters where
  m := sourceBlockSize s
  kappa := sourceKappa s
  width := sourceWidth s
  tagged := decide (s=j)
  m_ge := by exact_mod_cast (sourceStage s).m_ge_100
  kappa_nonneg := by unfold sourceKappa; positivity
  kappa_le := by
    unfold sourceKappa
    apply one_div_le_one_div_of_le (by norm_num)
    have hh : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    nlinarith
  width_lower := fun w => (sourceWidth_bounds s w).1
  width_upper := fun w => (sourceWidth_bounds s w).2

/-- Actual infinite endpoint densities for the recursively constructed source
coupling. There are no assumed scale, width, or density hypotheses. -/
theorem stagedCoupling_endpoint_L2_density (j : ℕ) (right : SourceCoordinate → Bool) :
    ∃ g : (SourceCoordinate → ℝ) → ℝ,
      MemLp g 2 (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) ∧
      (∀ᵐ x ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure), 0 ≤ g x) ∧
      (∫ x, g x ^ 2 ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) ≤
        Real.exp (20*(2*(∑' s, sourceKappa s ^ 2)+1)) ∧
      (CouplingParameters.blockProductCoupling (stagedCouplingParameters j) sourceBlockSize).map
          (CouplingParameters.blockProductEndpoint right) =
        (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)).withDensity
          (fun x => ENNReal.ofReal (g x)) :=
  CouplingParameters.blockProductEndpoint_L2_density (stagedCouplingParameters j) sourceBlockSize
    (fun _ => rfl) j (fun _ => rfl) (fun _ => rfl) right

end
end FiniteFactor

end OAI
