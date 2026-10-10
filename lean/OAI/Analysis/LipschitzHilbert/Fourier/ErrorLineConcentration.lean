import OAI.Analysis.LipschitzHilbert.Estimates.PositiveErrorMajorant

namespace OAI

/-! Line moments of the positive error majorant, and transfer to any
measurable nonnegative error that it dominates. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.LineErrorSources

attribute [local instance] Classical.propDecidable

variable {N : ℕ}

theorem majorant_root_integral (P : LineErrorSources N) (g : FiniteLineGrid)
    (hwidth : P.topLength ≤ g.width) :
    (∫ x, P.majorant x ∂g.lineMeasure) ≤ P.meanConstant * g.width := by
  have hlen (j : Fin N) : P.length j ≤ g.width :=
    (div_le_self P.topLength_pos.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))).trans hwidth
  have heq : P.shortPart g.width = P.majorant := by
    funext x
    unfold shortPart majorant
    apply Finset.sum_congr rfl
    intro j _
    exact ite_eq_left (hlen j)
  have h := P.shortPart_integral g.origin g.width g.width_pos
  rw [heq] at h
  have hi : IntegrableOn P.majorant (Icc (g.origin-g.width) (g.origin+g.width)) :=
    P.majorant_continuous.continuousOn.integrableOn_Icc
  have hsub : g.root ⊆ Icc (g.origin-g.width) (g.origin+g.width) := by
    intro x hx
    exact ⟨by linarith [hx.1,g.width_pos], hx.2.le⟩
  exact (setIntegral_mono_set hi (Filter.Eventually.of_forall (fun x => P.majorant_nonneg x))
    (Filter.Eventually.of_forall (fun _ hx => hsub hx))).trans h

theorem majorant_mean (P : LineErrorSources N) (g : FiniteLineGrid)
    (hwidth : P.topLength ≤ g.width) :
    |integralAverage g.lineMeasure P.majorant| ≤ P.meanConstant := by
  have hmass : g.lineMeasure.real univ = g.width := by
    change (volume.restrict g.root).real univ = g.width
    simpa only [g.cell_zero, FiniteLineGrid.meshWidth, pow_zero, div_one] using g.cell_mass 0 0
  have hn : 0 ≤ ∫ x, P.majorant x ∂g.lineMeasure := integral_nonneg P.majorant_nonneg
  rw [integralAverage, smul_eq_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr measureReal_nonneg),
    abs_of_nonneg hn, hmass]
  calc
    _ ≤ g.width⁻¹ * (P.meanConstant * g.width) :=
      mul_le_mul_of_nonneg_left (P.majorant_root_integral g hwidth) (inv_nonneg.mpr g.width_pos.le)
    _ = _ := by field_simp [g.width_pos.ne']

theorem majorant_moment (P : LineErrorSources N) (g : FiniteLineGrid)
    (hb : 1 < g.branching) (hwidth : P.topLength ≤ g.width) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x, (ENNReal.ofReal (P.majorant x))^p ∂g.lineMeasure) ≤
      (2 : ℝ≥0∞)^p *
        (7 * ENNReal.ofReal ((p * (((g.branching : ℝ)+2) *
          (2 * P.meanConstant + P.oscillationConstant + 1)) / Real.log (3/2))^p) +
          (ENNReal.ofReal P.meanConstant)^p) * g.lineMeasure univ := by
  have hi : Integrable P.majorant g.lineMeasure := by
    have h := g.continuous_integrable_cell P.majorant_continuous 0 0
    rw [g.cell_zero] at h
    exact h
  have hK : 0 ≤ P.meanConstant := by
    have := P.sumBound_nonneg
    unfold meanConstant
    positivity
  have hC : 0 ≤ P.oscillationConstant := by
    have := P.sourceBound_nonneg
    unfold oscillationConstant
    positivity
  have hA : 0 < 2 * P.meanConstant + P.oscillationConstant + 1 := by positivity
  have hBMO : g.HasFullMeanOscillationBound P.majorant
      (2 * P.meanConstant + P.oscillationConstant + 1) := by
    intro level i hi
    exact (P.majorant_mean_oscillation g level i hi).trans
      (mul_le_mul_of_nonneg_right (by linarith) (g.meshWidth_pos level).le)
  have h := g.continuous_raw_moment hb P.majorant P.majorant_continuous.measurable hi
    (fun _ _ => P.majorant_continuous.continuousAt) hA hBMO (P.majorant_mean g hwidth) hp
  simpa only [abs_of_nonneg (P.majorant_nonneg _)] using h

theorem dominated_error_moment (P : LineErrorSources N) (g : FiniteLineGrid)
    (hb : 1 < g.branching) (hwidth : P.topLength ≤ g.width) (E : ℝ → ℝ)
    (hE : ∀ x, E x ≤ P.majorant x) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x, (ENNReal.ofReal (E x))^p ∂g.lineMeasure) ≤
      (2 : ℝ≥0∞)^p *
        (7 * ENNReal.ofReal ((p * (((g.branching : ℝ)+2) *
          (2 * P.meanConstant + P.oscillationConstant + 1)) / Real.log (3/2))^p) +
          (ENNReal.ofReal P.meanConstant)^p) * g.lineMeasure univ := by
  exact (lintegral_mono (fun x => ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hE x)) hp)).trans
    (P.majorant_moment g hb hwidth hp)

end LipschitzHilbert.LineErrorSources

end

end OAI
