import OAI.Analysis.LipschitzHilbert.Fourier.ErrorLineConcentration

namespace OAI

/-! Error moments on a reference interval only use retained packet
lengths. Empty longer scales do not enlarge the interval. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.LineErrorSources
attribute [local instance] Classical.propDecidable
variable {N : ℕ}

/-- Remove the unused long sources without changing either source budget. -/
def restrictLength (P : LineErrorSources N) (H : ℝ) : LineErrorSources N where
  topLength := P.topLength
  topLength_pos := P.topLength_pos
  sourceBound := P.sourceBound
  sourceBound_nonneg := P.sourceBound_nonneg
  sumBound := P.sumBound
  sumBound_nonneg := P.sumBound_nonneg
  source := fun j x => if P.length j ≤ H then P.source j x else 0
  measurable_source := fun j => by
    by_cases h : P.length j ≤ H
    · simpa only [ite_eq_left h] using P.measurable_source j
    · simp only [ite_eq_right h]
      exact measurable_const
  source_nonneg := fun j x => by split_ifs; exact P.source_nonneg j x; exact le_rfl
  source_bound := fun j x => by split_ifs; exact P.source_bound j x; exact P.sourceBound_nonneg
  source_sum := fun x => (Finset.sum_le_sum (fun j _ => by
    split_ifs; exact le_rfl; exact P.source_nonneg j x)).trans (P.source_sum x)

theorem restrictLength_source_zero (P : LineErrorSources N) (H : ℝ) (j : Fin N)
    (h : H < (P.restrictLength H).length j) : (P.restrictLength H).source j = 0 := by
  have hn : ¬ P.length j ≤ H := not_le.mpr h
  funext x
  simp only [restrictLength,ite_eq_right hn,Pi.zero_apply]

theorem majorant_root_integral_of_supported (P : LineErrorSources N) (g : FiniteLineGrid)
    (hsource : ∀ j, g.width < P.length j → P.source j = 0) :
    (∫ x, P.majorant x ∂g.lineMeasure) ≤ P.meanConstant*g.width := by
  have heq : P.shortPart g.width = P.majorant := by
    funext x
    unfold shortPart majorant
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : P.length j ≤ g.width
    · exact ite_eq_left h
    · rw [ite_eq_right h]
      simp only [term,hsource j (lt_of_not_ge h),positiveConvolution]
      simp
  have h := P.shortPart_integral g.origin g.width g.width_pos
  rw [heq] at h
  have hi : IntegrableOn P.majorant (Icc (g.origin-g.width) (g.origin+g.width)) :=
    P.majorant_continuous.continuousOn.integrableOn_Icc
  have hsub : g.root ⊆ Icc (g.origin-g.width) (g.origin+g.width) := by
    intro x hx
    exact ⟨by linarith [hx.1,g.width_pos],hx.2.le⟩
  exact (setIntegral_mono_set hi (Filter.Eventually.of_forall P.majorant_nonneg)
    (Filter.Eventually.of_forall (fun _ hx => hsub hx))).trans h

theorem majorant_mean_of_supported (P : LineErrorSources N) (g : FiniteLineGrid)
    (hsource : ∀ j, g.width < P.length j → P.source j = 0) :
    |integralAverage g.lineMeasure P.majorant| ≤ P.meanConstant := by
  have hmass : g.lineMeasure.real univ = g.width := by
    change (volume.restrict g.root).real univ = g.width
    simpa only [g.cell_zero,FiniteLineGrid.meshWidth,pow_zero,div_one] using g.cell_mass 0 0
  rw [integralAverage,smul_eq_mul,abs_mul,abs_of_nonneg (inv_nonneg.mpr measureReal_nonneg),
    abs_of_nonneg (integral_nonneg P.majorant_nonneg),hmass]
  calc
    _ ≤ g.width⁻¹*(P.meanConstant*g.width) := mul_le_mul_of_nonneg_left
      (P.majorant_root_integral_of_supported g hsource) (inv_nonneg.mpr g.width_pos.le)
    _ = _ := by field_simp [g.width_pos.ne']

theorem majorant_moment_of_supported (P : LineErrorSources N) (g : FiniteLineGrid)
    (hb : 1 < g.branching) (hsource : ∀ j, g.width < P.length j → P.source j = 0)
    {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x, (ENNReal.ofReal (P.majorant x))^p ∂g.lineMeasure) ≤
      (2:ℝ≥0∞)^p*(7*ENNReal.ofReal
        ((p*(((g.branching:ℝ)+2)*(2*P.meanConstant+P.oscillationConstant+1))/Real.log (3/2))^p)+
        (ENNReal.ofReal P.meanConstant)^p)*g.lineMeasure univ := by
  have hi : Integrable P.majorant g.lineMeasure := by
    have h := g.continuous_integrable_cell P.majorant_continuous 0 0
    rwa [g.cell_zero] at h
  have hmean : 0 ≤ P.meanConstant := by
    unfold meanConstant
    exact mul_nonneg (by positivity) P.sumBound_nonneg
  have hosc : 0 ≤ P.oscillationConstant := by
    unfold oscillationConstant
    exact mul_nonneg (by positivity) P.sourceBound_nonneg
  have hA : 0 < 2*P.meanConstant+P.oscillationConstant+1 := by positivity
  have hBMO : g.HasFullMeanOscillationBound P.majorant
      (2*P.meanConstant+P.oscillationConstant+1) := by
    intro level i hi
    exact (P.majorant_mean_oscillation g level i hi).trans
      (mul_le_mul_of_nonneg_right (by linarith) (g.meshWidth_pos level).le)
  have h := g.continuous_raw_moment hb P.majorant P.majorant_continuous.measurable hi
    (fun _ _ => P.majorant_continuous.continuousAt) hA hBMO
    (P.majorant_mean_of_supported g hsource) hp
  simpa only [abs_of_nonneg (P.majorant_nonneg _)] using h

end LipschitzHilbert.LineErrorSources

end

end OAI
