import OAI.Analysis.LipschitzHilbert.Estimates.SlicedIntegral

namespace OAI

/-! Integrating a uniform real section-length bound in reference coordinates. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert

theorem section_measure_bound (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (U V : Set ℝ) (hV : MeasurableSet V) (hUf : volume U ≠ ∞) (hVf : volume V ≠ ∞)
    (hsub : E ⊆ U ×ˢ V) {M : ℝ} (hM : 0 ≤ M)
    (hsections : ∀ y ∈ V, volume.real ((fun x => (x, y)) ⁻¹' E) ≤ M) :
    (volume.prod volume).real E ≤ M * volume.real V := by
  have hsectionSub (y : ℝ) : ((fun x => (x, y)) ⁻¹' E) ⊆ U :=
    fun x hx => (hsub hx).1
  have hsectionFinite (y : ℝ) : volume ((fun x => (x, y)) ⁻¹' E) ≠ ∞ :=
    measure_ne_top_of_subset (hsectionSub y) hUf
  have hpoint (y : ℝ) : volume ((fun x => (x, y)) ⁻¹' E) ≤
      V.indicator (fun _ => ENNReal.ofReal M) y := by
    by_cases hy : y ∈ V
    · rw [indicator_of_mem hy]
      exact (ENNReal.le_ofReal_iff_toReal_le (hsectionFinite y) hM).2 (hsections y hy)
    · rw [indicator_of_notMem hy]
      have heq : ((fun x => (x, y)) ⁻¹' E) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hy (hsub hx).2
      simp only [heq, measure_empty, le_refl]
  have hmeasure : (volume.prod volume) E ≤ ENNReal.ofReal M * volume V := by
    rw [Measure.prod_apply_symm hE]
    calc
      _ ≤ ∫⁻ y, V.indicator (fun _ => ENNReal.ofReal M) y := lintegral_mono hpoint
      _ = _ := by rw [lintegral_indicator hV, lintegral_const, Measure.restrict_apply_univ]
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVf) hmeasure
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hM] using hreal

end LipschitzHilbert

end

end OAI
