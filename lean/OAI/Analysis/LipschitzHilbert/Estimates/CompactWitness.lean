import OAI.Analysis.LipschitzHilbert.Fourier.WitnessLineAverage
import Mathlib.MeasureTheory.Measure.Regular

namespace OAI

/-! The compact subwitness used for measurable horizontal projections. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

/-- Inner regularity produces the compact witness with half the original
area, while preserving every pointwise witness condition by inclusion. -/
theorem exists_compact_half_witness (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (hfinite : (volume.prod volume) E ≠ ∞) (hpos : 0 < (volume.prod volume).real E) :
    ∃ K ⊆ E, IsCompact K ∧ (volume.prod volume).real E / 2 ≤
      (volume.prod volume).real K := by
  have hr : ENNReal.ofReal ((volume.prod volume).real E / 2) < (volume.prod volume) E := by
    rw [← ENNReal.ofReal_toReal hfinite]
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr (by linarith)
  obtain ⟨K, hKE, hK, harea⟩ := hE.exists_lt_isCompact_of_ne_top hfinite hr
  refine ⟨K, hKE, hK, ?_⟩
  have hle := ENNReal.toReal_mono (hK.measure_lt_top.ne) harea.le
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (volume.prod volume).real E / 2)] at hle
  exact hle

namespace SlopeBox

/-- Extract the compact subwitness needed by the line-average argument from
the original measurable popularity witness. -/
theorem exists_compact_popularity_witness (T : SlopeBox) (E : Set (ℝ × ℝ))
    (hE : MeasurableSet E) (hfinite : (volume.prod volume) E ≠ ∞) {q A : ℝ}
    (hq : 0 < q) (harea : q * T.length * T.width ≤ (volume.prod volume).real E)
    (hbox : ∀ z ∈ E, T.radius z ≤ A) :
    ∃ K ⊆ E, IsCompact K ∧
      (q / 2) * T.length * T.width ≤ (volume.prod volume).real K ∧
      ∀ z ∈ K, T.radius z ≤ A := by
  have hlength := T.length_pos
  have hwidth := T.width_pos
  have hpos : 0 < (volume.prod volume).real E :=
    (mul_pos (mul_pos hq hlength) hwidth).trans_le harea
  obtain ⟨K, hKE, hK, hhalf⟩ := exists_compact_half_witness E hE hfinite hpos
  refine ⟨K, hKE, hK, ?_, fun z hz => hbox z (hKE hz)⟩
  linarith

end SlopeBox
end LipschitzHilbert

end

end OAI
