import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory
namespace CylinderOpenThickening

theorem compact_open_enlarge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)]
    [Measure.OuterRegular (volume : Measure E)]
    {K : Set E} (hK : IsCompact K) {eps : ℝ} (heps : 0 < eps) :
    ∃ U : Set E, K ⊆ U ∧ IsOpen U ∧ Bornology.IsBounded U ∧
      MeasurableSet U ∧ volume.real U < volume.real K + eps := by
  obtain ⟨O, hKO, hOo, hOm⟩ := K.exists_isOpen_lt_add
    (μ := volume) hK.measure_lt_top.ne (ENNReal.ofReal_pos.mpr heps).ne'
  let U := O ∩ Metric.thickening 1 K
  have hUo : IsOpen U := hOo.inter Metric.isOpen_thickening
  have hUb : Bornology.IsBounded U :=
    hK.isBounded.thickening.subset inter_subset_right
  have hKU : K ⊆ U := fun x hx =>
    ⟨hKO hx, Metric.self_subset_thickening (by norm_num) K hx⟩
  have hUm : volume U < volume K + ENNReal.ofReal eps :=
    (measure_mono inter_subset_left).trans_lt hOm
  refine ⟨U, hKU, hUo, hUb, hUo.measurableSet, ?_⟩
  have hfin : volume K + ENNReal.ofReal eps ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hK.measure_lt_top.ne, ENNReal.ofReal_ne_top⟩
  have hh := (ENNReal.toReal_lt_toReal (ne_top_of_lt hUm) hfin).mpr hUm
  simpa only [Measure.real, ENNReal.toReal_add hK.measure_lt_top.ne
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal heps.le] using hh

end CylinderOpenThickening

end

end OAI
