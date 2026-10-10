import OAI.GroupTheory.PolycyclicRecognition.Analysis.SectionVolume
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

namespace OAI

/-! # Compact coordinate sections with quantitative retained volume -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory
open scoped ENNReal

theorem isCompact_coordinate_section
    {V Z : Type*} [TopologicalSpace V] [TopologicalSpace Z] [T1Space Z]
    {K : Set (V × Z)} (hK : IsCompact K) (z : Z) :
    IsCompact {v | (v, z) ∈ K} := by
  have he : {v | (v, z) ∈ K} =
      Prod.fst '' (K ∩ Prod.snd ⁻¹' {z}) := by
    ext v
    constructor
    · intro hv
      exact ⟨(v, z), ⟨hv, rfl⟩, rfl⟩
    · rintro ⟨⟨w, y⟩, ⟨hw, hy⟩, rfl⟩
      simp only [mem_preimage, mem_singleton_iff] at hy
      change (w, z) ∈ K
      simpa only [hy] using hw
  rw [he]
  exact (hK.inter_right (isClosed_singleton.preimage continuous_snd)).image continuous_fst

theorem exists_compact_section_volume_gt
    (n k : ℕ) {K : Set ((Fin n → ℝ) × (Fin k → ℝ))}
    (hK : IsCompact K) {Q : Set (Fin k → ℝ)} (hQ : IsCompact Q)
    (hKQ : ∀ p ∈ K, p.2 ∈ Q)
    {t q : ℝ} (ht : 0 ≤ t) (hq : (volume Q).toReal ≤ q)
    (hmass : t * q < (volume K).toReal) :
    ∃ z ∈ Q, IsCompact {v | (v, z) ∈ K} ∧
      t < (volume {v | (v, z) ∈ K}).toReal := by
  have hlt : ENNReal.ofReal t * volume Q < volume K := by
    apply (ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top (by simp) hQ.measure_ne_top) hK.measure_ne_top).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht]
    exact (mul_le_mul_of_nonneg_left hq ht).trans_lt hmass
  obtain ⟨z, hz, hvolume⟩ := exists_section_measure_gt volume volume hK.measurableSet
    hQ.measurableSet hKQ (ENNReal.ofReal t) hlt
  have hsection := isCompact_coordinate_section hK z
  refine ⟨z, hz, hsection, ?_⟩
  have hh := (ENNReal.toReal_lt_toReal (by simp) hsection.measure_ne_top).mpr hvolume
  simpa only [ENNReal.toReal_ofReal ht] using hh

end PolycyclicRecognition

end

end OAI
