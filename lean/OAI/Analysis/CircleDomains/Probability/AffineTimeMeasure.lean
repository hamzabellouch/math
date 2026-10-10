import OAI.Analysis.CircleDomains.Topology.AffineIntervalImages
import Mathlib.MeasureTheory.Measure.Map

namespace OAI

/-! The precise pullback of an arbitrary time measure to a retained affine
interval. This is the measure identity used for arclength restriction. -/

open Set MeasureTheory

noncomputable section

namespace CircleDomainRigidity

theorem preimage_rescale_Icc {a b : PathTime} (hab : a < b) (c d : PathTime) :
    rescalePathTime a b ⁻¹' Icc c d ∩ Icc a b =
      Icc (affinePathTime a b c) (affinePathTime a b d) := by
  have hf := affinePathTime_strictMono hab
  ext t
  constructor
  · rintro ⟨ht, habt⟩
    have he := affine_rescalePathTime hab habt
    constructor
    · simpa only [he] using hf.monotone ht.1
    · simpa only [he] using hf.monotone ht.2
  · intro ht
    have hct := affinePathTime_mem_Icc hab.le c
    have hdt := affinePathTime_mem_Icc hab.le d
    have htab : t ∈ Icc a b := ⟨hct.1.trans ht.1, ht.2.trans hdt.2⟩
    have he := affine_rescalePathTime hab htab
    refine ⟨⟨?_, ?_⟩, htab⟩
    · apply hf.le_iff_le.mp
      rw [he]
      exact ht.1
    · apply hf.le_iff_le.mp
      rw [he]
      exact ht.2

theorem map_rescale_restrict_Icc (μ : Measure PathTime) {a b : PathTime}
    (hab : a < b) (c d : PathTime) :
    ((μ.restrict (Icc a b)).map (rescalePathTime a b)) (Icc c d) =
      μ (Icc (affinePathTime a b c) (affinePathTime a b d)) := by
  rw [Measure.map_apply (rescalePathTime a b).continuous.measurable measurableSet_Icc,
    Measure.restrict_apply ((rescalePathTime a b).continuous.measurable measurableSet_Icc),
    preimage_rescale_Icc hab]

end CircleDomainRigidity

end

end OAI
