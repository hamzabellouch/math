import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Tactic.Module
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

namespace Yau
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def segmentPoint (a b : E) (t : ℝ) : E := (1 - t) • a + t • b

theorem zero_on_segment {u : E → ℝ} (hu : Continuous u) {a b : E}
    (ha : u a < 0) (hb : 0 < u b) :
    ∃ t ∈ Icc (0 : ℝ) 1, u (segmentPoint a b t) = 0 := by
  have hc : Continuous (fun t : ℝ ↦ u (segmentPoint a b t)) :=
    hu.comp (((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const))
  have h0 : (0 : ℝ) ∈ Icc (u (segmentPoint a b 0)) (u (segmentPoint a b 1)) := by
    simpa [segmentPoint] using And.intro ha.le hb.le
  exact intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc.continuousOn h0

theorem projection_covers {u : E → ℝ} (hu : Continuous u)
    (P : E →L[ℝ] F) (L : F →L[ℝ] E) (hL : ∀ z, P (L z) = z)
    {a b : E} (ha : P a = 0) (hb : P b = 0) {A : Set F} {C : Set E}
    (hneg : ∀ z ∈ A, u (a + L z) < 0)
    (hpos : ∀ z ∈ A, 0 < u (b + L z))
    (hseg : ∀ z ∈ A, ∀ t ∈ Icc (0 : ℝ) 1,
      segmentPoint (a + L z) (b + L z) t ∈ C) :
    A ⊆ P '' (C ∩ {x | u x = 0}) := by
  intro z hz
  obtain ⟨t, ht, hzero⟩ := zero_on_segment hu (hneg z hz) (hpos z hz)
  refine ⟨segmentPoint (a + L z) (b + L z) t, ⟨hseg z hz t ht, hzero⟩, ?_⟩
  simp only [segmentPoint, map_add, map_smul, ha, hb, hL, zero_add]
  module

theorem hausdorff_nodal_lower_bound
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    {u : E → ℝ} (hu : Continuous u)
    (P : E →L[ℝ] F) (L : F →L[ℝ] E) (hL : ∀ z, P (L z) = z)
    {a b : E} (ha : P a = 0) (hb : P b = 0) {A : Set F} {C : Set E}
    (hneg : ∀ z ∈ A, u (a + L z) < 0)
    (hpos : ∀ z ∈ A, 0 < u (b + L z))
    (hseg : ∀ z ∈ A, ∀ t ∈ Icc (0 : ℝ) 1,
      segmentPoint (a + L z) (b + L z) t ∈ C)
    {K : ℝ≥0} (hP : LipschitzWith K P) {d : ℝ} (hd : 0 ≤ d) :
    Measure.hausdorffMeasure d A ≤
      (K : ℝ≥0∞) ^ d * Measure.hausdorffMeasure d (C ∩ {x | u x = 0}) := by
  exact (measure_mono (projection_covers hu P L hL ha hb hneg hpos hseg)).trans
    (hP.hausdorffMeasure_image_le hd _)

end
end Yau

end OAI
