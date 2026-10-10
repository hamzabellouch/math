import Mathlib
import OAI.Geometry.CAT0Fillings.Model

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
universe u

theorem IsCAT0.exists_squared_distance_convex
    {X : Type u} [MetricSpace X] (hX : IsCAT0 X) :
    ∃ segment : X → X → ℝ → X,
      (∀ x y, segment x y 0 = x ∧ segment x y 1 = y) ∧
      ∀ o y x t, t ∈ Icc (0 : ℝ) 1 →
        dist (segment o y t) x ^ 2 ≤
          (1 - t) * dist o x ^ 2 + t * dist y x ^ 2 -
            t * (1 - t) * dist o y ^ 2 := by
  obtain ⟨s, hs, _, hc⟩ := hX
  refine ⟨s, hs, ?_⟩
  intro o y x t ht
  have h := hc o y x t 1 ht (by simp)
  rw [(hs o x).2] at h
  convert h using 1
  ring

theorem IsCAT0.quadrilateral {X : Type u} [MetricSpace X] (hX : IsCAT0 X)
    (a b c d : X) :
    dist a c ^ 2 + dist b d ^ 2 ≤
      dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2 := by
  obtain ⟨s, _, hs⟩ := hX.exists_squared_distance_convex
  have hb := hs a c b (1 / 2) (by norm_num)
  have hd := hs a c d (1 / 2) (by norm_num)
  have ht := dist_triangle b (s a c (1 / 2)) d
  have ht' : dist b d ^ 2 ≤
      (dist b (s a c (1 / 2)) + dist (s a c (1 / 2)) d) ^ 2 :=
    (sq_le_sq₀ dist_nonneg (add_nonneg dist_nonneg dist_nonneg)).mpr ht
  have hm := sq_nonneg (dist b (s a c (1 / 2)) - dist (s a c (1 / 2)) d)
  rw [dist_comm c b] at hb
  rw [dist_comm a d] at hd
  rw [dist_comm b (s a c (1 / 2))] at ht' hm
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

end CAT0Fillings
end

end OAI
