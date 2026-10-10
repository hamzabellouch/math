import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.IsometricSMul

namespace OAI

/-! # Metric Følner sets force right invariance of Haar measure

Right translation moves every point a fixed distance in a left invariant
metric. A nontrivial modular character contradicts the neighborhood-volume
ratio tending to one.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter
open scoped Topology ENNReal

theorem isMulRightInvariant_of_metricFolner
    {G ι : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
    [IsIsometricSMul G G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [Measure.InnerRegular μ]
    {l : Filter ι} [l.NeBot] (A : ι → Set G)
    (hA : ∀ i, MeasurableSet (A i))
    (hzero : ∀ i, μ (A i) ≠ 0) (hfinite : ∀ i, μ (A i) ≠ ∞)
    (hratio : ∀ R : ℝ, 0 ≤ R →
      Tendsto (fun i => μ (Metric.cthickening R (A i)) / μ (A i)) l (𝓝 1)) :
    μ.IsMulRightInvariant := by
  have hle (g : G) : Measure.modularCharacter g ≤ 1 := by
    have hbound (i : ι) : (Measure.modularCharacter g : ℝ≥0∞) ≤
        μ (Metric.cthickening (dist (1 : G) g) (A i)) / μ (A i) := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl (hzero i)) (Or.inl (hfinite i))).mpr
      have hsubset : (fun x : G => x * g) ⁻¹' A i ⊆
          Metric.cthickening (dist (1 : G) g) (A i) := by
        intro x hx
        apply Metric.mem_cthickening_of_dist_le x (x * g) _ _ hx
        have hh := dist_mul_left x (1 : G) g
        simpa only [mul_one] using hh.le
      have hm := μ.mono hsubset
      change μ ((fun x : G => x * g) ⁻¹' A i) ≤
        μ (Metric.cthickening (dist (1 : G) g) (A i)) at hm
      rw [← Measure.map_apply (measurable_mul_const g) (hA i),
        Measure.map_right_mul_eq_modularCharacterFun_smul μ g] at hm
      rw [Measure.smul_apply] at hm
      change (Measure.modularCharacter g : ℝ≥0∞) * μ (A i) ≤ _ at hm
      exact hm
    have hh := ge_of_tendsto (hratio (dist (1 : G) g) dist_nonneg)
      (Eventually.of_forall hbound)
    exact_mod_cast hh
  have heq (g : G) : Measure.modularCharacter g = 1 := by
    apply le_antisymm (hle g)
    calc
      1 = Measure.modularCharacter g * Measure.modularCharacter g⁻¹ := by
        rw [← map_mul, mul_inv_cancel, map_one]
      _ ≤ Measure.modularCharacter g * 1 :=
        mul_le_mul_of_nonneg_left (hle g⁻¹) (zero_le : 0 ≤ Measure.modularCharacter g)
      _ = Measure.modularCharacter g := mul_one _
  refine ⟨fun g => ?_⟩
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g,
    show Measure.modularCharacterFun g = 1 from heq g, one_smul]

end PolycyclicRecognition

end

end OAI
