import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem continuous_integral_Lp_of_le {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] (hμν : μ ≤ ν)
    {q : ℝ≥0∞} (hq : 1 ≤ q) [Fact (1 ≤ q)] :
    Continuous (fun f : Lp ℝ q ν => ∫ x, f x ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro f
  have hmem (g : Lp ℝ q ν) : MemLp g q μ := (Lp.memLp g).mono_measure hμν
  have ht : Tendsto (fun g : Lp ℝ q ν => eLpNorm (⇑g - ⇑f) q ν) (𝓝 f) (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' id f).mp tendsto_id
  let C : ℝ≥0∞ := μ univ ^ (1 - 1 / q.toReal)
  have hC : C ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg _ (measure_ne_top μ univ)
    by_cases hqt : q = ∞
    · simp [hqt]
    · have hqr : 1 ≤ q.toReal := by exact_mod_cast (ENNReal.toReal_mono hqt hq)
      exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hqr)
  have htC : Tendsto (fun g : Lp ℝ q ν => eLpNorm (⇑g - ⇑f) q ν * C)
      (𝓝 f) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const ht (Or.inr hC)
  have ht1 : Tendsto (fun g : Lp ℝ q ν => eLpNorm (⇑g - ⇑f) 1 μ) (𝓝 f) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htC
    · exact fun _ => bot_le
    · intro g
      calc
        eLpNorm (⇑g - ⇑f) 1 μ ≤ eLpNorm (⇑g - ⇑f) q μ * C := by
          simpa [C] using eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq
            ((hmem g).sub (hmem f)).aestronglyMeasurable
        _ ≤ eLpNorm (⇑g - ⇑f) q ν * C :=
          mul_le_mul_left (eLpNorm_mono_measure _ hμν) _
  exact tendsto_integral_of_L1' f
    (Eventually.of_forall (fun g => (hmem g).integrable hq)) ht1

end PlanarFalconer

end OAI
