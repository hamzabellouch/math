import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.UniformSpace.CompactConvergence

namespace OAI

namespace Yau.Analysis
open Set Filter MeasureTheory
open scoped Topology
noncomputable section

theorem compact_uniform_integral_limit {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X] (mu : Measure X) [IsLocallyFiniteMeasure mu]
    (Q : Set X) (hQ : IsCompact Q) (F : ℕ → X → ℝ) (f : X → ℝ)
    (hF : ∀ j, Continuous (F j)) (hf : Continuous f)
    (hFs : ∀ j x, x ∉ Q → F j x=0) (hfs : ∀ x, x ∉ Q → f x=0)
    (hconv : TendstoUniformlyOn F f atTop Q) :
    Tendsto (fun j ↦ ∫ x, F j x ∂mu) atTop (𝓝 (∫ x, f x ∂mu)) := by
  have hfinite : IsFiniteMeasure (mu.restrict Q) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hQ.measure_lt_top⟩
  obtain ⟨C,hC⟩ := hQ.exists_bound_of_continuousOn hf.continuousOn
  have hbound : ∃ B, ∀ᶠ j in atTop, ∀ᵐ x ∂mu.restrict Q, ‖F j x‖ ≤ B := by
    refine ⟨C+1,?_⟩
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv 1 (by norm_num)] with j hj
    filter_upwards [ae_restrict_mem hQ.measurableSet] with x hx
    have hb : |f x| ≤ C := hC x hx
    have hd : |f x-F j x| < 1 := by simpa only [Real.dist_eq] using hj x hx
    have h1 := abs_le.mp hb
    have h2 := abs_lt.mp hd
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have ht := tendsto_integral_filter_of_norm_le_const
    (μ := mu.restrict Q)
    (Eventually.of_forall (fun j ↦ (hF j).aestronglyMeasurable)) hbound
    ((ae_restrict_mem hQ.measurableSet).mono (fun x hx ↦ hconv.tendsto_at hx))
  simpa only [setIntegral_eq_integral_of_forall_compl_eq_zero (hFs _),
    setIntegral_eq_integral_of_forall_compl_eq_zero hfs] using ht

end
end Yau.Analysis

end OAI
