import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.BoundedMulLp

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology ENNReal

variable {X : Type*} [MeasurableSpace X] {m : Measure X}
lemma boundedMulLp_tendsto {φ : ℕ → X → ℝ}
    (hφ : ∀ n,AEStronglyMeasurable (φ n) m)
    (hφ1 : ∀ n,∀ᵐ x ∂m,|φ n x| ≤ 1)
    (hconv : ∀ᵐ x ∂m,Tendsto (fun n => φ n x) atTop (𝓝 1)) (f : Lp ℝ 2 m) :
    Tendsto (fun n => boundedMulLp (hφ n) (hφ1 n) f) atTop (𝓝 f) := by
  let g : ℕ → X → ℝ := fun n x => f x*φ n x
  have hg (n : ℕ) : MemLp (g n) 2 m := memLp_mul_bounded (Lp.memLp f) (hφ n) (hφ1 n)
  have hdom (n : ℕ) : ∀ᵐ x ∂m,‖g n x‖ ≤ ‖f x‖ := by
    filter_upwards [hφ1 n] with x hx
    calc ‖g n x‖ = |f x| *|φ n x| := by simp [g]
         _ ≤ |f x| *1 := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
         _ = ‖f x‖ := by simp
  have hi : UnifIntegrable g 2 m := by
    rw [unifIntegrable_iff']
    intro ε hε
    obtain ⟨δ,hδ,hδf⟩ := (Lp.memLp f).eLpNorm_indicator_le (by norm_num) (by norm_num) hε
    refine ⟨δ,hδ,fun n s hs hms => ?_⟩
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs]
    apply le_trans (eLpNorm_mono_ae ((hg n).aestronglyMeasurable.indicator hs) ?_) (hδf s hs hms)
    filter_upwards [hdom n] with x hx
    by_cases hxs : x ∈ s
    · simpa only [indicator_of_mem hxs] using hx
    · simp only [indicator_of_notMem hxs,le_refl]
  have ht : UnifTight g 2 m := by
    intro ε hε
    obtain ⟨supportSet, hsupportSet, hfinite, hbound⟩ :=
      (unifTight_const (ι := ℕ) (by norm_num) (Lp.memLp f)).exists_measurableSet_indicator hε.ne'
    refine ⟨supportSet,hfinite.ne,fun n => ?_⟩
    apply le_trans
      (eLpNorm_mono_ae ((hg n).aestronglyMeasurable.indicator hsupportSet.compl) ?_) (hbound n)
    filter_upwards [hdom n] with x hx
    by_cases hxs : x ∈ supportSetᶜ
    · simpa only [indicator_of_mem hxs] using hx
    · simp only [indicator_of_notMem hxs,le_refl]
  have hc : ∀ᵐ x ∂m,Tendsto (fun n => g n x) atTop (𝓝 (f x)) := hconv.mono fun x hx => by
    simpa only [mul_one] using hx.const_mul (f x)
  have H := tendsto_Lp_of_tendsto_ae (by norm_num : (1:ℝ≥0∞) ≤ 2)
    (by norm_num : (2:ℝ≥0∞) ≠ ∞) (fun n => (hg n).aestronglyMeasurable) (Lp.memLp f) hi ht hc
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  convert H using 1
  ext n
  apply eLpNorm_congr_ae
  filter_upwards [boundedMulLp_ae (hφ n) (hφ1 n) f] with x hx
  simp only [Pi.sub_apply,hx,g]
end WeakHessian

end
end InlinedFile0

end OAI
