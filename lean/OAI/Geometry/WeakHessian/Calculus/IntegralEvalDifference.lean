import Mathlib
import OAI.Geometry.WeakHessian.Model

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {m : Measure X} [m.WeaklyRegular]

omit [m.WeaklyRegular] in
lemma integral_eval_difference_le {π : Measure (Curve X)} {C : ℝ≥0}
    (hC : ∀ t : Time, π.map (fun γ => γ t) ≤ (C:ℝ≥0∞) • m)
    {f g : X → ℝ} (hf : Integrable f m) (hg : Integrable g m) (t : Time) :
    |(∫ γ, f (γ t) ∂π)-(∫ γ, g (γ t) ∂π)| ≤ C * ∫ x, |f x-g x| ∂m := by
  have hm : Measurable (fun γ : Curve X => γ t) := (continuous_eval_const t).measurable
  have hf' := ((hf.smul_measure ENNReal.coe_ne_top).mono_measure (hC t)).comp_aemeasurable hm.aemeasurable
  have hg' := ((hg.smul_measure ENNReal.coe_ne_top).mono_measure (hC t)).comp_aemeasurable hm.aemeasurable
  dsimp only [Function.comp_def] at hf' hg'
  rw [← integral_sub hf' hg']
  calc
    |∫ γ, f (γ t)-g (γ t) ∂π| ≤ ∫ γ, |f (γ t)-g (γ t)| ∂π := abs_integral_le_integral_abs
    _ = ∫ x, |f x-g x| ∂(π.map (fun γ => γ t)) :=
      (integral_map hm.aemeasurable (((hf.sub hg).abs.smul_measure ENNReal.coe_ne_top).mono_measure (hC t)).1).symm
    _ ≤ ∫ x, |f x-g x| ∂((C:ℝ≥0∞) • m) :=
      integral_mono_measure (hC t) (ae_of_all _ fun x => abs_nonneg _) ((hf.sub hg).abs.smul_measure ENNReal.coe_ne_top)
    _ = _ := by rw [integral_smul_measure]; rfl

lemma IsTestPlan.continuous_integral_eval {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    {f : X → ℝ} (hf : Integrable f m) :
    Continuous (fun t : Time => ∫ γ, f (γ t) ∂π) := by
  let : IsProbabilityMeasure π := hπ.1
  obtain ⟨C,hC⟩ := hπ.2.1
  apply continuous_iff_continuousAt.mpr
  intro s
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0 < ε/(3*((C:ℝ)+1)) := by positivity
  obtain ⟨g,hg,hgi⟩ := hf.exists_boundedContinuous_integral_sub_le hδ
  have hb (t : Time) : |(∫ γ, f (γ t) ∂π)-(∫ γ, g (γ t) ∂π)| ≤ ε/3 := by
    have H := integral_eval_difference_le hC hf hgi t
    have hh : (∫ x, |f x-g x| ∂m) ≤ ε/(3*((C:ℝ)+1)) := by simpa only [Real.norm_eq_abs] using hg
    have hc : (C:ℝ)/(C+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    calc
      _ ≤ C * (ε/(3*((C:ℝ)+1))) := H.trans (mul_le_mul_of_nonneg_left hh C.coe_nonneg)
      _ = ε/3 * ((C:ℝ)/(C+1)) := by field_simp
      _ ≤ ε/3 := by nlinarith
  have hgc : Continuous (fun t : Time => ∫ γ, g (γ t) ∂π) := by
    apply continuous_of_dominated (bound := fun _ => ‖g‖)
    · intro t
      exact (g.continuous.comp (continuous_eval_const t)).aestronglyMeasurable
    · intro t
      exact ae_of_all _ fun γ => g.norm_coe_le_norm (γ t)
    · exact integrable_const _
    · exact ae_of_all _ fun γ => g.continuous.comp γ.continuous
  have hev := (Metric.tendsto_nhds.mp (hgc.continuousAt (x := s))) (ε/3) (by positivity)
  filter_upwards [hev] with t ht
  rw [Real.dist_eq] at ht ⊢
  have H := abs_sub_le (∫ γ, f (γ t) ∂π) (∫ γ, g (γ t) ∂π) (∫ γ, g (γ s) ∂π)
  have J := abs_sub_le (∫ γ, f (γ t) ∂π) (∫ γ, g (γ s) ∂π) (∫ γ, f (γ s) ∂π)
  have hh := hb s
  rw [abs_sub_comm] at hh
  linarith [hb t]

end WeakHessian

end
end InlinedFile0

end OAI
