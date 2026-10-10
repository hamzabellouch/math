import Mathlib
import OAI.Geometry.WeakHessian.Entropy.MulLogFenchel

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
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X]
variable {m μ : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure μ]

omit [MetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma integrable_exp_of_bounded {f : X → ℝ} (hf : Measurable f) {A : ℝ}
    (hA : ∀ x, f x ≤ A) (ν : Measure X) [IsFiniteMeasure ν] :
    Integrable (fun x => Real.exp (f x)) ν := by
  apply Integrable.of_bound (Real.measurable_exp.comp hf).aestronglyMeasurable (Real.exp A)
  exact ae_of_all _ fun x => by
    simp only [Function.comp_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (hA x)

lemma exists_continuous_fenchel_approx {f : X → ℝ} (hf : Measurable f) {A M : ℝ}
    (hA : ∀ x, ‖f x‖ ≤ A) (hM : 0 < M) (hfM : ∀ x, f x ≤ Real.log M)
    {ε : ℝ} (hε : 0 < ε) : ∃ g : X →ᵇ ℝ,
      (∫ x, f x ∂μ) - (∫ x, Real.exp (f x) ∂m) ≤
        (∫ x, g x ∂μ) - (∫ x, Real.exp (g x) ∂m) + ε := by
  let ν := μ+m
  have hfν : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable A (ae_of_all _ hA)
  let η := ε/(1+M)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨h,hh,_⟩ := hfν.exists_boundedContinuous_integral_sub_le hη
  let g : X →ᵇ ℝ := h ⊓ BoundedContinuousFunction.const X (Real.log M)
  have hg (x : X) : g x = min (h x) (Real.log M) := rfl
  have hfg : Integrable (fun x => ‖f x-g x‖) ν := (hfν.sub (g.integrable ν)).norm
  have hL : (∫ x, ‖f x-g x‖ ∂ν) ≤ η := by
    apply le_trans (integral_mono hfg (hfν.sub (h.integrable ν)).norm ?_) hh
    intro x
    change ‖f x-g x‖ ≤ ‖f x-h x‖
    rw [hg]
    exact min_sub_clamp (hfM x)
  have hμν : μ ≤ ν := Measure.le_add_right le_rfl
  have hmν : m ≤ ν := Measure.le_add_left le_rfl
  have hfμ := hfν.mono_measure hμν
  have hμL : (∫ x, ‖f x-g x‖ ∂μ) ≤ η :=
    (integral_mono_measure hμν (ae_of_all _ fun _ => norm_nonneg _) hfg).trans hL
  have hmL : (∫ x, ‖f x-g x‖ ∂m) ≤ η :=
    (integral_mono_measure hmν (ae_of_all _ fun _ => norm_nonneg _) hfg).trans hL
  have hfirst : (∫ x, f x ∂μ) - (∫ x, g x ∂μ) ≤ η := by
    rw [← integral_sub hfμ (g.integrable μ)]
    exact (le_trans (Real.le_norm_self _) (norm_integral_le_integral_norm _)).trans hμL
  have hgM (x : X) : g x ≤ Real.log M := by rw [hg]; exact min_le_right _ _
  have heF := integrable_exp_of_bounded hf hfM m
  have heG := integrable_exp_of_bounded g.continuous.measurable hgM m
  have heDiff : (∫ x, Real.exp (g x) ∂m) - (∫ x, Real.exp (f x) ∂m) ≤ M*η := by
    calc
      _ = ∫ x, Real.exp (g x)-Real.exp (f x) ∂m := (integral_sub heG heF).symm
      _ ≤ ∫ x, M*‖f x-g x‖ ∂m := by
        apply integral_mono (heG.sub heF) ((hfg.mono_measure hmν).const_mul M)
        intro x
        have H := exp_sub_bound (hgM x) (hfM x)
        rw [Real.exp_log hM,norm_sub_rev (g x)] at H
        exact (le_trans (Real.le_norm_self _) H)
      _ = M*(∫ x, ‖f x-g x‖ ∂m) := integral_const_mul _ _
      _ ≤ M*η := mul_le_mul_of_nonneg_left hmL hM.le
  refine ⟨g,?_⟩
  have H : (1+M)*η = ε := mul_div_cancel₀ ε (by linarith : (1+M) ≠ 0)
  nlinarith

end WeakHessian

end
end InlinedFile0

end OAI
