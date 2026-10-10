import Mathlib
import OAI.Geometry.WeakHessian.Entropy.FisherEpsilon

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
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

noncomputable def reducedEntropy (x : ℝ) : ℝ := x*Real.log x-x

lemma renormalizedEntropy_tendsto {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => renormalizedEntropy (fisherEpsilon n) x) atTop (𝓝 (reducedEntropy x)) := by
  have h1 := Real.continuous_mul_log.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := x)).add fisherEpsilon_tendsto)
  have h2 := Real.continuous_mul_log.continuousAt.tendsto.comp fisherEpsilon_tendsto
  convert! (h1.sub h2).sub_const x using 1
  · ext n
    exact renormalizedEntropy_eq (fisherEpsilon_pos n) hx
  · simp only [reducedEntropy,add_zero,zero_mul,sub_zero]

lemma reducedEntropy_lower {x w : ℝ} (hx : 0 ≤ x) (hw : 0 < w) :
    x*Real.log w-w ≤ reducedEntropy x :=
  ge_of_tendsto (renormalizedEntropy_tendsto hx)
    (Eventually.of_forall (fun n => renormalizedEntropy_lower (fisherEpsilon_pos n) hx hw))

lemma reducedEntropy_upper {x : ℝ} (hx : 0 ≤ x) : reducedEntropy x ≤ x^2/2 :=
  le_of_tendsto (renormalizedEntropy_tendsto hx)
    (Eventually.of_forall (fun n => renormalizedEntropy_upper (fisherEpsilon_pos n) (fisherEpsilon_le_one n) hx))

lemma renormalizedEntropy_abs_bound {a x V : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hx : 0 ≤ x) :
    |renormalizedEntropy a x| ≤ x^2/2+|x*V|+Real.exp (-V) := by
  have hl := renormalizedEntropy_lower ha hx (Real.exp_pos (-V))
  rw [Real.log_exp,mul_neg] at hl
  have hu := renormalizedEntropy_upper ha ha1 hx
  exact abs_le.mpr ⟨by linarith [le_abs_self (x*V),sq_nonneg x],
    by linarith [abs_nonneg (x*V),Real.exp_pos (-V)]⟩

lemma reducedEntropy_abs_bound {x V : ℝ} (hx : 0 ≤ x) :
    |reducedEntropy x| ≤ x^2/2+|x*V|+Real.exp (-V) :=
  le_of_tendsto ((renormalizedEntropy_tendsto hx).abs)
    (Eventually.of_forall (fun n => renormalizedEntropy_abs_bound (fisherEpsilon_pos n) (fisherEpsilon_le_one n) hx))

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma integrable_reducedEntropy {u V : X → ℝ} (hu : MemLp u 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hUV : Integrable (fun x => u x*V x) m)
    (hV : Integrable (fun x => Real.exp (-V x)) m) :
    Integrable (fun x => reducedEntropy (u x)) m := by
  apply (((hu.integrable_sq.div_const 2).add hUV.norm).add hV).mono'
    ((Real.continuous_mul_log.sub continuous_id).comp_aestronglyMeasurable hu.aestronglyMeasurable)
  filter_upwards [hun] with x hx
  simpa only [Real.norm_eq_abs,Pi.add_apply,reducedEntropy,Pi.sub_apply,id_eq] using! reducedEntropy_abs_bound (V := V x) hx

lemma tendsto_integral_renormalizedEntropy {u V : X → ℝ} (hu : MemLp u 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hUV : Integrable (fun x => u x*V x) m)
    (hV : Integrable (fun x => Real.exp (-V x)) m) :
    Tendsto (fun n => ∫ x,renormalizedEntropy (fisherEpsilon n) (u x) ∂m) atTop
      (𝓝 (∫ x,reducedEntropy (u x) ∂m)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => u x^2/2+‖u x*V x‖+Real.exp (-V x))
  · intro n
    exact (continuous_iff_continuousAt.mpr fun y =>
      (renormalizedEntropy_hasDeriv (fisherEpsilon_pos n) y).continuousAt).comp_aestronglyMeasurable hu.aestronglyMeasurable
  · exact ((hu.integrable_sq.div_const 2).add hUV.norm).add hV
  · intro n
    filter_upwards [hun] with x hx
    simpa only [Real.norm_eq_abs] using renormalizedEntropy_abs_bound (V := V x)
      (fisherEpsilon_pos n) (fisherEpsilon_le_one n) hx
  · exact hun.mono (fun x hx => renormalizedEntropy_tendsto hx)
end WeakHessian

end
end InlinedFile0

end OAI
