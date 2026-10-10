import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.L2MeasureInclusion

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb
variable {Y ι : Type*} [MeasurableSpace Y] [Countable ι]
lemma l2_weighted_density_setIntegral {ν : Measure Y} (u : ι → Lp ℂ 2 ν) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : Summable (fun i => w i * ‖u i‖^2)) (A : Set Y) :
    HasSum (fun i => w i * ∫ y in A, ‖u i y‖^2 ∂ν)
      (∫ y in A, ∑' i, w i * ‖u i y‖^2 ∂ν) := by
  have hi (i : ι) : Integrable (fun y => w i * ‖u i y‖^2) ν :=
    ((Lp.memLp (u i)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).const_mul (w i)
  have hp (i : ι) (y : Y) : 0 ≤ w i * ‖u i y‖^2 := mul_nonneg (hw i) (sq_nonneg _)
  have hn : Summable (fun i => ∫ y in A, ‖w i * ‖u i y‖^2‖ ∂ν) := by
    apply Summable.of_nonneg_of_le (fun index =>
      integral_nonneg (fun point => norm_nonneg (w index * ‖u index point‖^2)))
      (f := fun i => w i * ‖u i‖^2) _ hs
    intro i
    simp only [Real.norm_eq_abs, abs_of_nonneg (hp i _)]
    calc
      (∫ y in A, w i * ‖u i y‖^2 ∂ν) ≤ ∫ y, w i * ‖u i y‖^2 ∂ν :=
        setIntegral_le_integral (hi i) (Filter.Eventually.of_forall (hp i))
      _ = w i * ‖u i‖^2 := by rw [integral_const_mul, ← l2_norm_sq]
  have h := hasSum_integral_of_summable_integral_norm (fun i => (hi i).restrict) hn
  simpa only [integral_const_mul] using h
end Coulomb

end

end OAI
