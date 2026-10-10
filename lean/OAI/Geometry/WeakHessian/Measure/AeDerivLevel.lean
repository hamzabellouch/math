import Mathlib

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
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian

lemma ae_deriv_zero_on_level (q : ℝ → ℝ) (c : ℝ) :
    ∀ᵐ t ∂volume, DifferentiableAt ℝ q t → q t = c → deriv q t = 0 := by
  let s : Set ℝ := {t | q t = c}
  let e : Set ℝ := {t ∈ s | 𝓝[s ∩ Ioi t] t = ⊥}
  have he : e.Countable := countable_setOfPred_isolated_right_within
  have hne : ∀ᵐ t ∂volume, t ∉ e := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using he.measure_zero volume
  filter_upwards [hne] with t ht hdiff hqt
  have hright : (𝓝[s ∩ Ioi t] t).NeBot := by
    rw [neBot_iff]
    exact fun h => ht ⟨hqt,h⟩
  have hacc : AccPt t (𝓟 s) := by
    rw [accPt_principal_iff_nhdsWithin]
    apply hright.mono (nhdsWithin_mono t ?_)
    rintro y ⟨hy,hty⟩
    exact ⟨hy,ne_of_gt hty⟩
  have hzero : HasDerivWithinAt q 0 s t :=
    (hasDerivWithinAt_const t s c).congr (fun _ hx => hx) hqt
  exact (hdiff.hasDerivAt.hasDerivWithinAt.derivWithin hacc.uniqueDiffWithinAt).symm.trans
    (hzero.derivWithin hacc.uniqueDiffWithinAt)

lemma ae_deriv_eq_on_eq (q r : ℝ → ℝ) :
    ∀ᵐ t ∂volume, DifferentiableAt ℝ q t → DifferentiableAt ℝ r t →
      q t = r t → deriv q t = deriv r t := by
  filter_upwards [ae_deriv_zero_on_level (q-r) 0] with t ht hq hr heq
  have hz := ht (hq.sub hr) (by simp only [Pi.sub_apply, heq, sub_self])
  rwa [deriv_sub hq hr, sub_eq_zero] at hz

end WeakHessian

end
end InlinedFile0

end OAI
