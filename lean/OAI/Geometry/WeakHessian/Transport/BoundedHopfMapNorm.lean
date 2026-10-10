import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.UpperGradientTendstoNorm
import OAI.Geometry.WeakHessian.Transport.BoundedHopfMapLipschitz

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
namespace WeakHessianTransport
open WeakHessian MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] [TopologicalSpace.SeparableSpace X] in
lemma boundedHopfMap_norm_le (f : X →ᵇ ℝ) (t : ℝ) : ‖boundedHopfMap f t‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  by_cases ht : 0 < t
  · rw [boundedHopfMap_apply_pos f ht,Real.norm_eq_abs]
    exact abs_le.mpr ⟨lower_le_hopfLax (fun x => (boundedContinuous_bounds f x).1) ht x,
      (hopfLax_le_self (fun x => (boundedContinuous_bounds f x).1) ht x).trans (boundedContinuous_bounds f x).2⟩
  · simpa only [boundedHopfMap,dite_eq_right ht] using f.norm_coe_le_norm x

omit [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma integral_bounded_pairing_diff_bound {u v : X → ℝ} (hu : Integrable u m)
    (hv : Integrable v m) (q r : X →ᵇ ℝ) :
    ‖(∫ x,v x*r x ∂m)-(∫ x,u x*q x ∂m)‖ ≤
      ‖r-q‖*(∫ x,‖v x‖ ∂m)+‖q‖*(∫ x,‖v x-u x‖ ∂m) := by
  have he : (∫ x,v x*r x ∂m)-(∫ x,u x*q x ∂m) =
      (∫ x,v x*(r-q) x ∂m)+(∫ x,(v x-u x)*q x ∂m) := by
    rw [integral_bounded_pairing_sub_right hv,integral_bounded_pairing_sub_left hu hv]
    ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (norm_integral_bounded_pairing hv _)
    (norm_integral_bounded_pairing (hv.sub hu) q))

omit [TopologicalSpace.SeparableSpace X] in
lemma hopf_L1_lipschitz (f : X →ᵇ ℝ) {ρ : ℝ → X → ℝ}
    (hi : ∀ s,0 ≤ s → Integrable (ρ s) m) {M C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hm : ∀ s,0 ≤ s → (∫ x,‖ρ s x‖ ∂m) ≤ M)
    (hLip : ∀ s t,0 ≤ s → 0 ≤ t → (∫ x,‖ρ t x-ρ s x‖ ∂m) ≤ C*|t-s|)
    {a : ℝ} (ha : 0 < a) :
    LipschitzOnWith ⟨(2*‖f‖/a)*M+‖f‖*C,by positivity⟩
      (fun s => ∫ x,ρ s x*boundedHopfMap f s x ∂m) (Ici a) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht s hs
  have ht0 : 0 ≤ t := ha.le.trans ht
  have hs0 : 0 ≤ s := ha.le.trans hs
  have hq := (boundedHopfMap_time_lipschitz f ha).dist_le_mul t ht s hs
  change dist (boundedHopfMap f t) (boundedHopfMap f s) ≤ (2*‖f‖/a)*dist t s at hq
  rw [dist_eq_norm,Real.dist_eq] at hq
  have H := integral_bounded_pairing_diff_bound (hi s hs0) (hi t ht0) (boundedHopfMap f s) (boundedHopfMap f t)
  have hb (r : ℝ) : 0 ≤ ∫ x,‖ρ r x‖ ∂m := integral_nonneg fun x => norm_nonneg _
  have h1 := mul_le_mul hq (hm t ht0) (hb _) (by positivity : 0 ≤ (2*‖f‖/a)*|t-s|)
  have h2 := mul_le_mul (boundedHopfMap_norm_le f s) (hLip s t hs0 ht0)
    (integral_nonneg fun x => norm_nonneg _) (norm_nonneg f)
  have H' := H.trans (add_le_add h1 h2)
  change ‖(∫ x,ρ t x*boundedHopfMap f t x ∂m)-(∫ x,ρ s x*boundedHopfMap f s x ∂m)‖ ≤
    ((2*‖f‖/a)*M+‖f‖*C)*|t-s|
  calc
    _ ≤ ((2*‖f‖/a)*|t-s|)*M+‖f‖*(C*|t-s|) := H'
    _ = _ := by ring
end WeakHessianTransport
end
end InlinedFile0

end OAI
