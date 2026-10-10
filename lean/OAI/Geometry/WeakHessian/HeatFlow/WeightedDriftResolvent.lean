import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.BoundedDriftFixedPoint

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile152
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.bounded_drift_resolvent {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    {τ : ℝ} (hτ : 0 < τ) (hL2 : (L:ℝ)*Real.sqrt τ < 1)
    (hLinf : 5*(L:ℝ)*Real.exp (|K| *τ)*Real.sqrt τ ≤ 1/2)
    (u : Lp ℝ 2 m) {B : ℝ} (hB : 0 ≤ B) (hu : ∀ᵐ x ∂m,|u x| ≤ B) :
    ∃ r : Lp ℝ 2 m,∃ g : X → ℝ,GloballyLipschitz g ∧ g =ᵐ[m] r ∧
      IsLaplacian (exponentialMeasure m V) r (fun x => τ⁻¹*r x-u x) := by
  let h := hrcd.2
  obtain ⟨w,hw,hwb⟩ := hrcd.drift_fixedPoint hN hfull hfin h o hV hτ hL2 hLinf u hB hu
  let r := driftResolvent h hτ w
  let P := hrcd.1.driftPerturbation hfin h o hV hτ
  obtain ⟨g,hg,he⟩ := hrcd.cheeger_resolvent_lipschitz hN hfull hfin h o w
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hB) hwb hτ
  have hr := hrcd.1.driftResolvent_isLaplacian hfin h o hτ w
  have hrw := hr.reweight hfin (hrcd.1.global_localGradientParallelogram hfin o h) hV hBV
  have hea : (fun x => (τ⁻¹ • r-w : Lp ℝ 2 m) x+gamma m V r x) =ᵐ[m]
      (fun x => τ⁻¹*r x-u x) := by
    have hw' : w = u+P w := hw
    filter_upwards [Lp.coeFn_sub (τ⁻¹ • r) w,Lp.coeFn_smul τ⁻¹ r,
      Lp.coeFn_add u (P w),hrcd.1.driftPerturbation_ae hfin h o hV hτ w] with x ha hb hc hd
    rw [ha]
    change (τ⁻¹ • r) x-w x+gamma m V r x = _
    rw [hb]
    change τ⁻¹*r x-w x+gamma m V r x = _
    have hwx : w x=u x+gamma m V r x := by
      calc
        w x = (u+P w) x := congrArg (fun q : Lp ℝ 2 m => q x) hw'
        _ = u x+P w x := hc
        _ = _ := by rw [hd]
    rw [hwx]
    ring
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hBV
  refine ⟨r,g,⟨_,hg⟩,he,?_⟩
  exact hrw.congr_ae EventuallyEq.rfl ((Measure.absolutelyContinuous_of_le_smul hν).ae_le hea)
end WeakHessian

end
end InlinedFile152

end OAI
