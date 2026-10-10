import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.TestBochner

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile112
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_core_integrated {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G g ξ : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    (hg : IsTestFunction m g) (hgc : HasCompactSupport g)
    {L T : ℝ≥0} (hF : LipschitzWith L F) (hξ : LipschitzWith T ξ)
    {B C D : ℝ} (hB : ∀ x,|F x| ≤ B) (hC : ∀ x,|ξ x| ≤ C)
    (hG : ∀ x,|G x| ≤ D) (hGc : Continuous G)
    (hξc : HasCompactSupport ξ) (hξ0 : ∀ x,0 ≤ ξ x) {a : ℝ} (ha : 0 ≤ a) :
    (∫ x,Real.exp (a*F x)*ξ x*(K-a*G x)*gamma m g g x ∂m) ≤
      driftBochner m (fun x => a*F x) g ξ := by
  have hq := hrcd.test_gammaHalf_sobolev hN hfull hfin o hg
  have hp := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  apply hHess.core_integrated hfin hp hg hgc hq hF hξ hB hC hG hGc hξc hξ0 ha
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x,|a*F x| ≤ |a| *B := fun x => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg a)
  have hw := lipschitz_exp_bounded hV (fun x => (le_abs_self _).trans (hVB x))
  have hwB : ∀ x,|Real.exp (a*F x)| ≤ Real.exp (|a| *B) := fun x => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hVB x))
  exact hrcd.test_integratedBochner hN hfull hfin o hg (lipschitz_mul_bounded hξ hw hC hwB)
    hξc.mul_right (fun x => mul_nonneg (hξ0 x) (Real.exp_pos _).le)
end WeakHessian

end
end InlinedFile112

end OAI
