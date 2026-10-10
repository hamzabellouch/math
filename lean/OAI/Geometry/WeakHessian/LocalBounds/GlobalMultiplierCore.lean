import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ActualCore
import OAI.Geometry.WeakHessian.Calculus.DriftRadialLimit

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile177
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_global_multiplier_core {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G g ξ : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    (hg : IsTestFunction m g) (hgc : HasCompactSupport g)
    {L T : ℝ≥0} (hF : LipschitzWith L F) (hξ : LipschitzWith T ξ)
    {B C D : ℝ} (hB : ∀ x,|F x| ≤ B) (hC : ∀ x,|ξ x| ≤ C)
    (hG : ∀ x,|G x| ≤ D) (hGc : Continuous G)
    (hξS : Sobolev m ξ) (hξ0 : ∀ x,0 ≤ ξ x) {a : ℝ} (ha : 0 ≤ a) :
    (∫ x,Real.exp (a*F x)*ξ x*(K-a*G x)*gamma m g g x ∂m) ≤
      driftBochner m (fun x => a*F x) g ξ := by
  have hpar := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  have hq := hrcd.test_gammaHalf_sobolev hN hfull hfin o hg
  have hgs := (laplacian_isLaplacian hg.1).1
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x,|a*F x| ≤ |a| *B := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg a)
  have hw := (Real.continuous_exp.comp hV.continuous).aestronglyMeasurable (μ := m)
  have hwB : ∀ᵐ x ∂m, ‖Real.exp (a*F x)‖ ≤ Real.exp (|a| *B) := ae_of_all _ fun x => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hVB x))
  have hk : Continuous (fun x => K-a*G x) := continuous_const.sub (continuous_const.mul hGc)
  have hkB : ∀ᵐ x ∂m, ‖K-a*G x‖ ≤ |K| + |a| *|D| := ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]
    calc
      |K-a*G x| ≤ |K|+|a*G x| := abs_sub _ _
      _ = |K|+|a| *|G x| := by rw [abs_mul]
      _ ≤ |K|+|a| *|D| := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left ((hG x).trans (le_abs_self _)) (abs_nonneg a))
  have hi : Integrable (fun x => Real.exp (a*F x)*ξ x*(K-a*G x)*gamma m g g x) m := by
    simpa only [mul_assoc,Function.comp_apply,Pi.mul_apply] using (((integrable_gamma hfin hgs hgs).bdd_mul
      hk.aestronglyMeasurable hkB).bdd_mul hξ.continuous.aestronglyMeasurable
        (by simpa only [Real.norm_eq_abs] using ae_of_all m hC)).bdd_mul hw hwB
  have hcB (n : ℕ) (x : X) : |radialCutoff o n x| ≤ 1 := by
    rw [abs_of_nonneg (radialCutoff_nonneg o n x)]; exact radialCutoff_le_one o n x
  have hcutL (n : ℕ) := lipschitz_mul_bounded hξ (radialCutoff_lipschitz o n) hC (hcB n)
  have hcutB (n : ℕ) (x : X) : |ξ x*radialCutoff o n x| ≤ C := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hcB n x) (abs_nonneg _)).trans (by simpa using hC x)
  have he (n : ℕ) : (∫ x,Real.exp (a*F x)*(ξ x*radialCutoff o n x)*(K-a*G x)*gamma m g g x ∂m) =
      ∫ x,(Real.exp (a*F x)*ξ x*(K-a*G x)*gamma m g g x)*radialCutoff o n x ∂m := by
    congr 1; funext x; ring
  have hbound (n : ℕ) : (∫ x,(Real.exp (a*F x)*ξ x*(K-a*G x)*gamma m g g x)*radialCutoff o n x ∂m) ≤
      driftBochner m (fun x => a*F x) g (fun x => ξ x*radialCutoff o n x) := by
    rw [← he]
    exact hHess.rcd_core_integrated hN hrcd hfull hfin o hg hgc hF (hcutL n)
      hB (hcutB n) hG hGc ((radialCutoff_compact o n).mul_left)
      (fun x => mul_nonneg (hξ0 x) (radialCutoff_nonneg o n x)) ha
  exact le_of_tendsto_of_tendsto (integral_radialCutoff_tendsto o hi)
    (driftBochner_radialCutoff_tendsto hfin hpar o hg hq hV hξ hVB hC hξS)
    (Eventually.of_forall hbound)
end WeakHessian

end
end InlinedFile177

end OAI
