import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.GlobalMultiplierCore
import OAI.Geometry.WeakHessian.LocalBounds.OriginalCoreProducer

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile179
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_graph_inequality {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G u A ξ B : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L T : ℝ≥0} (hF : LipschitzWith L F) (hξ : LipschitzWith T ξ)
    {CF Cξ CG CB : ℝ} (hFbounded : ∀ x,|F x| ≤ CF) (hξbounded : ∀ x,|ξ x| ≤ Cξ)
    (hGbounded : ∀ x,|G x| ≤ CG) (hGc : Continuous G)
    (hξ0 : ∀ x,0 ≤ ξ x) {a : ℝ} (ha : 0 ≤ a)
    (hu : IsLaplacian (exponentialMeasure m (fun x => a*F x)) u A)
    (hξA : IsLaplacian (exponentialMeasure m (fun x => a*F x)) ξ B)
    (hBbounded : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|B x| ≤ CB) :
    (∫ x,(ξ x*(K-a*G x))*gamma (exponentialMeasure m (fun x => a*F x)) u u x
      ∂exponentialMeasure m (fun x => a*F x)) ≤
      graphBochner (exponentialMeasure m (fun x => a*F x)) u A ξ B := by
  have hpar := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFbounded x) (abs_nonneg a)
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hVB
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal) hν
  have hnpar := hpar.change_measure (C := (Real.exp (|a| *CF)).toNNReal)
    (D := (Real.exp (|a| *CF)).toNNReal) hm hν
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hξS : Sobolev m ξ := (sobolev_exponentialMeasure_iff hVB ξ).mpr hξA.1
  obtain ⟨gs,hgs,hgc,hut,hAt⟩ := (hrcd.originalTestGraphCore hN hfull hfin o).reweight_approx
    hfin hpar hV hVB hu
  have hk : Continuous (fun x => ξ x*(K-a*G x)) :=
    hξ.continuous.mul (continuous_const.sub (continuous_const.mul hGc))
  have hkBound : ∀ᵐ x ∂ν,|ξ x*(K-a*G x)| ≤ |Cξ| *(|K| + |a| *|CG|) := ae_of_all _ fun x => by
    have ht : |K-a*G x| ≤ |K| + |a| *|CG| := by
      calc
        |K-a*G x| ≤ |K|+|a*G x| := abs_sub _ _
        _ = |K|+|a| *|G x| := by rw [abs_mul]
        _ ≤ |K|+|a| *|CG| := add_le_add le_rfl
          (mul_le_mul_of_nonneg_left ((hGbounded x).trans (le_abs_self _)) (abs_nonneg a))
    rw [abs_mul]
    exact mul_le_mul ((hξbounded x).trans (le_abs_self _)) ht (abs_nonneg _) (abs_nonneg _)
  apply graphBochner_bound_of_approx hnfin hnpar
    (fun n => (laplacian_isLaplacian (hgs n).1).reweight hfin hpar hV hVB) hu
    hξ hξbounded hξA.2.1.aestronglyMeasurable hBbounded hk.aestronglyMeasurable hkBound hut hAt
  intro n
  rw [graphBochner_reweight_eq_drift hfin hpar (hgs n)
    (hrcd.test_gammaHalf_sobolev hN hfull hfin o (hgs n)) hV hξ hVB hξbounded hξA]
  have he : (∫ x,(ξ x*(K-a*G x))*gamma ν (gs n) (gs n) x ∂ν) =
      ∫ x,Real.exp (a*F x)*ξ x*(K-a*G x)*gamma m (gs n) (gs n) x ∂m := by
    rw [integral_exponentialMeasure hV.continuous.aemeasurable]
    apply integral_congr_ae
    filter_upwards [gamma_exponentialMeasure (m := m) hVB (gs n) (gs n)] with x hx
    change gamma m (gs n) (gs n) x = gamma ν (gs n) (gs n) x at hx
    rw [← hx]; ring
  rw [he]
  exact hHess.rcd_global_multiplier_core hN hrcd hfull hfin o (hgs n) (hgc n) hF hξ
    hFbounded hξbounded hGbounded hGc hξS hξ0 ha
end WeakHessian

end
end InlinedFile179

end OAI
