import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.BoundedDriftRegularity
import OAI.Geometry.WeakHessian.LocalBounds.WeightedGraphInequality

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile180
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_BE {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G u A ξ B : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F)
    {CF Cξ CG CB : ℝ} (hFbounded : ∀ x,|F x| ≤ CF)
    (hGbounded : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (hu : IsLaplacian (exponentialMeasure m (fun x => a*F x)) u A)
    (hAS : Sobolev (exponentialMeasure m (fun x => a*F x)) A)
    (hξA : IsLaplacian (exponentialMeasure m (fun x => a*F x)) ξ B)
    (hξbounded : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hBbounded : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|B x| ≤ CB)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x) :
    (∫ x,(ξ x*(K-a*G x))*gamma (exponentialMeasure m (fun x => a*F x)) u u x
      ∂exponentialMeasure m (fun x => a*F x)) ≤
      (1/2)*(∫ x,B x*gamma (exponentialMeasure m (fun x => a*F x)) u u x
        ∂exponentialMeasure m (fun x => a*F x))-
      ∫ x,ξ x*gamma (exponentialMeasure m (fun x => a*F x)) u A x
        ∂exponentialMeasure m (fun x => a*F x) := by
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
  obtain ⟨ψ,⟨T,hψ⟩,hψe⟩ := hrcd.bounded_weighted_laplacian_lipschitz hN hfull hfin o
    hV hVB hξA hξbounded hBbounded
  have hψB : ∀ x,|ψ x| ≤ Cξ := by
    apply continuous_le_of_ae_le hfull hψ.continuous.abs continuous_const
    apply (Measure.absolutelyContinuous_of_le_smul hm).ae_le
    filter_upwards [hψe,hξbounded] with x hx hb
    rwa [hx]
  have hψ0 : ∀ x,0 ≤ ψ x := by
    apply continuous_le_of_ae_le hfull continuous_const hψ.continuous
    apply (Measure.absolutelyContinuous_of_le_smul hm).ae_le
    filter_upwards [hψe,hξ0] with x hx hb
    rwa [hx]
  have hψA := hξA.congr_ae hψe.symm EventuallyEq.rfl
  have H := hHess.rcd_weighted_graph_inequality hN hrcd hfull hfin o hF hψ
    hFbounded hψB hGbounded hGc hψ0 ha hu hψA hBbounded
  rw [graphBochner_eq_BE hnfin hnpar hu hAS hψ hψB] at H
  have e1 : (∫ x,(ψ x*(K-a*G x))*gamma ν u u x ∂ν) =
      ∫ x,(ξ x*(K-a*G x))*gamma ν u u x ∂ν := by
    apply integral_congr_ae
    filter_upwards [hψe] with x hx
    rw [hx]
  have e2 : (∫ x,ψ x*gamma ν u A x ∂ν) = ∫ x,ξ x*gamma ν u A x ∂ν := by
    apply integral_congr_ae
    filter_upwards [hψe] with x hx
    rw [hx]
  change (∫ x,(ψ x*(K-a*G x))*gamma ν u u x ∂ν) ≤
    (1/2)*(∫ x,B x*gamma ν u u x ∂ν)-(∫ x,ψ x*gamma ν u A x ∂ν) at H
  rw [e1,e2] at H
  exact H
end WeakHessian

end
end InlinedFile180

end OAI
