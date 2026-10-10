import Mathlib
import OAI.Geometry.WeakHessian.Entropy.IntegralDensityMeasureLp'

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology
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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
open WeakHessianFunctional MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]

lemma RelaxedProx.sub_const {u v D : Lp ℝ 2 ν} {t : ℝ} (h : RelaxedProx u t v D) (c : ℝ) :
    RelaxedProx (u-constLp c) t (v-constLp c) D := by
  have hneg : WithLp.toLp 2 (-constLp (m := ν) c,0) ∈ l2RelaxedGraph ν := by
    simpa only [neg_one_smul,abs_neg,abs_one,one_smul,smul_zero] using
      relaxedGraph_hom (-1) (relaxedGraph_const (m := ν) c)
  refine ⟨?_,?_⟩
  · simpa only [add_zero,sub_eq_add_neg] using relaxedGraph_add h.graph hneg
  · intro q E hE
    have H := h.variation (q+constLp c) E (by
      simpa only [add_zero] using relaxedGraph_add hE (relaxedGraph_const (m := ν) c))
    rw [show (u-constLp c)-(v-constLp c)=u-v by abel,
      show q-(v-constLp c)=q+constLp c-v by abel]
    exact H

omit [MetricSpace X] in
lemma centeredLp_mass (u : Lp ℝ 2 ν) :
    (∫ x,(u-constLp (m := ν) (∫ y,u y ∂ν) : Lp ℝ 2 ν) x ∂ν) = 0 := by
  have he : (fun x => (u-constLp (m := ν) (∫ y,u y ∂ν) : Lp ℝ 2 ν) x) =ᵐ[ν]
      fun x => u x-(∫ y,u y ∂ν) := by
    filter_upwards [Lp.coeFn_sub u (constLp (∫ y,u y ∂ν)),constLp_coe (m := ν) (∫ y,u y ∂ν)] with x hx hy
    simp only [hx,Pi.sub_apply,hy]
  rw [integral_congr_ae he,integral_sub ((Lp.memLp u).integrable (by norm_num)) (integrable_const _)]
  simp

omit [MetricSpace X] in
lemma centeredLp_bound {u : Lp ℝ 2 ν} {B : ℝ} (hu : ∀ᵐ x ∂ν,|u x| ≤ B) (c : ℝ) :
    ∀ᵐ x ∂ν,|(u-constLp (m := ν) c : Lp ℝ 2 ν) x| ≤ B+|c| := by
  filter_upwards [Lp.coeFn_sub u (constLp c),constLp_coe (m := ν) c,hu] with x hx hy hu
  simp only [hx,Pi.sub_apply,hy]
  exact (abs_sub _ _).trans (add_le_add hu le_rfl)

variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] [BorelSpace X] {m : Measure X}
lemma CurvatureDimension.prox_weak_pairing {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hν : ν ≪ m)
    {u v D : Lp ℝ 2 ν} {t : ℝ} (h : RelaxedProx u t v D)
    (n : ℕ) (hu : ∀ᵐ x ∂ν,|u x| ≤ (n:ℝ))
    {f W : Lp ℝ 2 ν} (hf : IsLocalWeakUpperGradient ν (f : X → ℝ) (W : X → ℝ)) :
    |⟪f,u-v⟫_ℝ| ≤ t^2*‖D‖*‖W‖ := by
  let c := ∫ x,u x ∂ν
  have H := hcd.prox_weak_pairing_centered hν (h.sub_const c) (centeredLp_mass u)
    (by positivity : 0 ≤ (n:ℝ)+|c|) (centeredLp_bound hu c) (centeredLp_bound (h.bounded n hu) c) hf
  simpa only [sub_sub_sub_cancel_right] using H

lemma CurvatureDimension.prox_gradient_norm_le {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hν : ν ≪ m)
    {u v D W : Lp ℝ 2 ν} {t : ℝ} (h : RelaxedProx u t v D) (ht : t ≠ 0)
    (n : ℕ) (hu : ∀ᵐ x ∂ν,|u x| ≤ (n:ℝ))
    (hf : IsLocalWeakUpperGradient ν (u : X → ℝ) (W : X → ℝ)) : ‖D‖ ≤ ‖W‖ := by
  have H := hcd.prox_weak_pairing hν h n hu hf
  rw [real_inner_comm] at H
  have HS := h.displacement
  have HP : 0 < t^2 := sq_pos_of_ne_zero ht
  have HD : t^2*‖D‖^2 ≤ t^2*(‖D‖*‖W‖) := by
    have HA := le_abs_self ⟪u-v,u⟫_ℝ
    nlinarith [sq_nonneg ‖u-v‖]
  have HN := (mul_le_mul_iff_right₀ HP).mp HD
  nlinarith [norm_nonneg D,norm_nonneg W]
end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
