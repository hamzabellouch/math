import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.BoundedMulLp
import OAI.Geometry.WeakHessian.Measure.AeNonnegCompactIntegral

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
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

omit [BorelSpace X] in
lemma norm_minimal_relaxedGradient_inner {f D E : Lp ℝ 2 m}
    (hD : WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m)
    (hmin : ∀ E : Lp ℝ 2 m, WithLp.toLp 2 (f,E) ∈ l2RelaxedGraph m → ‖D‖ ≤ ‖E‖)
    (hE : WithLp.toLp 2 (f,E) ∈ l2RelaxedGraph m) :
    0 ≤ ⟪D,E-D⟫_ℝ := by
  let S : Set (Lp ℝ 2 m) := {E | WithLp.toLp 2 (f,E) ∈ l2RelaxedGraph m}
  have hSc : Convex ℝ S := by
    intro A hA B hB a b ha hb hab
    have H := convex_l2RelaxedGraph (m := m) hA hB ha hb hab
    change WithLp.toLp 2 (a • f+b • f,a • A+b • B) ∈ l2RelaxedGraph m at H
    rwa [← add_smul,hab,one_smul] at H
  have : Nonempty S := ⟨⟨D,hD⟩⟩
  have hn : ‖(0 : Lp ℝ 2 m)-D‖ = ⨅ w : S, ‖(0 : Lp ℝ 2 m)-w‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro w
      simpa only [zero_sub,norm_neg] using hmin w w.property
    · exact ciInf_le ⟨0,by rintro _ ⟨w,rfl⟩; exact norm_nonneg _⟩ (⟨D,hD⟩ : S)
  have H := (norm_eq_iInf_iff_real_inner_le_zero hSc hD).mp hn E hE
  simpa only [zero_sub,inner_neg_left,neg_nonpos] using H

lemma pointwise_minimal_relaxedGradient [ProperSpace X] [TopologicalSpace.SeparableSpace X]
    (hfinite : FiniteOnBoundedSets m) {f D E : Lp ℝ 2 m}
    (hD : WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m)
    (hmin : ∀ E : Lp ℝ 2 m, WithLp.toLp 2 (f,E) ∈ l2RelaxedGraph m → ‖D‖ ≤ ‖E‖)
    (hE : WithLp.toLp 2 (f,E) ∈ l2RelaxedGraph m) : ∀ᵐ x ∂m, D x ≤ E x := by
  have hi : Integrable (fun x => D x*(E x-D x)) m :=
    (Lp.memLp D).integrable_mul ((Lp.memLp E).sub (Lp.memLp D))
  have hpos : ∀ᵐ x ∂m, 0 ≤ D x*(E x-D x) := by
    apply WeakHessianCalculus.ae_nonneg_of_integral_lipschitz_compact hi
    intro φ hc hφ hφ0 hφ1
    have hB : ∀ᵐ x ∂m, |φ x| ≤ 1 := ae_of_all _ fun x => by
      rw [abs_of_nonneg (hφ0 x)]; exact hφ1 x
    let T := boundedMulLp hφ.choose_spec.continuous.aestronglyMeasurable hB
    have hm := relaxedGradient_mix hφ hc hφ0 hφ1 hB hE hD
    have H := norm_minimal_relaxedGradient_inner hD hmin hm
    change 0 ≤ ⟪D,T E+D-T D-D⟫_ℝ at H
    rw [show T E+D-T D-D = T (E-D) by rw [map_sub]; abel] at H
    rw [L2.inner_def] at H
    convert H using 1
    apply integral_congr_ae
    filter_upwards [boundedMulLp_ae hφ.choose_spec.continuous.aestronglyMeasurable hB (E-D),
      Lp.coeFn_sub E D] with x hx hy
    change D x*(E x-D x)*φ x = (T (E-D)) x*D x
    change _ = (boundedMulLp hφ.choose_spec.continuous.aestronglyMeasurable hB (E-D)) x*D x
    rw [hx,hy,Pi.sub_apply]
    ring
  have hDn := (relaxedGraph_isUpperGradient hfinite (p := WithLp.toLp 2 (f,D)) hD).2.1
  have hEn := (relaxedGraph_isUpperGradient hfinite (p := WithLp.toLp 2 (f,E)) hE).2.1
  filter_upwards [hpos,hDn,hEn] with x hx hd he
  change 0 ≤ D x at hd
  change 0 ≤ E x at he
  by_cases hzero : D x = 0
  · rwa [hzero]
  · have hp : 0 < D x := lt_of_le_of_ne hd (Ne.symm hzero)
    exact sub_nonneg.mp ((nonneg_of_mul_nonneg_right hx hp))
end WeakHessian

end
end InlinedFile0

end OAI
