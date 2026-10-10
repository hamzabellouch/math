import Mathlib
import OAI.Geometry.CAT0Fillings.Prism.Mass
import OAI.Geometry.CAT0Fillings.Prism.TimeCoordinate

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings
open Set MeasureTheory

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
omit [BorelSpace X] [Nonempty X] in
lemma IsMetricCurrent.compactlySupported_of_compact {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) : CompactlySupported T := by
  refine ⟨univ,isCompact_univ,?_⟩
  intro b π hab hb
  have hzero : b = 0 := funext (fun x => hb x (mem_univ x))
  rw [hzero]
  change T (fun _ => 0) π = 0
  simpa using hT.linearFirst (fun _ => 0) (fun _ => 0) π 0 0
    (BoundedLip.const 0) (BoundedLip.const 0) hab.2

end CAT0Fillings

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

end CAT0Fillings

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable
open BorelCoefficients


attribute [local instance] Classical.propDecidable
open Set Metric
open scoped NNReal

end CAT0Fillings

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma ae_prism_jacobian_bound_mixed (π : Fin (k+1) → ℝ × X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) (R : ℝ≥0)
    (ht : ∀ i x, LipschitzWith R (fun t : ℝ => π i (t,x))) :
    ∀ᵐ p ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain),
      |C.prism.jacobian π ((Prism.split k).symm p)| ≤
        (R:ℝ) * ∑ i : Fin (k+1), |C.jacobian (fun j x => π (i.succAbove j) (p.1,x)) p.2| := by
  have hpz := Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Icc (0:ℝ) 1)) |>.ae
    (ae_restrict_mem (μ := volume) C.borel)
  filter_upwards [C.ae_prism_jacobian_decompose π hπ,hpz] with p hd hz
  rw [hd,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hl : LipschitzWith R (fun t => C.scalar (fun x => π i (t,x)) p.2) := by
    have heq : (fun t => C.scalar (fun x => π i (t,x)) p.2) =
        (fun t => π i (t,C.param ⟨p.2,hz⟩)) := funext fun _ => C.scalar_eq hz
    rw [heq]
    exact ht i _
  have hD : |deriv (fun t => C.scalar (fun x => π i (t,x)) p.2) p.1| ≤ R := by
    simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz hl
  simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
  exact mul_le_mul_of_nonneg_right hD (abs_nonneg _)

lemma prism_action_bound_mixed {ν : Measure X} [IsFiniteMeasure ν] (hν : Controls C.action ν)
    (b : ℝ × X → ℝ) (π : Fin (k+1) → ℝ × X → ℝ) (hab : Admissible b π)
    (R : ℝ≥0) (ht : ∀ i x, LipschitzWith R (fun t : ℝ => π i (t,x)))
    (hs : ∀ i t, LipschitzWith 1 (fun x : X => π i (t,x))) :
    |C.prism.action b π| ≤ ((k+1:ℝ)*(R:ℝ)) *
      ∫ p : ℝ × X, |b p| ∂(volume.restrict (Icc (0:ℝ) 1)).prod ν := by
  let F (i : Fin (k+1)) (p : ℝ × Euc k) :=
    |(C.multiplicity p.2 : ℝ) * C.scalar (fun x => b (p.1,x)) p.2 *
      C.jacobian (fun j x => π (i.succAbove j) (p.1,x)) p.2|
  have hF (i : Fin (k+1)) : Integrable (F i)
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)) :=
    (C.integrable_prism_slice b (fun j => π (i.succAbove j))
      ⟨hab.1,fun j => hab.2 _⟩).abs
  have hib : Integrable (fun p : ℝ × X => |b p|)
      ((volume.restrict (Icc (0:ℝ) 1)).prod ν) := by
    obtain ⟨M,hM⟩ := hab.1.2
    exact Integrable.of_bound hab.1.continuous.abs.aestronglyMeasurable M
      (Eventually.of_forall fun p => by simpa using hM p)
  have hinner (i : Fin (k+1)) :
      (∫ p, F i p ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)) ≤
      ∫ p : ℝ × X, |b p| ∂(volume.restrict (Icc (0:ℝ) 1)).prod ν := by
    rw [integral_prod _ (hF i),integral_prod _ hib]
    apply integral_mono_ae (hF i).integral_prod_left hib.integral_prod_left
    exact Eventually.of_forall fun t => C.chart_abs_integrand_le hν
      (boundedLip_slice hab.1 t) (fun j => hs (i.succAbove j) t)
  rw [C.prism_action_eq b π hab]
  calc
    _ ≤ ∫ p, |(C.multiplicity p.2 : ℝ)*C.scalar (fun x => b (p.1,x)) p.2*
        C.prism.jacobian π ((Prism.split k).symm p)|
        ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain) := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)))
        (fun p => (C.multiplicity p.2 : ℝ)*C.scalar (fun x => b (p.1,x)) p.2*
          C.prism.jacobian π ((Prism.split k).symm p))
    _ ≤ ∫ p, (R:ℝ)*∑ i, F i p
        ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain) := by
      apply integral_mono_ae (C.integrable_prism_formula b π hab).abs
        ((integrable_finsetSum _ fun i _ => hF i).const_mul _)
      filter_upwards [C.ae_prism_jacobian_bound_mixed π hab.2 R ht] with p hp
      have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg
        (abs_nonneg ((C.multiplicity p.2 : ℝ))) (abs_nonneg (C.scalar (fun x => b (p.1,x)) p.2)))
      simpa only [F,abs_mul,←Finset.mul_sum,mul_assoc,mul_comm,mul_left_comm] using hh
    _ = (R:ℝ)*∑ i, ∫ p, F i p
        ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain) := by
      rw [integral_const_mul,integral_finsetSum _ fun i _ => hF i]
    _ ≤ (R:ℝ)*∑ _i : Fin (k+1), ∫ p : ℝ × X, |b p|
        ∂(volume.restrict (Icc (0:ℝ) 1)).prod ν :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hinner i) R.coe_nonneg
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin, nsmul_eq_mul]; push_cast; ring

end CAT0Fillings.IntegerChart
end
end

end OAI
