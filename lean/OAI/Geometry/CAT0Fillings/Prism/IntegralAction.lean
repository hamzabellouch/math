import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.BorelAction
import OAI.Geometry.CAT0Fillings.Calculus.LipschitzFTC
import OAI.Geometry.CAT0Fillings.Charts.MultiplicityRestriction
import OAI.Geometry.CAT0Fillings.Prism.Action

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

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Measure Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)
omit [CompactSpace X] in
lemma integrable_prism_minor_derivative (v : Fin (k+1) → ℝ × X → ℝ) (K : ℝ≥0)
    (hv : ∀ i, LipschitzWith K (v i)) (i : Fin (k+1)) :
    Integrable (fun p : ℝ × Euc k => (C.multiplicity p.2 : ℝ) *
      C.jacobian (fun j x => v (i.succAbove j) (p.1,x)) p.2 *
      deriv (fun s => v i (s,C.paramExtended p.2)) p.1)
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)) := by
  have hi := C.integrable_prism_slice (fun _ => 1) (fun j => v (i.succAbove j))
    ⟨BoundedLip.const 1,fun j => ⟨K,hv _⟩⟩
  have hi' : Integrable (fun p : ℝ × Euc k => (C.multiplicity p.2 : ℝ) *
      C.jacobian (fun j x => v (i.succAbove j) (p.1,x)) p.2)
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)) := by
    apply hi.congr
    have hz := (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Icc (0:ℝ) 1))).ae
        (ae_restrict_mem (μ := volume) C.borel)
    filter_upwards [hz] with p hp
    rw [C.scalar_eq hp]
    simp
  have hm : Measurable (fun p : ℝ × Euc k =>
      deriv (fun s => v i (s,C.paramExtended p.2)) p.1) :=
    (measurable_timeDeriv (hv i).continuous).comp
      (measurable_fst.prodMk (C.measurable_paramExtended.comp measurable_snd))
  exact hi'.mul_bdd hm.aestronglyMeasurable
    (Eventually.of_forall fun p => norm_deriv_le_of_lipschitz
      (CAT0Fillings.lipschitz_time (hv i) (C.paramExtended p.2)))

lemma prism_action_one_eq_integral (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : Controls C.action μ) (v : Fin (k+1) → ℝ × X → ℝ) (K : ℝ≥0)
    (hv : ∀ i, LipschitzWith K (v i)) :
    C.prism.action (fun _ => 1) v =
      ∫ t in (0:ℝ)..1, ∑ i, (-1:ℝ)^i.val *
        BorelCoefficients.borelAction μ C.action_isMetricCurrent
          (fun x => deriv (fun s => v i (s,x)) t)
          (fun j x => v (i.succAbove j) (t,x)) := by
  let F (i : Fin (k+1)) (p : ℝ × Euc k) : ℝ :=
    (C.multiplicity p.2 : ℝ) * C.jacobian (fun j x => v (i.succAbove j) (p.1,x)) p.2 *
      deriv (fun s => v i (s,C.paramExtended p.2)) p.1
  have hFi i : Integrable (F i)
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)) :=
    C.integrable_prism_minor_derivative v K hv i
  have hF : Integrable (fun p => ∑ i, (-1:ℝ)^i.val * F i p)
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)) :=
    integrable_finsetSum _ (fun i _ => (hFi i).const_mul _)
  have hi (t i) : BorelCoefficients.borelAction μ C.action_isMetricCurrent
      (fun x => deriv (fun s => v i (s,x)) t) (fun j x => v (i.succAbove j) (t,x)) =
      ∫ z, F i (t,z) ∂volume.restrict C.domain := by
    apply C.borelAction_eq_integral C.action_isMetricCurrent hμ
      ((measurable_timeDeriv (hv i).continuous).comp (measurable_const.prodMk measurable_id))
      ⟨K,fun x => norm_deriv_le_of_lipschitz
        (CAT0Fillings.lipschitz_time (hv i) x)⟩
      _ (fun j => ⟨K,CAT0Fillings.lipschitz_slice (hv _) t⟩)
  rw [C.prism_action_eq (fun _ => 1) v ⟨BoundedLip.const 1,fun i => ⟨K,hv i⟩⟩]
  calc
    _ = ∫ p, ∑ i, (-1:ℝ)^i.val * F i p
        ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain) := by
      apply integral_congr_ae
      have hz := (Measure.quasiMeasurePreserving_snd
        (μ := volume.restrict (Icc (0:ℝ) 1))).ae (ae_restrict_mem (μ := volume) C.borel)
      filter_upwards [C.ae_prism_jacobian_decompose v (fun i => ⟨K,hv i⟩),hz] with p hp hz
      rw [C.scalar_eq hz,hp,mul_one,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have he : (fun t => C.scalar (fun x => v i (t,x)) p.2) =
          (fun t => v i (t,C.paramExtended p.2)) := by
        funext t
        simp only [C.scalar_eq hz,paramExtended,dite_eq_left hz]
      rw [he]
      dsimp [F]
      ring
    _ = ∫ t, ∫ z, ∑ i, (-1:ℝ)^i.val * F i (t,z)
        ∂volume.restrict C.domain ∂volume.restrict (Icc (0:ℝ) 1) := integral_prod _ hF
    _ = ∫ t in (0:ℝ)..1, ∑ i, (-1:ℝ)^i.val *
        BorelCoefficients.borelAction μ C.action_isMetricCurrent
          (fun x => deriv (fun s => v i (s,x)) t)
          (fun j x => v (i.succAbove j) (t,x)) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),←integral_Icc_eq_integral_Ioc]
      apply integral_congr_ae
      have ha := ae_all_iff.mpr (fun i => (hFi i).prod_right_ae)
      filter_upwards [ha] with t ht
      rw [integral_finsetSum Finset.univ (fun i _ => (ht i).const_mul _)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul,hi]

end CAT0Fillings.IntegerChart

end
end

end OAI
