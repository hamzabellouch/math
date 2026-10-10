import Mathlib
import OAI.Geometry.IntegralFillings.Jacobian.WeakLimits
import OAI.Geometry.IntegralFillings.Charts.ExtensionsLimit
import OAI.Geometry.IntegralFillings.Charts.Scalar

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal

namespace SharpIntegralFillings
namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
lemma integrable_weight {b : X → ℝ} (hb : BoundedLip b) :
    Integrable (fun z => (C.multiplicity z : ℝ) * C.scalar b z)
      (volume.restrict C.domain) := by
  obtain ⟨K,hK⟩ := hb.1
  obtain ⟨M,hM⟩ := hb.2
  apply C.integrable.mul_bdd (C.measurable_scalar hK).aestronglyMeasurable
  filter_upwards [ae_restrict_mem C.borel] with z hz
  simpa [C.scalar_eq hz,Real.norm_eq_abs] using hM (C.param ⟨z,hz⟩)

lemma action_eq_extended_jacobian {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) {F : Fin k → Euc k → ℝ} {K : ℝ≥0}
    (hF : ∀ i, LipschitzWith K (F i))
    (heq : ∀ i, EqOn (C.scalar (π i)) (F i) C.domain) :
    C.action b π = ∫ z,
      C.domain.indicator (fun z => (C.multiplicity z : ℝ) * C.scalar b z) z *
        coordinateJacobian F (fun j => EuclideanSpace.single j 1) z := by
  rw [action,ite_eq_left h]
  have H := C.ae_jacobian_eq_extensions hF heq
  have H' : C.jacobian π =ᵐ[volume.restrict C.domain]
      coordinateJacobian F (fun j => EuclideanSpace.single j 1) := by
    filter_upwards [H] with z hz
    rw [hz,coordinateJacobian,← Matrix.det_transpose]
    rfl
  calc
    _ = ∫ z in C.domain, ((C.multiplicity z : ℝ) * C.scalar b z) *
        coordinateJacobian F (fun j => EuclideanSpace.single j 1) z := by
      apply integral_congr_ae
      filter_upwards [H'] with z hz
      rw [hz]
    _ = _ := by
      rw [← integral_indicator C.borel]
      apply integral_congr_ae
      filter_upwards [] with z
      exact Set.indicator_mul_left _ _ _

lemma action_sequentialContinuity (b : X → ℝ) (π : Fin k → X → ℝ)
    (πs : ℕ → Fin k → X → ℝ) (hb : BoundedLip b)
    (hπs : ∀ i, ∃ K : ℝ≥0, ∀ j, LipschitzWith K (πs j i))
    (hlim : ∀ i x, Tendsto (fun j => πs j i x) atTop (𝓝 (π i x))) :
    Tendsto (fun j => C.action b (πs j)) atTop (𝓝 (C.action b π)) := by
  obtain ⟨L,U,hφ,_⟩ := C.bilipschitz
  choose Ks hKs using hπs
  let K : ℝ≥0 := ∑ i, Ks i
  have hK (i : Fin k) : Ks i ≤ K :=
    Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)
  have hseq (j : ℕ) (i : Fin k) : LipschitzWith K (πs j i) := (hKs i j).weaken (hK i)
  have hπ (i : Fin k) : LipschitzWith K (π i) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact le_of_tendsto ((hlim i x).dist (hlim i y))
      (Eventually.of_forall fun j => (hseq j i).dist_le_mul x y)
  have htot : TotallyBounded C.domain := C.bounded.isCompact_closure.totallyBounded.subset subset_closure
  have hsc (i : Fin k) (j : ℕ) : LipschitzOnWith (K*L) (C.scalar (πs j i)) C.domain :=
    C.scalar_lipschitzOn hφ (hseq j i)
  have hlsc (i : Fin k) (z : Euc k) (hz : z ∈ C.domain) :
      Tendsto (fun j => C.scalar (πs j i) z) atTop (𝓝 (C.scalar (π i) z)) := by
    simpa only [C.scalar_eq hz] using hlim i (C.param ⟨z,hz⟩)
  choose Fs F hFs hF heqs heq hlimF using fun i =>
    exists_convergent_lipschitz_extensions htot (hsc i) (hlsc i)
  let a : Euc k → ℝ := C.domain.indicator (fun z => (C.multiplicity z : ℝ) * C.scalar b z)
  have ha : Integrable a volume := (integrable_indicator_iff C.borel).mpr (C.integrable_weight hb)
  have H := weak_coordinateJacobian volume k (fun j i => hFs i j) hF hlimF
    (fun j => EuclideanSpace.single j 1) ha
  have heqs' (j : ℕ) := C.action_eq_extended_jacobian ⟨hb,fun i => ⟨K,hseq j i⟩⟩
    (fun i => hFs i j) (fun i => heqs i j)
  have heq' := C.action_eq_extended_jacobian ⟨hb,fun i => ⟨K,hπ i⟩⟩ hF heq
  simpa only [heqs',heq'] using H

end IntegerChart
end SharpIntegralFillings

end

end OAI
