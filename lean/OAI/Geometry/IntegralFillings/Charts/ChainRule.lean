import Mathlib
import OAI.Geometry.IntegralFillings.Currents.WeightedAction
import OAI.Geometry.IntegralFillings.Currents.Contraction

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Filter Set
open scoped Topology NNReal
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

namespace SharpIntegralFillings
open Set MeasureTheory Filter BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] {k : ℕ} {T : Functional X (k+1)}
lemma weightedCurrent_boundary_cycle (hT : IsMetricCurrent T) (hrect : IntegerRectifiable T)
    (hz : IsCycle T) (μ : Measure X) [IsFiniteMeasure μ] (hμ : Controls T μ)
    {u : X → ℝ} (hu : BoundedLip u) :
    boundarySucc (weightedCurrent μ hT u) = - contractCurrent u T := by
  classical
  funext b π
  by_cases hab : Admissible b π
  · have hcons : Admissible (fun _ : X => (1:ℝ)) (Matrix.vecCons b π) :=
      ⟨BoundedLip.const 1,fun i => Fin.cases hab.1.1 (fun j => hab.2 j) i⟩
    simp only [boundarySucc,ite_eq_left hab,weightedCurrent,ite_eq_left hcons,mul_one,
      Pi.neg_apply,contractCurrent_apply _ _ hab]
    rw [borelAction_eq μ hT hμ ⟨hu,fun i => Fin.cases hab.1.1 (fun j => hab.2 j) i⟩]
    exact Foundations.IntegerRectifiable.cycle_product_rule hrect hz hu hab.1 π hab.2
  · simp only [boundarySucc,ite_eq_right hab,Pi.neg_apply,contractCurrent,neg_zero]

lemma weightedCurrent_boundary_controls (hT : IsMetricCurrent T) (hrect : IntegerRectifiable T)
    (hz : IsCycle T) (μ : Measure X) [IsFiniteMeasure μ] (hμ : Controls T μ)
    {u : X → ℝ} (hu : BoundedLip u) {K : ℝ≥0} (hK : LipschitzWith K u) :
    Controls (boundarySucc (weightedCurrent μ hT u)) (K • μ) := by
  rw [weightedCurrent_boundary_cycle hT hrect hz μ hμ hu]
  intro b π hb hπ
  simpa only [Pi.neg_apply,abs_neg] using contractCurrent_controls hT hμ hK b π hb hπ

end SharpIntegralFillings

namespace SharpIntegralFillings.IntegerChart
open Set MeasureTheory Filter

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma ae_fderivWithin_scalar_comp {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {φ dφ : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (dφ t) t) :
    ∀ᵐ z ∂volume.restrict C.domain,
      fderivWithin ℝ (C.scalar (φ ∘ u)) C.domain z =
        dφ (C.scalar u z) • fderivWithin ℝ (C.scalar u) C.domain z := by
  filter_upwards [ae_uniqueDiffWithinAt volume C.domain,ae_restrict_mem C.borel,
    C.ae_differentiableWithinAt_scalar hu] with z hz hzs hdu
  have heq : EqOn (C.scalar (φ ∘ u)) (φ ∘ C.scalar u) C.domain := by
    intro y hy
    simp only [Function.comp_apply,C.scalar_eq hy]
  have hh := (hφ (C.scalar u z)).comp_hasFDerivWithinAt z hdu.hasFDerivWithinAt
  exact (hh.congr heq (heq hzs)).fderivWithin hz

lemma ae_jacobian_update_comp (π : Fin k → X → ℝ) (i : Fin k)
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {φ dφ : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (dφ t) t) :
    ∀ᵐ z ∂volume.restrict C.domain,
      C.jacobian (Function.update π i (φ ∘ u)) z =
        dφ (C.scalar u z) * C.jacobian (Function.update π i u) z := by
  filter_upwards [C.ae_fderivWithin_scalar_comp hu hφ] with z hz
  rw [C.jacobian_update,C.jacobian_update,hz]
  simpa only [_root_.smul_apply,Pi.smul_def,smul_eq_mul] using Matrix.det_updateRow_smul
    (Matrix.of fun a j => fderivWithin ℝ (C.scalar (π a)) C.domain z (EuclideanSpace.single j 1))
    i (dφ (C.scalar u z))
    (fun j => fderivWithin ℝ (C.scalar u) C.domain z (EuclideanSpace.single j 1))

lemma action_update_comp {b u : X → ℝ} (hb : BoundedLip b) (hu : BoundedLip u)
    {φ dφ : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (dφ t) t)
    (hφu : BoundedLip (φ ∘ u)) (hdu : BoundedLip (dφ ∘ u))
    (π : Fin k → X → ℝ) (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k) :
    C.action b (Function.update π i (φ ∘ u)) =
      C.action (fun x => b x * dφ (u x)) (Function.update π i u) := by
  obtain ⟨K,hK⟩ := hu.1
  have hup {a : X → ℝ} (ha : BoundedLip a) :
      ∀ j, ∃ K : ℝ≥0, LipschitzWith K ((Function.update π i a) j) := by
    intro j
    by_cases hji : j = i
    · simpa [hji] using ha.1
    · simpa [hji] using hπ j
  rw [action,ite_eq_left ⟨hb,hup hφu⟩,action,ite_eq_left ⟨hb.mul hdu,hup hu⟩]
  apply integral_congr_ae
  filter_upwards [C.ae_jacobian_update_comp π i hK hφ,ae_restrict_mem C.borel] with z hz hzs
  rw [hz,C.scalar_eq hzs,C.scalar_eq hzs,C.scalar_eq hzs]
  ring

end SharpIntegralFillings.IntegerChart

namespace SharpIntegralFillings.Foundations
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

omit [BorelSpace X] [CompactSpace X] in
lemma IntegerRectifiable.apply_update_comp {k : ℕ} {T : Functional X k}
    (hT : IntegerRectifiable T) {b u : X → ℝ} (hb : BoundedLip b) (hu : BoundedLip u)
    {φ dφ : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (dφ t) t)
    (hφu : BoundedLip (φ ∘ u)) (hdu : BoundedLip (dφ ∘ u))
    (π : Fin k → X → ℝ) (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k) :
    T b (Function.update π i (φ ∘ u)) =
      T (fun x => b x * dφ (u x)) (Function.update π i u) := by
  obtain ⟨C,_,_,_,heq⟩ := hT
  rw [heq,heq]
  apply tsum_congr
  intro j
  exact (C j).action_update_comp hb hu hφ hφu hdu π hπ i

end SharpIntegralFillings.Foundations

end

end OAI
