import Mathlib
import OAI.Geometry.IntegralFillings.Charts.Scalar
import OAI.Geometry.IntegralFillings.Slicing.CoordinateChart

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
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))
lemma coordinateSlice_scalar_eq (t : ℝ)
    (ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t))) (f : X → ℝ)
    {z : Euc k} (hz : z ∈ C.coordinateDomain t) :
    (C.coordinateSlice t ht).scalar f z = C.scalar f (coordinateLayer k t z) := by
  rw [(C.coordinateSlice t ht).scalar_eq hz,C.scalar_eq hz]
  rfl

lemma coordinateSlice_fderiv (t : ℝ)
    (ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t))) {f : X → ℝ} {F : Euc (k+1) → ℝ}
    (heq : EqOn F (C.scalar f) C.domain) {z : Euc k}
    (hz : z ∈ C.coordinateDomain t) (hF : DifferentiableAt ℝ F (coordinateLayer k t z))
    (hu : UniqueDiffWithinAt ℝ C.domain (coordinateLayer k t z))
    (hv : UniqueDiffWithinAt ℝ (C.coordinateDomain t) z) (j : Fin k) :
    (fderivWithin ℝ ((C.coordinateSlice t ht).scalar f) (C.coordinateDomain t) z)
      (EuclideanSpace.single j 1) =
    (fderivWithin ℝ (C.scalar f) C.domain (coordinateLayer k t z))
      (EuclideanSpace.single j.succ 1) := by
  have hFC : fderivWithin ℝ (C.scalar f) C.domain (coordinateLayer k t z) =
      fderiv ℝ F (coordinateLayer k t z) :=
    (hF.hasFDerivAt.hasFDerivWithinAt.congr (fun w hw => (heq hw).symm) (heq hz).symm).fderivWithin hu
  let L : Euc k →L[ℝ] Euc (k+1) :=
    (Prism.split k).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ ℝ (Euc k))
  have hl : HasFDerivAt (coordinateLayer k t) L z := by
    exact (Prism.split k).symm.hasFDerivAt.comp z
      ((hasFDerivAt_const (𝕜 := ℝ) t z).prodMk (hasFDerivAt_id (𝕜 := ℝ) z))
  have hFS : fderivWithin ℝ ((C.coordinateSlice t ht).scalar f) (C.coordinateDomain t) z =
      (fderiv ℝ F (coordinateLayer k t z)).comp L := by
    apply HasFDerivWithinAt.fderivWithin _ hv
    apply (hF.hasFDerivAt.comp z hl).hasFDerivWithinAt.congr
    · intro w hw
      rw [C.coordinateSlice_scalar_eq t ht f hw]
      exact (heq hw).symm
    · rw [C.coordinateSlice_scalar_eq t ht f hz]
      exact (heq hz).symm
  rw [hFC,hFS,ContinuousLinearMap.comp_apply]
  have hb : L (EuclideanSpace.single j 1) = EuclideanSpace.single j.succ 1 := by
    apply (Prism.split k).injective
    change Prism.split k ((Prism.split k).symm (0,EuclideanSpace.single j 1)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply,Prism.split_single_succ]
  rw [hb]

lemma ae_coordinateSlice_fderiv {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∀ᵐ t : ℝ, ∀ (ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t))),
    ∀ᵐ z ∂volume.restrict (C.coordinateDomain t), ∀ j : Fin k,
      (fderivWithin ℝ ((C.coordinateSlice t ht).scalar f) (C.coordinateDomain t) z)
        (EuclideanSpace.single j 1) =
      (fderivWithin ℝ (C.scalar f) C.domain (coordinateLayer k t z))
        (EuclideanSpace.single j.succ 1) := by
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  obtain ⟨F,hF,heq⟩ := (C.scalar_lipschitzOn hL hf).extend_real
  have hfull : ∀ᵐ w : Euc (k+1), w ∈ C.domain →
      DifferentiableAt ℝ F w ∧ UniqueDiffWithinAt ℝ C.domain w := by
    filter_upwards [hF.ae_differentiableAt (μ := volume),
      (ae_restrict_iff' C.borel).mp (ae_uniqueDiffWithinAt volume C.domain)] with w hw hu
    exact fun hm => ⟨hw,hu hm⟩
  have hp := (Prism.split_symm_measurePreserving k).quasiMeasurePreserving.ae hfull
  filter_upwards [Measure.ae_ae_of_ae_prod hp] with t ht
  intro hi
  have ht' : ∀ᵐ z ∂volume.restrict (C.coordinateDomain t),
      DifferentiableAt ℝ F (coordinateLayer k t z) ∧
      UniqueDiffWithinAt ℝ C.domain (coordinateLayer k t z) :=
    (ae_restrict_iff' (C.measurableSet_coordinateDomain t)).mpr ht
  filter_upwards [ht',ae_restrict_mem (C.measurableSet_coordinateDomain t),
    ae_uniqueDiffWithinAt volume (C.coordinateDomain t)] with z hz hm hu
  exact fun j => C.coordinateSlice_fderiv t hi (fun w hw => (heq hw).symm) hm hz.1 hz.2 hu j

end SharpIntegralFillings.IntegerChart

namespace SharpIntegralFillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))

noncomputable def coordinateEmptyChart : IntegerChart X k where
  domain := ∅
  borel := MeasurableSet.empty
  bounded := Bornology.isBounded_empty
  param := fun z => False.elim z.property
  bilipschitz := by
    refine ⟨0,0,?_,?_⟩
    · apply LipschitzWith.of_dist_le_mul
      intro a b
      exact False.elim a.property
    · intro a b
      exact False.elim a.property
  multiplicity := fun _ => 0
  integrable := by simp

noncomputable def coordinateSliceTotal (t : ℝ) : IntegerChart X k := by
  classical
  exact if ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t)) then C.coordinateSlice t ht
    else coordinateEmptyChart

lemma ae_coordinateSliceTotal_eq : ∀ᵐ t : ℝ,
    ∃ ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t)),
      C.coordinateSliceTotal t = C.coordinateSlice t ht := by
  filter_upwards [C.ae_integrable_coordinateMultiplicity] with t ht
  exact ⟨ht,dite_eq_left ht⟩

end SharpIntegralFillings.IntegerChart
end

end OAI
