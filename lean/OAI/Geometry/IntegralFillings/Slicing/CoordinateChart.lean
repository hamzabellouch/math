import Mathlib
import OAI.Geometry.IntegralFillings.Slicing.EuclideanSplit

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
noncomputable def coordinateLayer (k : ℕ) (t : ℝ) (z : Euc k) : Euc (k+1) :=
  (Prism.split k).symm (t,z)

lemma coordinateLayer_lipschitz (t : ℝ) :
    LipschitzWith ‖(Prism.split k).symm.toContinuousLinearMap‖₊ (coordinateLayer k t) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have h := (Prism.split k).symm.lipschitzWith.dist_le_mul (t,z) (t,w)
  simpa only [coordinateLayer,Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using h

lemma coordinateLayer_antilipschitz (t : ℝ) :
    AntilipschitzWith ‖(Prism.split k).toContinuousLinearMap‖₊ (coordinateLayer k t) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro z w
  have h := (Prism.split k).lipschitzWith.dist_le_mul
    (coordinateLayer k t z) (coordinateLayer k t w)
  simpa only [coordinateLayer,ContinuousLinearEquiv.apply_symm_apply,Prod.dist_eq,dist_self,
    max_eq_right dist_nonneg] using h

noncomputable def coordinateDomain (t : ℝ) : Set (Euc k) :=
  coordinateLayer k t ⁻¹' C.domain

lemma measurableSet_coordinateDomain (t : ℝ) : MeasurableSet (C.coordinateDomain t) :=
  C.borel.preimage (coordinateLayer_lipschitz (k := k) t).continuous.measurable

lemma bounded_coordinateDomain (t : ℝ) : Bornology.IsBounded (C.coordinateDomain t) := by
  apply Bornology.IsBounded.subset
    ((LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : ℝ × Euc k → Euc k)).isBounded_image
      ((Prism.split k).lipschitzWith.isBounded_image C.bounded))
  intro z hz
  refine ⟨(t,z),?_,rfl⟩
  exact ⟨coordinateLayer k t z,hz,(Prism.split k).apply_symm_apply (t,z)⟩

noncomputable def coordinateParam (t : ℝ) (z : C.coordinateDomain t) : X :=
  C.param ⟨coordinateLayer k t z,z.2⟩

lemma coordinateParam_lipschitz (t : ℝ) {L : ℝ≥0} (hL : LipschitzWith L C.param) :
    LipschitzWith (L * ‖(Prism.split k).symm.toContinuousLinearMap‖₊) (C.coordinateParam t) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have h := hL.dist_le_mul ⟨coordinateLayer k t z,z.2⟩ ⟨coordinateLayer k t w,w.2⟩
  have hh := (coordinateLayer_lipschitz (k := k) t).dist_le_mul z.val w.val
  change dist (C.coordinateParam t z) (C.coordinateParam t w) ≤ _ at h
  calc
    _ ≤ (L:ℝ) * dist (coordinateLayer k t z) (coordinateLayer k t w) := h
    _ ≤ (L:ℝ) * (‖(Prism.split k).symm.toContinuousLinearMap‖₊ * dist z.val w.val) :=
      mul_le_mul_of_nonneg_left hh L.coe_nonneg
    _ = _ := by simp only [NNReal.coe_mul,mul_assoc,Subtype.dist_eq]

lemma coordinateParam_antilipschitz (t : ℝ) {U : ℝ≥0} (hU : AntilipschitzWith U C.param) :
    AntilipschitzWith (‖(Prism.split k).toContinuousLinearMap‖₊ * U) (C.coordinateParam t) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro z w
  have h := hU.le_mul_dist ⟨coordinateLayer k t z,z.2⟩ ⟨coordinateLayer k t w,w.2⟩
  have hh := (coordinateLayer_antilipschitz (k := k) t).le_mul_dist z.val w.val
  calc
    dist z w ≤ ‖(Prism.split k).toContinuousLinearMap‖₊ *
        dist (coordinateLayer k t z) (coordinateLayer k t w) := hh
    _ ≤ ‖(Prism.split k).toContinuousLinearMap‖₊ *
        ((U:ℝ)*dist (C.coordinateParam t z) (C.coordinateParam t w)) :=
      mul_le_mul_of_nonneg_left h (NNReal.coe_nonneg _)
    _ = _ := by simp only [NNReal.coe_mul,mul_assoc]

lemma coordinateParam_bilipschitz (t : ℝ) : ∃ L U : ℝ≥0,
    LipschitzWith L (C.coordinateParam t) ∧ AntilipschitzWith U (C.coordinateParam t) := by
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  exact ⟨_,_,C.coordinateParam_lipschitz t hL,C.coordinateParam_antilipschitz t hU⟩

lemma ae_integrable_coordinateMultiplicity : ∀ᵐ t : ℝ,
    Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t)) := by
  have hi : Integrable (C.domain.indicator (fun z => (C.multiplicity z:ℝ))) :=
    (integrable_indicator_iff C.borel).mpr C.integrable
  have hip : Integrable (fun p : ℝ × Euc k =>
      C.domain.indicator (fun z => (C.multiplicity z:ℝ)) ((Prism.split k).symm p)) :=
    ((Prism.split_symm_measurePreserving k).integrable_comp_emb
      (Prism.split k).symm.toHomeomorph.measurableEmbedding).mpr hi
  filter_upwards [hip.prod_right_ae] with t ht
  apply (integrable_indicator_iff (C.measurableSet_coordinateDomain t)).mp
  have heq : (C.coordinateDomain t).indicator (fun z => (C.multiplicity (coordinateLayer k t z):ℝ)) =
      fun z => C.domain.indicator (fun w => (C.multiplicity w:ℝ)) ((Prism.split k).symm (t,z)) := by
    funext z
    change (C.coordinateDomain t).indicator _ z = C.domain.indicator _ (coordinateLayer k t z)
    by_cases hz : coordinateLayer k t z ∈ C.domain
    · rw [indicator_of_mem (show z ∈ C.coordinateDomain t from hz),indicator_of_mem hz]
    · rw [indicator_of_notMem (show z ∉ C.coordinateDomain t from hz),indicator_of_notMem hz]
  rw [heq]
  exact ht

noncomputable def coordinateSlice (t : ℝ)
    (ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t))) : IntegerChart X k where
  domain := C.coordinateDomain t
  borel := C.measurableSet_coordinateDomain t
  bounded := C.bounded_coordinateDomain t
  param := C.coordinateParam t
  bilipschitz := C.coordinateParam_bilipschitz t
  multiplicity z := C.multiplicity (coordinateLayer k t z)
  integrable := ht

end SharpIntegralFillings.IntegerChart

end

end OAI
