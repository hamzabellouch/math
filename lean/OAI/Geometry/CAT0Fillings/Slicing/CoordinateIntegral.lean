import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.Differentiability
import OAI.Geometry.CAT0Fillings.Charts.Jacobian
import OAI.Geometry.CAT0Fillings.Slicing.CoordinateChart
import OAI.Geometry.CAT0Fillings.Slicing.CoordinateDerivative

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

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))
noncomputable def coordinateMinor (π : Fin k → X → ℝ) (w : Euc (k+1)) : ℝ :=
  (Matrix.of fun i j : Fin k =>
    (fderivWithin ℝ (C.scalar (π i)) C.domain w) (EuclideanSpace.single j.succ 1)).det

lemma ae_coordinateSlice_jacobian (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    ∀ᵐ t : ℝ, ∀ (ht : Integrable (fun z => (C.multiplicity (coordinateLayer k t z):ℝ))
      (volume.restrict (C.coordinateDomain t))),
    ∀ᵐ z ∂volume.restrict (C.coordinateDomain t),
      (C.coordinateSlice t ht).jacobian π z = C.coordinateMinor π (coordinateLayer k t z) := by
  have hall : ∀ i, ∀ᵐ t : ℝ, ∀ ht, ∀ᵐ z ∂volume.restrict (C.coordinateDomain t), ∀ j : Fin k,
      (fderivWithin ℝ ((C.coordinateSlice t ht).scalar (π i)) (C.coordinateDomain t) z)
        (EuclideanSpace.single j 1) =
      (fderivWithin ℝ (C.scalar (π i)) C.domain (coordinateLayer k t z))
        (EuclideanSpace.single j.succ 1) := by
    intro i
    obtain ⟨K,hK⟩ := hπ i
    exact C.ae_coordinateSlice_fderiv hK
  filter_upwards [ae_all_iff.mpr hall] with t ht
  intro hi
  filter_upwards [ae_all_iff.mpr (fun i => ht i hi)] with z hz
  apply congrArg Matrix.det
  ext i j
  exact hz i j

lemma ae_coordinate_minor_eq {u : X → ℝ}
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1)
    (π : Fin k → X → ℝ) :
    ∀ᵐ z ∂volume.restrict C.domain,
      C.jacobian (Matrix.vecCons u π) z = C.coordinateMinor π z := by
  filter_upwards [ae_uniqueDiffWithinAt volume C.domain,ae_restrict_mem C.borel] with z hz hm
  have hd : fderivWithin ℝ (C.scalar u) C.domain z =
      (ContinuousLinearMap.fst ℝ ℝ (Euc k)).comp (Prism.split k).toContinuousLinearMap := by
    apply HasFDerivWithinAt.fderivWithin _ hz
    apply (((ContinuousLinearMap.fst ℝ ℝ (Euc k)).hasFDerivAt).comp z
      (Prism.split k).hasFDerivAt).hasFDerivWithinAt.congr
    · intro w hw
      rw [C.scalar_eq hw,hu w hw]
      rfl
    · rw [C.scalar_eq hm,hu z hm]
      rfl
  let A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ := Matrix.of fun i j =>
    (fderivWithin ℝ (C.scalar (Matrix.vecCons u π i)) C.domain z) (EuclideanSpace.single j 1)
  have ha0 : ∀ j, A 0 j = if j=0 then 1 else 0 := by
    intro j
    dsimp only [A,Matrix.of_apply,Matrix.cons_val_zero]
    rw [hd]
    cases j using Fin.cases with
    | zero => simp [ContinuousLinearMap.comp_apply]
    | succ j => simp [ContinuousLinearMap.comp_apply]
  change A.det = _
  rw [Matrix.det_succ_row_zero]
  simp only [ha0,mul_ite,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    Fin.val_zero,pow_zero,one_mul]
  apply congrArg Matrix.det
  ext i j
  simp only [Matrix.submatrix_apply,Fin.succAbove_zero,A,Matrix.of_apply,Matrix.cons_val_succ]

end CAT0Fillings.IntegerChart

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X (k+1))

lemma coordinate_indicator (g : Euc (k+1) → ℝ) (t : ℝ) :
    (fun z => C.domain.indicator g ((Prism.split k).symm (t,z))) =
      (C.coordinateDomain t).indicator (fun z => g (coordinateLayer k t z)) := by
  funext z
  change C.domain.indicator g (coordinateLayer k t z) = _
  by_cases hz : coordinateLayer k t z ∈ C.domain
  · rw [indicator_of_mem hz,indicator_of_mem (show z ∈ C.coordinateDomain t from hz)]
  · rw [indicator_of_notMem hz,indicator_of_notMem (show z ∉ C.coordinateDomain t from hz)]

lemma coordinate_setIntegral {g : Euc (k+1) → ℝ}
    (hg : Integrable g (volume.restrict C.domain)) :
    ∫ w in C.domain, g w = ∫ t : ℝ, ∫ z in C.coordinateDomain t,
      g (coordinateLayer k t z) := by
  rw [←integral_indicator C.borel,Prism.integral_split]
  have hi : Integrable (C.domain.indicator g) := (integrable_indicator_iff C.borel).mpr hg
  have hip : Integrable (fun p : ℝ × Euc k => C.domain.indicator g ((Prism.split k).symm p)) :=
    ((Prism.split_symm_measurePreserving k).integrable_comp_emb
      (Prism.split k).symm.toHomeomorph.measurableEmbedding).mpr hi
  change (∫ p : ℝ × Euc k, C.domain.indicator g ((Prism.split k).symm p) ∂volume.prod volume) = _
  rw [integral_prod _ hip]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    dsimp only
    rw [C.coordinate_indicator g t,integral_indicator (C.measurableSet_coordinateDomain t)]

lemma integrable_coordinate_setIntegral {g : Euc (k+1) → ℝ}
    (hg : Integrable g (volume.restrict C.domain)) :
    Integrable (fun t : ℝ => ∫ z in C.coordinateDomain t, g (coordinateLayer k t z)) := by
  have hi : Integrable (C.domain.indicator g) := (integrable_indicator_iff C.borel).mpr hg
  have hip : Integrable (fun p : ℝ × Euc k => C.domain.indicator g ((Prism.split k).symm p)) :=
    ((Prism.split_symm_measurePreserving k).integrable_comp_emb
      (Prism.split k).symm.toHomeomorph.measurableEmbedding).mpr hi
  convert hip.integral_prod_left using 1
  funext t
  rw [C.coordinate_indicator g t,integral_indicator (C.measurableSet_coordinateDomain t)]

lemma integrable_coordinateMinor {u : X → ℝ} {K : ℝ≥0} (hL : LipschitzWith K u)
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1)
    {b : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible b π) :
    Integrable (fun w => (C.multiplicity w:ℝ)*C.scalar b w*C.coordinateMinor π w)
      (volume.restrict C.domain) := by
  have ha : ∀ i, ∃ L : ℝ≥0, LipschitzWith L (Matrix.vecCons u π i) := by
    intro i
    cases i using Fin.cases with
    | zero => exact ⟨_,hL⟩
    | succ i => exact h.2 i
  apply (C.integrable_action_integrand h.1 ha).congr
  filter_upwards [C.ae_coordinate_minor_eq hu π] with z hz
  rw [hz]

lemma ae_coordinateSliceTotal_action {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) :
    ∀ᵐ t : ℝ, (C.coordinateSliceTotal t).action b π =
      ∫ z in C.coordinateDomain t, (C.multiplicity (coordinateLayer k t z):ℝ)*
        C.scalar b (coordinateLayer k t z)*C.coordinateMinor π (coordinateLayer k t z) := by
  filter_upwards [C.ae_coordinateSliceTotal_eq,C.ae_coordinateSlice_jacobian π h.2] with t ht hj
  obtain ⟨hi,heq⟩ := ht
  rw [heq,action,ite_eq_left h]
  apply integral_congr_ae
  filter_upwards [hj hi,ae_restrict_mem (C.measurableSet_coordinateDomain t)] with z hz hm
  change (C.multiplicity (coordinateLayer k t z):ℝ)*
    (C.coordinateSlice t hi).scalar b z*(C.coordinateSlice t hi).jacobian π z = _
  rw [C.coordinateSlice_scalar_eq t hi b hm,hz]

theorem coordinateSlice_action_integral {u : X → ℝ} {K : ℝ≥0} (hL : LipschitzWith K u)
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1)
    {b : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible b π) :
    C.action b (Matrix.vecCons u π) = ∫ t : ℝ, (C.coordinateSliceTotal t).action b π := by
  have ha : Admissible b (Matrix.vecCons u π) := ⟨h.1,fun i => by
    cases i using Fin.cases with
    | zero => exact ⟨_,hL⟩
    | succ i => exact h.2 i⟩
  rw [action,ite_eq_left ha]
  calc
    _ = ∫ w in C.domain, (C.multiplicity w:ℝ)*C.scalar b w*C.coordinateMinor π w := by
      apply integral_congr_ae
      filter_upwards [C.ae_coordinate_minor_eq hu π] with z hz
      rw [hz]
    _ = ∫ t : ℝ, ∫ z in C.coordinateDomain t, (C.multiplicity (coordinateLayer k t z):ℝ)*
        C.scalar b (coordinateLayer k t z)*C.coordinateMinor π (coordinateLayer k t z) :=
      C.coordinate_setIntegral (C.integrable_coordinateMinor hL hu h)
    _ = _ := integral_congr_ae (Filter.EventuallyEq.symm (C.ae_coordinateSliceTotal_action h))

lemma coordinateSlice_action_integrable {u : X → ℝ} {K : ℝ≥0} (hL : LipschitzWith K u)
    (hu : ∀ z (hz : z ∈ C.domain), u (C.param ⟨z,hz⟩) = (Prism.split k z).1)
    {b : X → ℝ} {π : Fin k → X → ℝ} (h : Admissible b π) :
    Integrable (fun t : ℝ => (C.coordinateSliceTotal t).action b π) :=
  (C.integrable_coordinate_setIntegral (C.integrable_coordinateMinor hL hu h)).congr
    (Filter.EventuallyEq.symm (C.ae_coordinateSliceTotal_action h))

end CAT0Fillings.IntegerChart
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

end CAT0Fillings

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
