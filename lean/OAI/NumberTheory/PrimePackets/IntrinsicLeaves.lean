import Mathlib
import OAI.NumberTheory.PrimePackets.LeafTransitions

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
namespace PrimeDegreePackets
variable {n : ℕ} {i j : Fin n} (hij : i ≠ j)

 

def selectedRootBox (x : X n) : boundedRootAtlas hij := (boundedRootAtlas_covers hij x).choose

lemma selectedRootBox_mem (x : X n) : x ∈ (selectedRootBox hij x).val.box.range :=
  (boundedRootAtlas_covers hij x).choose_spec

 

def intrinsicRootLeaf (μ : Measure (X n)) [IsFiniteMeasure μ] (x : X n) : Measure ℝ :=
  let B := (selectedRootBox hij x).val
  B.box.basedLeaf B.radius μ (B.box.coordinates ⟨x,selectedRootBox_mem hij x⟩).val

namespace RootBox
variable {hij} {k : Fin n}

 

theorem ae_intrinsicRootLeaf_coordinates (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ,
      intrinsicRootLeaf hij μ (rootQuotientParametrization hij z) = A.basedLeaf R μ z := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H := ae_all_iff.mpr (fun B : boundedRootAtlas hij =>
    A.ae_basedLeaf_chart_compatibility B.val.box R B.val.radius hAR B.val.time_bound μ hfree)
  filter_upwards [H] with z hz
  let x := rootQuotientParametrization hij z
  let B := selectedRootBox hij x
  let w := B.val.box.coordinates ⟨x,selectedRootBox_mem hij x⟩
  exact (hz B w.val w.prop (B.val.box.param_coordinates ⟨x,selectedRootBox_mem hij x⟩).symm).symm

lemma aemeasurable_intrinsicRootLeaf_restrict (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    AEMeasurable (intrinsicRootLeaf hij μ) (μ.restrict A.range) := by
  apply A.aemeasurable_of_coordinate μ
  exact (A.aemeasurable_basedLeaf R hAR μ hfree).congr
    ((A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree).mono (fun z hz => hz.symm))

lemma ae_intrinsicRootLeaf_spec_restrict (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ x ∂μ.restrict A.range, IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) ∧
      intrinsicRootLeaf hij μ x (Metric.ball 0 1) = 1 := by
  apply A.ae_of_coordinate μ
  filter_upwards [A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree,
    A.ae_basedLeaf_spec R hAR μ hfree] with z he hz
  rwa [he]

end RootBox

lemma boundedRootAtlas_iUnion : (⋃ B : boundedRootAtlas hij, B.val.box.range) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨B,hB⟩ := boundedRootAtlas_covers hij x
  exact mem_iUnion.mpr ⟨B,hB⟩

theorem aemeasurable_intrinsicRootLeaf (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    AEMeasurable (intrinsicRootLeaf hij μ) μ := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H := AEMeasurable.iUnion (μ := μ) (fun B : boundedRootAtlas hij =>
    B.val.box.aemeasurable_intrinsicRootLeaf_restrict B.val.radius B.val.time_bound μ hfree)
  simpa only [boundedRootAtlas_iUnion,Measure.restrict_univ] using H

 

theorem ae_intrinsicRootLeaf_spec (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ x ∂μ, IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) ∧
      intrinsicRootLeaf hij μ x (Metric.ball 0 1) = 1 := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H := (ae_restrict_iUnion_iff (μ := μ) (fun B : boundedRootAtlas hij => B.val.box.range)
    (fun x => IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) ∧
      intrinsicRootLeaf hij μ x (Metric.ball 0 1) = 1)).mpr
    (fun B => B.val.box.ae_intrinsicRootLeaf_spec_restrict B.val.radius B.val.time_bound μ hfree)
  simpa only [boundedRootAtlas_iUnion,Measure.restrict_univ] using H

 

def intrinsicRootKernel (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    Kernel (X n) ℝ := locallyFiniteRealVersion
      ⟨(aemeasurable_intrinsicRootLeaf hij μ hfree).mk (intrinsicRootLeaf hij μ),
        (aemeasurable_intrinsicRootLeaf hij μ hfree).measurable_mk⟩

instance intrinsicRootKernel_locallyFinite (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) (x : X n) :
    IsLocallyFiniteMeasure (intrinsicRootKernel hij μ hfree x) :=
  locallyFiniteRealVersion_locallyFinite _ _

instance intrinsicRootKernel_sFinite (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    IsSFiniteKernel (intrinsicRootKernel hij μ hfree) := locallyFiniteRealVersion_sFinite _

lemma ae_intrinsicRootKernel_eq (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ x ∂μ, intrinsicRootKernel hij μ hfree x = intrinsicRootLeaf hij μ x := by
  let κ : Kernel (X n) ℝ :=
    ⟨(aemeasurable_intrinsicRootLeaf hij μ hfree).mk (intrinsicRootLeaf hij μ),
      (aemeasurable_intrinsicRootLeaf hij μ hfree).measurable_mk⟩
  have he : ∀ᵐ x ∂μ, κ x = intrinsicRootLeaf hij μ x :=
    (aemeasurable_intrinsicRootLeaf hij μ hfree).ae_eq_mk.symm
  filter_upwards [he,ae_intrinsicRootLeaf_spec hij μ hfree] with x hx hs
  have : IsLocallyFiniteMeasure (κ x) := hx.symm ▸ hs.1
  exact (locallyFiniteRealVersion_eq κ x).trans hx

end PrimeDegreePackets


namespace PrimeDegreePackets
namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

lemma diagonal_time_bound (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ) :
    (A.diagonal ell hell t).time ⊆ rootLeafWindow (Real.exp ((ell j-ell i)*t)*R) 0 := by
  rintro _ ⟨u,hu,rfl⟩
  have h := hAR hu
  simp only [rootLeafWindow,Nat.cast_zero,add_zero,Set.mem_Ioo] at h ⊢
  change -(Real.exp ((ell j-ell i)*t)*R) < Real.exp ((ell j-ell i)*t)*u ∧
    Real.exp ((ell j-ell i)*t)*u < Real.exp ((ell j-ell i)*t)*R
  constructor
  · simpa only [mul_neg] using mul_lt_mul_of_pos_left h.1 (Real.exp_pos _)
  · exact mul_lt_mul_of_pos_left h.2 (Real.exp_pos _)

lemma ae_basedLeaf_diagonal (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ) :
    ∀ᵐ z ∂A.coordinateMeasure μ,
      (A.diagonal ell hell t).basedLeaf (Real.exp ((ell j-ell i)*t)*R) μ
          (rootDiagonalCoordinates ell hell t z) =
        anchorNormalize ((A.basedLeaf R μ z).map (rootTimeScaling ell i j t)) (Metric.ball 0 1) := by
  have H := ae_of_ae_map measurable_fst.aemeasurable
    (A.ae_leafMeasure_diagonal R (Real.exp ((ell j-ell i)*t)*R) hAR ell hell t
      (A.diagonal_time_bound R hAR ell hell t) μ hfree hinv)
  have Hlf := ae_of_ae_map measurable_fst.aemeasurable
    ((A.ae_leafMeasure_spec R hAR μ hfree).mono fun s hs => hs.1)
  filter_upwards [H,Hlf,A.ae_leafMeasure_ball_pos R hAR μ hfree] with z hz hlf hp
  let : IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) := hlf
  change basedRealMeasure ((A.diagonal ell hell t).leafMeasure _ μ
    (rootSliceDiagonal ell hell t z.1)) (Real.exp ((ell j-ell i)*t)*z.2) = _
  rw [hz]
  exact basedRealMeasure_scaling (A.leafMeasure R μ z.1)
    (Real.exp ((ell j-ell i)*t)) z.2 (Real.exp_ne_zero _) (hp 1 zero_lt_one)

lemma ae_intrinsicRootLeaf_diagonal_restrict (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ) :
    ∀ᵐ x ∂μ.restrict A.range,
      intrinsicRootLeaf hij μ (rightAction x (diagonalOneParameter ell hell t)) =
        anchorNormalize ((intrinsicRootLeaf hij μ x).map (rootTimeScaling ell i j t)) (Metric.ball 0 1) := by
  apply A.ae_of_coordinate μ
  have HD := (A.diagonal ell hell t).ae_intrinsicRootLeaf_coordinates
    (Real.exp ((ell j-ell i)*t)*R) (A.diagonal_time_bound R hAR ell hell t) μ hfree
  rw [A.diagonal_coordinateMeasure ell hell t μ hinv] at HD
  have HD' := ae_of_ae_map (rootDiagonalCoordinates ell hell t).measurable.aemeasurable HD
  filter_upwards [HD',A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree,
    A.ae_basedLeaf_diagonal R hAR ell hell t μ hfree hinv] with z hd ha hc
  rw [rootDiagonalCoordinates_param] at hd
  rw [hd,ha,hc]

end RootBox

 

theorem ae_intrinsicRootLeaf_diagonal {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ) :
    ∀ᵐ x ∂μ,
      intrinsicRootLeaf hij μ (rightAction x (diagonalOneParameter ell hell t)) =
        anchorNormalize ((intrinsicRootLeaf hij μ x).map (rootTimeScaling ell i j t)) (Metric.ball 0 1) := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H := (ae_restrict_iUnion_iff (μ := μ) (fun B : boundedRootAtlas hij => B.val.box.range) _).mpr
    (fun B => B.val.box.ae_intrinsicRootLeaf_diagonal_restrict B.val.radius B.val.time_bound
      ell hell t μ hfree hinv)
  simpa only [boundedRootAtlas_iUnion,Measure.restrict_univ] using H

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma ae_eq_of_measurePreserving_ennreal_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf1 : ∀ᵐ x ∂μ, f x ≤ 1)
    (hmono : ∀ᵐ x ∂μ, f x ≤ f (T x)) : f =ᵐ[μ] f ∘ T := by
  have hint : ∫⁻ x, f x ∂μ < ∞ :=
    (lintegral_mono_ae hf1).trans_lt (by simp)
  have he : ∫⁻ x, f (T x) ∂μ = ∫⁻ x, f x ∂μ := by
    have hf' : AEMeasurable f (μ.map T) := hT.map_eq.symm ▸ hf
    exact ((lintegral_map' hf' hT.measurable.aemeasurable).symm).trans
      (congrArg (fun ν : Measure α => ∫⁻ x, f x ∂ν) hT.map_eq)
  exact ae_eq_of_ae_le_of_lintegral_le hmono hint.ne
    (hf.comp_quasiMeasurePreserving hT.quasiMeasurePreserving) he.le

lemma ae_eq_of_measurePreserving_ennreal_ge {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf1 : ∀ᵐ x ∂μ, f x ≤ 1)
    (hmono : ∀ᵐ x ∂μ, f (T x) ≤ f x) : f =ᵐ[μ] f ∘ T := by
  have hfT := hf.comp_quasiMeasurePreserving hT.quasiMeasurePreserving
  have he : ∫⁻ x, f (T x) ∂μ = ∫⁻ x, f x ∂μ := by
    have hf' : AEMeasurable f (μ.map T) := hT.map_eq.symm ▸ hf
    exact ((lintegral_map' hf' hT.measurable.aemeasurable).symm).trans
      (congrArg (fun ν : Measure α => ∫⁻ x, f x ∂ν) hT.map_eq)
  have hint : ∫⁻ x, f (T x) ∂μ < ∞ := by
    rw [he]
    exact (lintegral_mono_ae hf1).trans_lt (by simp)
  exact (ae_eq_of_ae_le_of_lintegral_le hmono hint.ne hf he.ge).symm

lemma realScaling_preimage_singleton (c : ℝ) (hc : c ≠ 0) :
    (Homeomorph.mulLeft₀ c hc) ⁻¹' ({0} : Set ℝ) = {0} := by
  ext x
  change c*x=0 ↔ x=0
  exact mul_eq_zero.trans (or_iff_right hc)

lemma realScaling_preimage_unitBall_subset (c : ℝ) (hc : 1 ≤ c) :
    (Homeomorph.mulLeft₀ c (ne_of_gt (zero_lt_one.trans_le hc))) ⁻¹' Metric.ball (0:ℝ) 1 ⊆
      Metric.ball 0 1 := by
  intro x hx
  simp only [Set.mem_preimage,Metric.mem_ball,Homeomorph.coe_mulLeft₀,Real.dist_eq,sub_zero] at hx ⊢
  rw [abs_mul,abs_of_nonneg (zero_le_one.trans hc)] at hx
  nlinarith [abs_nonneg x]

lemma realScaling_unitBall_subset_preimage (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    Metric.ball (0:ℝ) 1 ⊆ (Homeomorph.mulLeft₀ c hc.ne') ⁻¹' Metric.ball 0 1 := by
  intro x hx
  simp only [Set.mem_preimage,Metric.mem_ball,Homeomorph.coe_mulLeft₀,Real.dist_eq,sub_zero] at hx ⊢
  rw [abs_mul,abs_of_pos hc]
  nlinarith [abs_nonneg x]

lemma normalized_realScaling_atom (ν : Measure ℝ) (c : ℝ) (hc : c ≠ 0) :
    anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc)) (Metric.ball 0 1) {0} =
      (ν ((Homeomorph.mulLeft₀ c hc) ⁻¹' Metric.ball 0 1))⁻¹ * ν {0} := by
  change (ν.map (Homeomorph.mulLeft₀ c hc) (Metric.ball 0 1))⁻¹ *
    ν.map (Homeomorph.mulLeft₀ c hc) {0} = _
  rw [Measure.map_apply (Homeomorph.mulLeft₀ c hc).measurable Metric.isOpen_ball.measurableSet,
    Measure.map_apply (Homeomorph.mulLeft₀ c hc).measurable (measurableSet_singleton 0),
    realScaling_preimage_singleton]

 

theorem ae_atom_eq_of_scaling_covariance {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ)
    (ν : α → Measure ℝ) (hν : AEMeasurable ν μ)
    (hball : ∀ᵐ x ∂μ, ν x (Metric.ball 0 1) = 1)
    (c : ℝ) (hc : 0 < c)
    (hcov : ∀ᵐ x ∂μ, ν (T x) =
      anchorNormalize ((ν x).map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) :
    ∀ᵐ x ∂μ, ν x {0} = ν (T x) {0} := by
  have hm : AEMeasurable (fun x => ν x {0}) μ :=
    (Measure.measurable_coe (measurableSet_singleton 0)).comp_aemeasurable hν
  have hle : ∀ᵐ x ∂μ, ν x {0} ≤ 1 := by
    filter_upwards [hball] with x hx
    rw [←hx]
    exact measure_mono (singleton_subset_iff.mpr (Metric.mem_ball_self zero_lt_one))
  rcases le_total 1 c with h | h
  · apply ae_eq_of_measurePreserving_ennreal_le μ hT hm hle
    filter_upwards [hball,hcov] with x hx he
    rw [he,normalized_realScaling_atom]
    have hb : ν x ((Homeomorph.mulLeft₀ c hc.ne') ⁻¹' Metric.ball 0 1) ≤ 1 := by
      rw [←hx]
      exact measure_mono (realScaling_preimage_unitBall_subset c h)
    calc
      ν x {0} = 1 * ν x {0} := (one_mul _).symm
      _ ≤ _ := mul_le_mul' (ENNReal.one_le_inv.mpr hb) le_rfl
  · apply ae_eq_of_measurePreserving_ennreal_ge μ hT hm hle
    filter_upwards [hball,hcov] with x hx he
    rw [he,normalized_realScaling_atom]
    have hb : 1 ≤ ν x ((Homeomorph.mulLeft₀ c hc.ne') ⁻¹' Metric.ball 0 1) := by
      rw [←hx]
      exact measure_mono (realScaling_unitBall_subset_preimage c hc h)
    calc
      _ ≤ 1 * ν x {0} := mul_le_mul' (ENNReal.inv_le_one.mpr hb) le_rfl
      _ = ν x {0} := one_mul _

lemma scaling_ball_mass_of_atom_eq (ν : Measure ℝ) (c : ℝ) (hc : c ≠ 0)
    (h0 : ν {0} ≠ 0) (hT : ν {0} ≠ ∞)
    (he : anchorNormalize (ν.map (Homeomorph.mulLeft₀ c hc)) (Metric.ball 0 1) {0} = ν {0}) :
    ν ((Homeomorph.mulLeft₀ c hc) ⁻¹' Metric.ball 0 1) = 1 := by
  rw [normalized_realScaling_atom] at he
  have H := congrArg (fun a : ℝ≥0∞ => a*(ν {0})⁻¹) he
  rw [ENNReal.mul_inv_cancel_right h0 hT,ENNReal.mul_inv_cancel h0 hT] at H
  exact ENNReal.inv_eq_one.mp H

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma realScaling_preimage_ball (c r : ℝ) (hc : 0 < c) :
    (Homeomorph.mulLeft₀ c hc.ne') ⁻¹' Metric.ball (0:ℝ) r = Metric.ball 0 (r/c) := by
  ext x
  simp only [Set.mem_preimage,Metric.mem_ball,Homeomorph.coe_mulLeft₀,Real.dist_eq,sub_zero]
  rw [abs_mul,abs_of_pos hc]
  rw [lt_div_iff₀ hc,mul_comm c]

lemma real_iInter_ball_inv_nat :
    (⋂ m : ℕ, Metric.ball (0:ℝ) ((m+1:ℝ)⁻¹)) = {0} := by
  ext x
  simp only [mem_iInter,mem_singleton_iff,Metric.mem_ball,Real.dist_eq,sub_zero]
  constructor
  · intro h
    by_contra hx
    have hx0 : 0 < |x| := abs_pos.mpr hx
    obtain ⟨m,hm⟩ := exists_nat_gt (|x|⁻¹)
    have hm0 : (0:ℝ) < m+1 := by positivity
    have hh := h m
    have hl : (m+1:ℝ)⁻¹ < |x| := by
      rw [←one_div]
      apply (one_div_lt hm0 hx0).mpr
      simpa only [one_div] using hm.trans (by linarith : (m:ℝ) < m+1)
    exact (not_lt_of_ge hl.le) hh
  · rintro rfl m
    simp only [abs_zero]
    positivity

lemma realMeasure_eq_dirac_of_ball_masses (ν : Measure ℝ)
    (hsmall : ∀ m : ℕ, ν (Metric.ball 0 ((m+1:ℝ)⁻¹)) = 1)
    (hlarge : ∀ m : ℕ, ν (Metric.ball 0 (m+1:ℝ)) = 1) : ν = Measure.dirac 0 := by
  have hmono : Monotone (fun m : ℕ => Metric.ball (0:ℝ) (m+1:ℝ)) := by
    intro a b hab
    exact Metric.ball_subset_ball (by exact_mod_cast Nat.add_le_add_right hab 1)
  have hu : ν univ = 1 := by
    rw [← Metric.iUnion_ball_nat_succ (0:ℝ),hmono.measure_iUnion]
    simp only [hlarge,iSup_const]
  have hanti : Antitone (fun m : ℕ => Metric.ball (0:ℝ) ((m+1:ℝ)⁻¹)) := by
    intro a b hab
    apply Metric.ball_subset_ball
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
  have h0 : ν {0} = 1 := by
    rw [←real_iInter_ball_inv_nat,hanti.measure_iInter
      (fun _ => Metric.isOpen_ball.measurableSet.nullMeasurableSet) ⟨0,by rw [hsmall]; exact ENNReal.one_ne_top⟩]
    simp only [hsmall,iInf_const]
  let : IsFiniteMeasure ν := ⟨by rw [hu]; exact ENNReal.one_lt_top⟩
  have hc : ν ({0} : Set ℝ)ᶜ = 0 := by
    rw [measure_compl (measurableSet_singleton _) (by finiteness),hu,h0,tsub_self]
  ext s hs
  by_cases hx : (0:ℝ) ∈ s
  · rw [Measure.dirac_apply_of_mem hx]
    apply le_antisymm
    · simpa only [hu] using measure_mono (subset_univ s) (μ := ν)
    · rw [←h0]
      exact measure_mono (singleton_subset_iff.mpr hx)
  · simp only [Measure.dirac_apply,indicator_of_notMem hx]
    apply le_antisymm _ bot_le
    exact (measure_mono (subset_compl_singleton_iff.mpr hx)).trans hc.le

 

theorem ae_dirac_of_scaling_covariance {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (ν : α → Measure ℝ)
    (hν : AEMeasurable ν μ) (hball : ∀ᵐ x ∂μ, ν x (Metric.ball 0 1) = 1)
    (hscale : ∀ (c : ℝ) (hc : 0 < c), ∃ T : α → α,
      MeasurePreserving T μ μ ∧ ∀ᵐ x ∂μ, ν (T x) =
        anchorNormalize ((ν x).map (Homeomorph.mulLeft₀ c hc.ne')) (Metric.ball 0 1)) :
    ∀ᵐ x ∂μ, ν x {0} ≠ 0 → ν x = Measure.dirac 0 := by
  have H (c : ℝ) (hc : 0 < c) : ∀ᵐ x ∂μ, ν x {0} ≠ 0 → ν x (Metric.ball 0 (1/c)) = 1 := by
    obtain ⟨T,hT,hcov⟩ := hscale c hc
    have he := ae_atom_eq_of_scaling_covariance μ hT ν hν hball c hc hcov
    filter_upwards [hball,hcov,he] with x hx hc' he' h0
    have hT' : ν x {0} ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (by
      rw [←hx]
      exact measure_mono (singleton_subset_iff.mpr (Metric.mem_ball_self zero_lt_one)))
    have hh := scaling_ball_mass_of_atom_eq (ν x) c hc.ne' h0 hT' (by rw [←hc']; exact he'.symm)
    rwa [realScaling_preimage_ball c 1 hc] at hh
  have HS := ae_all_iff.mpr (fun m : ℕ => H (m+1) (by positivity))
  have HL := ae_all_iff.mpr (fun m : ℕ => H ((m+1:ℝ)⁻¹) (by positivity))
  filter_upwards [HS,HL] with x hs hl h0
  apply realMeasure_eq_dirac_of_ball_masses (ν x)
  · intro m
    simpa only [one_div] using hs m h0
  · intro m
    simpa only [one_div,inv_inv] using hl m h0

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem ae_intrinsicRootLeaf_atom_dirac (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x {0} ≠ 0 →
      intrinsicRootLeaf hij μ x = Measure.dirac 0 := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  apply ae_dirac_of_scaling_covariance μ (intrinsicRootLeaf hij μ)
    (aemeasurable_intrinsicRootLeaf hij μ hfree)
    ((ae_intrinsicRootLeaf_spec hij μ hfree).mono fun x hx => hx.2)
  intro c hc
  let ell := coordinateContractionWeights d j
  have hell : ∑ k, ell k = 0 := coordinateContractionWeights_sum d j
  let t := Real.log c / (d+1:ℝ)
  let a := diagonalOneParameter ell hell t
  have hinv : μ.map (fun x => rightAction x a) = μ := by
    rw [show a = diagonalFlow (fun k : Fin d => ell k.castSucc*t) from
      diagonalOneParameter_eq_diagonalFlow ell hell t]
    exact hA _
  refine ⟨(fun x => rightAction x a),⟨(continuous_rightAction a).measurable,hinv⟩,?_⟩
  have hrate : ell j-ell i = (d+1:ℝ) := by
    simp [ell,coordinateContractionWeights,hij]
  have he : Real.exp ((ell j-ell i)*t) = c := by
    rw [hrate]
    dsimp [t]
    rw [mul_comm,div_mul_cancel₀ _ (by positivity),Real.exp_log hc]
  have hs : rootTimeScaling ell i j t = Homeomorph.mulLeft₀ c hc.ne' := by
    apply Homeomorph.ext
    intro v
    simp only [rootTimeScaling,Homeomorph.coe_mulLeft₀,he]
  have H := ae_intrinsicRootLeaf_diagonal hij ell hell t μ hfree hinv
  simpa only [hs] using H

 

theorem ae_intrinsicRootLeaf_zero_atom_or_trivial (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x {0} = 0 ∨ intrinsicRootLeaf hij μ x = Measure.dirac 0 := by
  filter_upwards [ae_intrinsicRootLeaf_atom_dirac d hij μ hA] with x hx
  exact eq_or_ne _ _ |>.imp_right hx

end PrimeDegreePackets
end
end

end OAI
