import Mathlib
import OAI.NumberTheory.PrimePackets.LeafSupport

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
namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

theorem ae_leafMeasure_change_anchor (A B : RootBox hij k) (R S : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0) (hBS : B.time ⊆ rootLeafWindow S 0)
    (hAB : A.time ⊆ B.time) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ B.transverse →
      A.leafMeasure R μ s = anchorNormalize (B.leafMeasure S μ s) A.time := by
  let C := rootLongBoxFamily hij k S
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k S m).to_subtype
  have hT (m : ℕ) (D : C m) : D.val.time = rootLeafWindow S m :=
    rootLongBoxFamily_time hij k S m D.val D.prop
  have hinc (m : ℕ) (D : C m) : B.time ⊆ D.val.time := by
    rw [hT m D]
    exact hBS.trans (rootLeafWindow_mono S (Nat.zero_le m))
  have hA : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ (m : ℕ) (D : C m),
      s ∈ D.val.transverse → D.val.conditionalKernel μ s A.time ≠ 0 ∧
      (A.leafMeasure R μ s).restrict D.val.time =
        (anchorNormalize (D.val.conditionalKernel μ s) A.time).restrict D.val.time := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro D
    exact A.ae_leafMeasure_restrict R hAR μ hfree D.val (hAB.trans (hinc m D))
  have hB := base_ae_of_ae A B hAB μ (B.ae_leafMeasure_spec S hBS μ hfree)
  filter_upwards [hA,hB,A.ae_injective_root_slice_of_ae_free μ hfree] with s hsA hsB hi
  intro hsBt
  have hsB' := hsB hsBt
  apply measure_eq_of_restrictionChain (rootLeafWindow S) (rootLeafWindow_mono S)
    (rootLeafWindow_cover S)
  intro m
  obtain ⟨D,hDC,hsD⟩ := rootLongBoxFamily_covers hij k S m s hi
  let D' : C m := ⟨D,hDC⟩
  have ha := hsA m D' hsD
  have hb := hsB'.2.2.2 m D hDC hsD
  have hBD : B.time ⊆ rootLeafWindow S m := hBS.trans (rootLeafWindow_mono S (Nat.zero_le m))
  have hAD : A.time ⊆ rootLeafWindow S m := hAB.trans hBD
  have hmB : D.conditionalKernel μ s B.time ≠ 0 :=
    (lt_of_lt_of_le (pos_iff_ne_zero.mpr ha.1) (measure_mono hAB)).ne'
  have he := congrArg (fun ν : Measure ℝ => anchorNormalize ν A.time) hb
  rw [anchorNormalize_restrict_comm _ A.time_open.measurableSet hAD,
    anchorNormalize_restrict_comm _ A.time_open.measurableSet hAD,
    anchorNormalize_twice _ _ _ hmB (measure_ne_top _ _)] at he
  rw [he]
  simpa only [hT m D'] using ha.2

 

theorem ae_change_anchor_mass (A B : RootBox hij k) (R S : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0) (hBS : B.time ⊆ rootLeafWindow S 0)
    (hAB : A.time ⊆ B.time) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ B.transverse →
      B.leafMeasure S μ s A.time ≠ 0 ∧ B.leafMeasure S μ s A.time ≠ ∞ := by
  filter_upwards [A.ae_leafMeasure_change_anchor B R S hAR hBS hAB μ hfree,
    A.ae_leafMeasure_spec R hAR μ hfree] with s hs hspec
  intro hsB
  have H : anchorNormalize (B.leafMeasure S μ s) A.time A.time = 1 := by
    rw [←hs hsB]
    exact hspec.2.1
  constructor
  · intro hz
    simp only [anchorNormalize,Measure.smul_apply,smul_eq_mul,hz,mul_zero] at H
    exact zero_ne_one H
  · intro hz
    simp only [anchorNormalize,Measure.smul_apply,smul_eq_mul,hz,ENNReal.inv_top,zero_mul] at H
    exact zero_ne_one H

 

theorem ae_basedLeaf_change_anchor (A B : RootBox hij k) (R S : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0) (hBS : B.time ⊆ rootLeafWindow S 0)
    (hAB : A.time ⊆ B.time) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ, z.1 ∈ B.transverse →
      A.basedLeaf R μ z = B.basedLeaf S μ z := by
  have he := ae_of_ae_map measurable_fst.aemeasurable
    (A.ae_leafMeasure_change_anchor B R S hAR hBS hAB μ hfree)
  have hm := ae_of_ae_map measurable_fst.aemeasurable
    (A.ae_change_anchor_mass B R S hAR hBS hAB μ hfree)
  filter_upwards [he,hm] with z hz hmz
  intro hsB
  change basedRealMeasure (A.leafMeasure R μ z.1) z.2 = basedRealMeasure (B.leafMeasure S μ z.1) z.2
  rw [hz hsB]
  exact basedRealMeasure_smul _ _ (ENNReal.inv_ne_zero.mpr (hmz hsB).2)
    (ENNReal.inv_ne_top.mpr (hmz hsB).1) _

end PrimeDegreePackets.RootBox


namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

theorem ae_basedLeaf_overlap (A B : RootBox hij k) (R S : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0) (hBS : B.time ⊆ rootLeafWindow S 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ, z ∈ B.domain →
      A.basedLeaf R μ z = B.basedLeaf S μ z := by
  let U := A.transverse ∩ B.transverse
  let J := A.time ∩ B.time
  have hU : IsOpen U := A.transverse_open.inter B.transverse_open
  have hJ : IsOpen J := A.time_open.inter B.time_open
  let D := A.shrink U J hU hJ inter_subset_left inter_subset_left
  have hDR : D.time ⊆ rootLeafWindow R 0 := inter_subset_left.trans hAR
  have hDA := D.ae_basedLeaf_change_anchor A R R hDR hAR inter_subset_left μ hfree
  have hDB := D.ae_basedLeaf_change_anchor B R S hDR hBS inter_subset_right μ hfree
  have H : ∀ᵐ z ∂D.coordinateMeasure μ, A.basedLeaf R μ z = B.basedLeaf S μ z := by
    filter_upwards [hDA,hDB,D.coordinateMeasure_ae_domain μ] with z hzA hzB hzD
    exact (hzA hzD.1.1).symm.trans (hzB hzD.1.2)
  rw [shrink_coordinateMeasure] at H
  have H' := (ae_restrict_iff' (hU.measurableSet.prod hJ.measurableSet)).mp H
  filter_upwards [H',A.coordinateMeasure_ae_domain μ] with z hz hzA
  intro hzB
  exact hz ⟨⟨hzA.1,hzB.1⟩,⟨hzA.2,hzB.2⟩⟩

end PrimeDegreePackets.RootBox


namespace PrimeDegreePackets
variable {n : ℕ} {i j k l : Fin n} (hij : i ≠ j)

abbrev RootSliceOverlap (i j k l : Fin n) (γ : G n) :=
  {s : RootSlice i j k // (γ * s.val).1 l i ≠ 0}

def rootTransitionPivot (γ : G n) (s : RootSliceOverlap i j k l γ) : RootPivot i l :=
  ⟨γ * s.val.val,s.prop⟩

def rootTransitionTime (γ : G n) (s : RootSliceOverlap i j k l γ) : ℝ :=
  rootParameter i j l (γ * s.val.val)

lemma rootTransition_inverse_mul (γ : G n) (s : RootSliceOverlap i j k l γ) :
    γ⁻¹ * (rootSliceRepresentative hij (rootTransitionPivot γ s)).val =
      s.val.val * Matrix.SpecialLinearGroup.transvection hij (-rootTransitionTime γ s) := by
  change γ⁻¹ * ((γ * s.val.val) * _) = _
  rw [←mul_assoc,inv_mul_cancel_left]
  rfl

def rootTransitionSlice (γ : G n) (s : RootSliceOverlap i j k l γ) :
    RootSliceOverlap i j l k γ⁻¹ :=
  ⟨rootSliceRepresentative hij (rootTransitionPivot γ s),by
    rw [rootTransition_inverse_mul,root_mul_entry,ite_eq_right hij,add_zero]
    exact s.val.prop.1⟩

lemma rootTransitionTime_inverse (γ : G n) (s : RootSliceOverlap i j k l γ) :
    rootTransitionTime γ⁻¹ (rootTransitionSlice hij γ s) = -rootTransitionTime γ s := by
  unfold rootTransitionTime
  change rootParameter i j k (γ⁻¹ * (rootSliceRepresentative hij (rootTransitionPivot γ s)).val) = _
  rw [rootTransition_inverse_mul]
  have H := rootParameter_translate hij (⟨s.val.val,s.val.prop.1⟩ : RootPivot i k)
    (-rootTransitionTime γ s)
  simpa only [rootPivotTranslate,rootParameter,s.val.prop.2,zero_div,zero_add,rootTransitionTime] using H

lemma rootTransitionSlice_inverse (γ : G n) (s : RootSliceOverlap i j k l γ) :
    (rootTransitionSlice hij γ⁻¹ (rootTransitionSlice hij γ s)).val.val = s.val.val := by
  change (γ⁻¹ * (rootSliceRepresentative hij (rootTransitionPivot γ s)).val) *
    Matrix.SpecialLinearGroup.transvection hij
      (-rootTransitionTime γ⁻¹ (rootTransitionSlice hij γ s)) = _
  rw [rootTransition_inverse_mul,rootTransitionTime_inverse,mul_assoc,
    ←Matrix.SpecialLinearGroup.transvection_add,neg_neg,neg_add_cancel,
    Matrix.SpecialLinearGroup.transvection_coeff_zero,mul_one]

lemma continuous_rootTransitionPivot (γ : G n) :
    Continuous (rootTransitionPivot (i := i) (j := j) (k := k) (l := l) γ) := by
  apply Continuous.subtype_mk
  exact continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val)

lemma continuous_rootTransitionTime (γ : G n) :
    Continuous (rootTransitionTime (i := i) (j := j) (k := k) (l := l) γ) :=
  continuous_rootParameter.comp (continuous_rootTransitionPivot γ)

lemma continuous_rootTransitionSlice (γ : G n) :
    Continuous (rootTransitionSlice (k := k) (l := l) hij γ) := by
  apply Continuous.subtype_mk
  exact (continuous_rootSliceRepresentative hij).comp (continuous_rootTransitionPivot γ)

 

def rootSliceTransition (γ : G n) :
    RootSliceOverlap i j k l γ ≃ₜ RootSliceOverlap i j l k γ⁻¹ where
  toFun := rootTransitionSlice hij γ
  invFun s := ⟨(rootTransitionSlice hij γ⁻¹ s).val, by
    simpa only [inv_inv] using (rootTransitionSlice hij γ⁻¹ s).prop⟩
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    exact rootTransitionSlice_inverse hij γ s
  right_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    simpa only [rootTransitionSlice,rootTransitionPivot,rootSliceRepresentative,inv_inv]
      using rootTransitionSlice_inverse hij γ⁻¹ s
  continuous_toFun := continuous_rootTransitionSlice hij γ
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (continuous_rootTransitionSlice (k := l) (l := k) hij γ⁻¹)

lemma rootTransition_reconstruct (γ : G n) (s : RootSliceOverlap i j k l γ) (t : ℝ) :
    (rootTransitionSlice hij γ s).val.val *
        Matrix.SpecialLinearGroup.transvection hij (t + rootTransitionTime γ s) =
      γ * (s.val.val * Matrix.SpecialLinearGroup.transvection hij t) := by
  change ((γ * s.val.val) * Matrix.SpecialLinearGroup.transvection hij (-rootTransitionTime γ s)) *
    Matrix.SpecialLinearGroup.transvection hij (t + rootTransitionTime γ s) = _
  rw [mul_assoc,←Matrix.SpecialLinearGroup.transvection_add]
  have h : -rootTransitionTime γ s + (t + rootTransitionTime γ s) = t := by ring
  rw [h,mul_assoc]

end PrimeDegreePackets


namespace PrimeDegreePackets
variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] [MeasurableSpace δ]

 
def restrictFibers (κ : Kernel α β) [IsSFiniteKernel κ]
    (T : Set (α × β)) (hT : MeasurableSet T) : Kernel α β where
  toFun a := (κ a).restrict (Prod.mk a ⁻¹' T)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    have H := Kernel.measurable_kernel_prodMk_left (κ := κ) ((measurable_snd hS).inter hT)
    convert H using 1
    funext a
    exact Measure.restrict_apply hS

instance restrictFibers_finite (κ : Kernel α β) [IsFiniteKernel κ]
    (T : Set (α × β)) (hT : MeasurableSet T) : IsFiniteKernel (restrictFibers κ T hT) := by
  refine ⟨κ.bound,κ.bound_lt_top,fun a => ?_⟩
  change (κ a).restrict (Prod.mk a ⁻¹' T) univ ≤ κ.bound
  exact (Measure.restrict_le_self _).trans (κ.measure_le_bound a univ)

lemma compProd_restrict_fibers (μ : Measure α) [SFinite μ]
    (κ : Kernel α β) [IsFiniteKernel κ] (T : Set (α × β)) (hT : MeasurableSet T) :
    (μ ⊗ₘ κ).restrict T = μ ⊗ₘ restrictFibers κ T hT := by
  ext S hS
  rw [Measure.restrict_apply hS,Measure.compProd_apply (hS.inter hT),Measure.compProd_apply hS]
  apply lintegral_congr
  intro a
  exact (Measure.restrict_apply (measurable_prodMk_left hS)).symm

lemma conditional_restrict_marginal [StandardBorelSpace β] [Nonempty β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ] (T : Set (α × β)) (hT : MeasurableSet T) :
    (ρ.restrict T).fst = ρ.fst.withDensity (fun a => ρ.condKernel a (Prod.mk a ⁻¹' T)) := by
  have H := compProd_restrict_fibers ρ.fst ρ.condKernel T hT
  rw [Measure.disintegrate] at H
  rw [H,fst_compProd_withDensity]
  congr 1
  funext a
  change (ρ.condKernel a).restrict (Prod.mk a ⁻¹' T) univ = _
  rw [Measure.restrict_apply MeasurableSet.univ,univ_inter]

 

theorem conditional_restrict_fibers [StandardBorelSpace β] [Nonempty β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ] (T : Set (α × β)) (hT : MeasurableSet T) :
    ∀ᵐ a ∂ρ.fst, ρ.condKernel a (Prod.mk a ⁻¹' T) • (ρ.restrict T).condKernel a =
      (ρ.condKernel a).restrict (Prod.mk a ⁻¹' T) := by
  let σ := ρ.restrict T
  let w := fun a => ρ.condKernel a (Prod.mk a ⁻¹' T)
  have hw : Measurable w := Kernel.measurable_kernel_prodMk_left hT
  let κ := scaleBaseKernel σ.condKernel w hw
  let : IsFiniteKernel κ := scaleBaseKernel_finite σ.condKernel w hw (fun a => prob_le_one)
  have he : ρ.fst ⊗ₘ κ = ρ.fst ⊗ₘ restrictFibers ρ.condKernel T hT := by
    calc
      _ = ρ.fst.withDensity w ⊗ₘ σ.condKernel := compProd_scaleBaseKernel _ _ w hw
      _ = σ.fst ⊗ₘ σ.condKernel := by rw [conditional_restrict_marginal ρ T hT]
      _ = σ := Measure.disintegrate σ σ.condKernel
      _ = ρ.fst ⊗ₘ restrictFibers ρ.condKernel T hT := by
        rw [←compProd_restrict_fibers,Measure.disintegrate]
  exact Kernel.ae_eq_of_compProd_eq he

 

def mapFibers (κ : Kernel α β) [IsSFiniteKernel κ]
    (F : α × β → δ) (hF : Measurable F) : Kernel α δ where
  toFun a := (κ a).map (fun b => F (a,b))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    have H := Kernel.measurable_kernel_prodMk_left (κ := κ) (hF hS)
    convert H using 1
    funext a
    exact Measure.map_apply ((show Measurable (fun b => F (a,b)) from hF.comp measurable_prodMk_left)) hS

lemma mapFibers_apply (κ : Kernel α β) [IsSFiniteKernel κ]
    (F : α × β → δ) (hF : Measurable F) (a : α) :
    mapFibers κ F hF a = (κ a).map (fun b => F (a,b)) := rfl

instance mapFibers_finite (κ : Kernel α β) [IsFiniteKernel κ]
    (F : α × β → δ) (hF : Measurable F) : IsFiniteKernel (mapFibers κ F hF) := by
  refine ⟨κ.bound,κ.bound_lt_top,fun a => ?_⟩
  change (κ a).map (fun b => F (a,b)) univ ≤ κ.bound
  rw [Measure.map_apply ((show Measurable (fun b => F (a,b)) from hF.comp measurable_prodMk_left)) MeasurableSet.univ,preimage_univ]
  exact κ.measure_le_bound a univ

lemma fst_map_fibers (ρ : Measure (α × β)) (e : α ≃ᵐ γ)
    (F : α × β → δ) (hF : Measurable F) :
    (ρ.map (fun z => (e z.1,F z))).fst = ρ.fst.map e := by
  have hfull : Measurable (fun z : α × β => (e z.1,F z)) :=
    (e.measurable.comp measurable_fst).prodMk hF
  rw [Measure.fst,Measure.map_map measurable_fst hfull,
    Measure.fst,Measure.map_map e.measurable measurable_fst]
  rfl

lemma compProd_map_fibers (μ : Measure α) [SFinite μ] (κ : Kernel α β)
    [IsFiniteKernel κ] (e : α ≃ᵐ γ) (F : α × β → δ) (hF : Measurable F) :
    (μ ⊗ₘ κ).map (fun z => (e z.1,F z)) =
      μ.map e ⊗ₘ (mapFibers κ F hF).comap e.symm e.symm.measurable := by
  have hfull : Measurable (fun z : α × β => (e z.1,F z)) :=
    (e.measurable.comp measurable_fst).prodMk hF
  ext S hS
  rw [Measure.map_apply hfull hS,Measure.compProd_apply (hfull hS),Measure.compProd_apply hS,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hS) e.measurable]
  apply lintegral_congr
  intro a
  rw [Kernel.comap_apply,e.symm_apply_apply,mapFibers_apply]
  exact (Measure.map_apply ((show Measurable (fun b => F (a,b)) from hF.comp measurable_prodMk_left))
    (show MeasurableSet (Prod.mk (e a) ⁻¹' S) from measurable_prodMk_left hS)).symm

 

theorem conditional_map_fibers [StandardBorelSpace β] [Nonempty β]
    [StandardBorelSpace δ] [Nonempty δ] (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    (e : α ≃ᵐ γ) (F : α × β → δ) (hF : Measurable F) :
    ∀ᵐ a ∂ρ.fst, (ρ.map (fun z => (e z.1,F z))).condKernel (e a) =
      (ρ.condKernel a).map (fun b => F (a,b)) := by
  let κ := (mapFibers ρ.condKernel F hF).comap e.symm e.symm.measurable
  have he : ρ.map (fun z => (e z.1,F z)) = (ρ.map (fun z => (e z.1,F z))).fst ⊗ₘ κ := by
    rw [fst_map_fibers ρ e F hF,←compProd_map_fibers ρ.fst ρ.condKernel e F hF,Measure.disintegrate]
  have H := eq_condKernel_of_measure_eq_compProd κ he
  rw [fst_map_fibers ρ e F hF] at H
  have H' := ae_of_ae_map e.measurable.aemeasurable H
  filter_upwards [H'] with a ha
  exact (by simpa only [κ,Kernel.comap_apply,e.symm_apply_apply,mapFibers_apply] using ha.symm)

end PrimeDegreePackets


namespace PrimeDegreePackets

 
def fiberShear {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) (τ : α → ℝ) (hτ : Continuous τ) : (α × ℝ) ≃ₜ (β × ℝ) where
  toFun z := (e z.1,z.2 + τ z.1)
  invFun z := (e.symm z.1,z.2 - τ (e.symm z.1))
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  continuous_toFun := (e.continuous.comp continuous_fst).prodMk
    (continuous_snd.add (hτ.comp continuous_fst))
  continuous_invFun := (e.symm.continuous.comp continuous_fst).prodMk
    (continuous_snd.sub (hτ.comp (e.symm.continuous.comp continuous_fst)))

def rootTransitionCoordinates {n : ℕ} {i j k l : Fin n} (hij : i ≠ j) (γ : G n) :
    (RootSliceOverlap i j k l γ × ℝ) ≃ₜ (RootSliceOverlap i j l k γ⁻¹ × ℝ) :=
  fiberShear (rootSliceTransition hij γ) (rootTransitionTime γ) (continuous_rootTransitionTime γ)

lemma rootTransitionCoordinates_param {n : ℕ} {i j k l : Fin n}
    (hij : i ≠ j) (γ : G n) (hγ : γ ∈ integralGroup n)
    (z : RootSliceOverlap i j k l γ × ℝ) :
    rootQuotientParametrization hij ((rootTransitionCoordinates hij γ z).1.val,
      (rootTransitionCoordinates hij γ z).2) =
      rootQuotientParametrization hij (z.1.val,z.2) := by
  change Quotient.mk _ ((rootTransitionSlice hij γ z.1).val.val *
    Matrix.SpecialLinearGroup.transvection hij (z.2 + rootTransitionTime γ z.1)) =
    Quotient.mk _ (z.1.val.val * Matrix.SpecialLinearGroup.transvection hij z.2)
  rw [rootTransition_reconstruct]
  symm
  apply Quotient.sound
  change (QuotientGroup.rightRel (integralGroup n))
    (z.1.val.val * Matrix.SpecialLinearGroup.transvection hij z.2)
    (γ * (z.1.val.val * Matrix.SpecialLinearGroup.transvection hij z.2))
  rw [QuotientGroup.rightRel_apply,mul_inv_cancel_right]
  exact hγ

lemma centerRealMeasure_translate (ν : Measure ℝ) (t u : ℝ) :
    centerRealMeasure (ν.map (Homeomorph.addRight u)) (t+u) = centerRealMeasure ν t := by
  unfold centerRealMeasure
  rw [Measure.map_map (Homeomorph.subRight (t+u)).measurable (Homeomorph.addRight u).measurable]
  congr 1
  funext x
  change (x+u)-(t+u)=x-t
  ring

lemma basedRealMeasure_translate (ν : Measure ℝ) (t u : ℝ) :
    basedRealMeasure (ν.map (Homeomorph.addRight u)) (t+u) = basedRealMeasure ν t := by
  unfold basedRealMeasure
  rw [centerRealMeasure_translate]

 
theorem conditional_rootTransition {n : ℕ} {i j k l : Fin n} (hij : i ≠ j) (γ : G n)
    (ρ : Measure (RootSliceOverlap i j k l γ × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ s ∂ρ.fst, (ρ.map (rootTransitionCoordinates hij γ)).condKernel
        (rootTransitionSlice hij γ s) =
      (ρ.condKernel s).map (Homeomorph.addRight (rootTransitionTime γ s)) := by
  exact conditional_map_fibers ρ (rootSliceTransition hij γ).toMeasurableEquiv
    (fun z => z.2 + rootTransitionTime γ z.1)
    (measurable_snd.add ((continuous_rootTransitionTime γ).measurable.comp measurable_fst))

 

theorem based_conditional_rootTransition {n : ℕ} {i j k l : Fin n}
    (hij : i ≠ j) (γ : G n)
    (ρ : Measure (RootSliceOverlap i j k l γ × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ z ∂ρ, basedRealMeasure
      ((ρ.map (rootTransitionCoordinates hij γ)).condKernel (rootTransitionSlice hij γ z.1))
        (z.2 + rootTransitionTime γ z.1) = basedRealMeasure (ρ.condKernel z.1) z.2 := by
  have H := ae_of_ae_map measurable_fst.aemeasurable (conditional_rootTransition hij γ ρ)
  filter_upwards [H] with z hz
  rw [hz,basedRealMeasure_translate]

end PrimeDegreePackets
end
end

end OAI
