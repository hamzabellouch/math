import Mathlib
import OAI.NumberTheory.PrimePackets.ConditionalFibers

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
variable {n : ℕ} {i j k l : Fin n} {hij : i ≠ j}

lemma transition_source_fiber (B : RootBox hij l) (γ : G n)
    (s : RootSliceOverlap i j k l γ)
    (hs : (rootTransitionSlice hij γ s).val ∈ B.transverse) :
    Prod.mk s ⁻¹' ((rootTransitionCoordinates hij γ) ⁻¹' B.overlapDomain γ⁻¹ k) =
      (Homeomorph.addRight (rootTransitionTime γ s)) ⁻¹' B.time := by
  ext t
  change (_ ∧ _) ↔ _
  exact and_iff_right hs

lemma transition_target_fiber (A : RootBox hij k) (γ : G n)
    (s : RootSliceOverlap i j k l γ) (hs : s.val ∈ A.transverse) :
    Prod.mk (rootTransitionSlice hij γ s) ⁻¹'
      ((rootTransitionCoordinates hij γ) '' A.overlapDomain γ l) =
      (Homeomorph.addRight (rootTransitionTime γ s)) '' A.time := by
  ext t
  constructor
  · rintro ⟨z,hz,he⟩
    have hbase : (rootSliceTransition hij γ) z.1 = (rootSliceTransition hij γ) s :=
      congrArg Prod.fst he
    have hzs : z.1 = s := (rootSliceTransition hij γ).injective hbase
    refine ⟨z.2,hz.2,?_⟩
    have ht := congrArg Prod.snd he
    change z.2 + rootTransitionTime γ z.1 = t at ht
    change z.2 + rootTransitionTime γ s = t
    simpa only [hzs] using ht
  · rintro ⟨v,hv,rfl⟩
    exact ⟨(s,v),⟨hs,hv⟩,rfl⟩

 

theorem overlap_conditional_projective_explicit (A : RootBox hij k) (B : RootBox hij l)
    (γ : G n) (hγ : γ ∈ integralGroup n) (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(A.transitionOverlapMeasure B γ μ).fst,
      let f := Homeomorph.addRight (rootTransitionTime γ s)
      A.conditionalKernel μ s.val (f ⁻¹' B.time) ≠ 0 ∧
      B.conditionalKernel μ (rootTransitionSlice hij γ s).val (f '' A.time) ≠ 0 ∧
      ((anchorNormalize (A.conditionalKernel μ s.val) (f ⁻¹' B.time)).restrict (f ⁻¹' B.time)).map f =
      (anchorNormalize (B.conditionalKernel μ (rootTransitionSlice hij γ s).val) (f '' A.time)).restrict
        (f '' A.time) := by
  have HA := A.transition_base_ae_source B γ μ (A.coordinateMeasure_fst_ae_transverse μ)
  have HB := A.transition_base_ae_target B γ hγ μ (B.coordinateMeasure_fst_ae_transverse μ)
  filter_upwards [A.overlap_conditional_projective B γ hγ μ,HA,HB] with s hs ha hb
  simpa only [B.transition_source_fiber γ s hb,A.transition_target_fiber γ s ha] using hs

end PrimeDegreePackets.RootBox


namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k l : Fin n} {hij : i ≠ j}

lemma ae_leafMeasure_restrict_conditional (A D : RootBox hij k)
    (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0) (hAD : A.time ⊆ D.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ D.transverse →
      D.conditionalKernel μ s A.time ≠ 0 ∧
      (A.leafMeasure R μ s).restrict D.time =
        (D.conditionalKernel μ s A.time)⁻¹ • D.conditionalKernel μ s := by
  have H := base_ae_of_ae A D hAD μ (D.conditionalKernel_ae_time μ)
  filter_upwards [A.ae_leafMeasure_restrict R hAR μ hfree D hAD,H] with s hs ht
  intro hsD
  refine ⟨(hs hsD).1,?_⟩
  rw [(hs hsD).2,anchorNormalize,Measure.restrict_smul,
    Measure.restrict_eq_self_of_ae_mem (ht hsD)]

 

theorem ae_leafTransition_restrict (A D : RootBox hij k) (B F : RootBox hij l)
    (R S : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0) (hBS : B.time ⊆ rootLeafWindow S 0)
    (hAD : A.time ⊆ D.time) (hBF : B.time ⊆ F.time)
    (γ : G n) (hγ : γ ∈ integralGroup n) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.transitionOverlapMeasure B γ μ).fst,
      s.val ∈ D.transverse → (rootTransitionSlice hij γ s).val ∈ F.transverse →
      let f := Homeomorph.addRight (rootTransitionTime γ s)
      let J := A.time ∩ f ⁻¹' B.time
      ((anchorNormalize (A.leafMeasure R μ s.val) J).restrict
        (f ⁻¹' F.time ∩ D.time)).map f =
      (anchorNormalize (B.leafMeasure S μ (rootTransitionSlice hij γ s).val) (f '' J)).restrict
        (f '' D.time ∩ F.time) := by
  have HA := A.transition_base_ae_source B γ μ
    (A.ae_leafMeasure_restrict_conditional D R hAR hAD μ hfree)
  have HB := A.transition_base_ae_target B γ hγ μ
    (B.ae_leafMeasure_restrict_conditional F S hBS hBF μ hfree)
  have HD := A.transition_base_ae_of_ae D B F hAD hBF γ μ
    (D.overlap_conditional_projective_explicit F γ hγ μ)
  filter_upwards [HA,HB,HD] with s ha hb hd
  intro hsD hsF f J
  have hJ : MeasurableSet J := A.time_open.measurableSet.inter (f.measurable B.time_open.measurableSet)
  have hJD : J ⊆ D.time := inter_subset_left.trans hAD
  have hJV : J ⊆ f ⁻¹' F.time := fun t ht => hBF ht.2
  have hJE : f '' J ⊆ F.time := by
    rintro _ ⟨t,ht,rfl⟩
    exact hBF ht.2
  have hJW : f '' J ⊆ f '' D.time := image_mono hJD
  have hDA := ha hsD
  have hFB := hb hsF
  have hDF := hd hsD hsF
  exact projective_extensions_overlap _ _ _ _ f.toMeasurableEquiv
    D.time_open.measurableSet F.time_open.measurableSet hJ hJD hJV hJE hJW
    _ _ (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) (ENNReal.inv_ne_top.mpr hDA.1)
    (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) (ENNReal.inv_ne_top.mpr hFB.1)
    hDA.2 hFB.2 hDF.1 (measure_ne_top _ _) hDF.2.1 (measure_ne_top _ _) hDF.2.2

end PrimeDegreePackets.RootBox


namespace PrimeDegreePackets

lemma translated_window_chain_cover (R S u : ℝ) :
    ⋃ m : ℕ, ((Homeomorph.addRight u) '' rootLeafWindow R m ∩ rootLeafWindow S m) = univ := by
  apply Set.eq_univ_of_forall
  intro t
  have h₁ : t-u ∈ ⋃ m, rootLeafWindow R m := by rw [rootLeafWindow_cover]; trivial
  have h₂ : t ∈ ⋃ m, rootLeafWindow S m := by rw [rootLeafWindow_cover]; trivial
  obtain ⟨a,ha⟩ := mem_iUnion.mp h₁
  obtain ⟨b,hb⟩ := mem_iUnion.mp h₂
  refine mem_iUnion.mpr ⟨max a b,⟨t-u,rootLeafWindow_mono R (le_max_left _ _) ha,?_⟩,
    rootLeafWindow_mono S (le_max_right _ _) hb⟩
  change (t-u)+u=t
  ring

namespace RootBox
variable {n : ℕ} {i j k l : Fin n} {hij : i ≠ j}

 

theorem ae_leafTransition (A : RootBox hij k) (B : RootBox hij l)
    (R S : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0) (hBS : B.time ⊆ rootLeafWindow S 0)
    (γ : G n) (hγ : γ ∈ integralGroup n) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.transitionOverlapMeasure B γ μ).fst,
      let f := Homeomorph.addRight (rootTransitionTime γ s)
      let J := A.time ∩ f ⁻¹' B.time
      (anchorNormalize (A.leafMeasure R μ s.val) J).map f =
        anchorNormalize (B.leafMeasure S μ (rootTransitionSlice hij γ s).val) (f '' J) := by
  let C := rootLongBoxFamily hij k R
  let D := rootLongBoxFamily hij l S
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k R m).to_subtype
  let (m : ℕ) : Countable (D m) := (rootLongBoxFamily_countable hij l S m).to_subtype
  have hC (m : ℕ) (K : C m) : K.val.time = rootLeafWindow R m :=
    rootLongBoxFamily_time hij k R m K.val K.prop
  have hD (m : ℕ) (L : D m) : L.val.time = rootLeafWindow S m :=
    rootLongBoxFamily_time hij l S m L.val L.prop
  have hAC (m : ℕ) (K : C m) : A.time ⊆ K.val.time := by
    rw [hC m K]
    exact hAR.trans (rootLeafWindow_mono R (Nat.zero_le m))
  have hBD (m : ℕ) (L : D m) : B.time ⊆ L.val.time := by
    rw [hD m L]
    exact hBS.trans (rootLeafWindow_mono S (Nat.zero_le m))
  have H : ∀ᵐ s ∂(A.transitionOverlapMeasure B γ μ).fst,
      ∀ (m : ℕ) (K : C m) (L : D m), s.val ∈ K.val.transverse →
        (rootTransitionSlice hij γ s).val ∈ L.val.transverse →
      let f := Homeomorph.addRight (rootTransitionTime γ s)
      let J := A.time ∩ f ⁻¹' B.time
      ((anchorNormalize (A.leafMeasure R μ s.val) J).restrict
        (f ⁻¹' L.val.time ∩ K.val.time)).map f =
      (anchorNormalize (B.leafMeasure S μ (rootTransitionSlice hij γ s).val) (f '' J)).restrict
        (f '' K.val.time ∩ L.val.time) := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro K
    apply ae_all_iff.mpr
    intro L
    exact A.ae_leafTransition_restrict K.val B L.val R S hAR hBS (hAC m K) (hBD m L) γ hγ μ hfree
  have HA := A.transition_base_ae_source B γ μ (A.ae_injective_root_slice_of_ae_free μ hfree)
  have HB := A.transition_base_ae_target B γ hγ μ (B.ae_injective_root_slice_of_ae_free μ hfree)
  filter_upwards [H,HA,HB] with s hs ha hb
  intro f J
  let W := fun m => f '' rootLeafWindow R m ∩ rootLeafWindow S m
  have hW : Monotone W := fun a b hab =>
    inter_subset_inter (image_mono (rootLeafWindow_mono R hab)) (rootLeafWindow_mono S hab)
  apply measure_eq_of_restrictionChain W hW (translated_window_chain_cover R S (rootTransitionTime γ s))
  intro m
  obtain ⟨K,hKC,hsK⟩ := rootLongBoxFamily_covers hij k R m s.val ha
  obtain ⟨L,hLD,hsL⟩ := rootLongBoxFamily_covers hij l S m (rootTransitionSlice hij γ s).val hb
  let K' : C m := ⟨K,hKC⟩
  let L' : D m := ⟨L,hLD⟩
  have he := hs m K' L' hsK hsL
  rw [hC m K',hD m L'] at he
  rw [f.measurableEmbedding.restrict_map]
  have hpre : f ⁻¹' W m = f ⁻¹' rootLeafWindow S m ∩ rootLeafWindow R m := by
    rw [show W m = f '' rootLeafWindow R m ∩ rootLeafWindow S m from rfl,
      preimage_inter,f.preimage_image,inter_comm]
  rw [hpre]
  exact he

 

theorem ae_leafTransition_anchor_mass (A : RootBox hij k) (B : RootBox hij l)
    (R S : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0) (hBS : B.time ⊆ rootLeafWindow S 0)
    (γ : G n) (hγ : γ ∈ integralGroup n) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.transitionOverlapMeasure B γ μ).fst,
      let f := Homeomorph.addRight (rootTransitionTime γ s)
      let J := A.time ∩ f ⁻¹' B.time
      A.leafMeasure R μ s.val J ≠ 0 ∧ A.leafMeasure R μ s.val J ≠ ∞ ∧
      B.leafMeasure S μ (rootTransitionSlice hij γ s).val (f '' J) ≠ 0 ∧
      B.leafMeasure S μ (rootTransitionSlice hij γ s).val (f '' J) ≠ ∞ := by
  have HA := A.transition_base_ae_source B γ μ (A.ae_leafMeasure_spec R hAR μ hfree)
  have HB := A.transition_base_ae_target B γ hγ μ (B.ae_leafMeasure_spec S hBS μ hfree)
  filter_upwards [HA,HB,A.overlap_conditional_projective_explicit B γ hγ μ] with s ha hb he
  intro f J
  have hA : A.leafMeasure R μ s.val J = A.conditionalKernel μ s.val (f ⁻¹' B.time) := by
    have H := congrArg (fun ν : Measure ℝ => ν (f ⁻¹' B.time)) ha.2.2.1
    simpa only [Measure.restrict_apply (f.measurable B.time_open.measurableSet),inter_comm] using H
  have hB : B.leafMeasure S μ (rootTransitionSlice hij γ s).val (f '' J) =
      B.conditionalKernel μ (rootTransitionSlice hij γ s).val (f '' A.time) := by
    have H := congrArg (fun ν : Measure ℝ => ν (f '' A.time)) hb.2.2.1
    have hset : f '' J = f '' A.time ∩ B.time := by
      rw [show J = A.time ∩ f ⁻¹' B.time from rfl,image_inter_preimage]
    rw [hset]
    simpa only [Measure.restrict_apply (f.measurableEmbedding.measurableSet_image.mpr
      A.time_open.measurableSet)] using H
  rw [hA,hB]
  exact ⟨he.1,measure_ne_top _ _,he.2.1,measure_ne_top _ _⟩

 

theorem ae_basedLeaf_transition (A : RootBox hij k) (B : RootBox hij l)
    (R S : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0) (hBS : B.time ⊆ rootLeafWindow S 0)
    (γ : G n) (hγ : γ ∈ integralGroup n) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.transitionOverlapMeasure B γ μ).fst, ∀ t : ℝ,
      A.basedLeaf R μ (s.val,t) = B.basedLeaf S μ
        ((rootTransitionSlice hij γ s).val,t + rootTransitionTime γ s) := by
  filter_upwards [A.ae_leafTransition B R S hAR hBS γ hγ μ hfree,
    A.ae_leafTransition_anchor_mass B R S hAR hBS γ hγ μ hfree] with s hs hm
  intro t
  have H := congrArg (fun ν : Measure ℝ => basedRealMeasure ν (t + rootTransitionTime γ s)) hs
  rw [basedRealMeasure_translate] at H
  unfold anchorNormalize at H
  rw [basedRealMeasure_smul _ _ (ENNReal.inv_ne_zero.mpr hm.2.1) (ENNReal.inv_ne_top.mpr hm.1),
    basedRealMeasure_smul _ _ (ENNReal.inv_ne_zero.mpr hm.2.2.2)
      (ENNReal.inv_ne_top.mpr hm.2.2.1)] at H
  exact H

end RootBox
end PrimeDegreePackets

open scoped Matrix Topology Classical ENNReal
namespace PrimeDegreePackets
variable {n : ℕ} {i j k l : Fin n} (hij : i ≠ j)

lemma rootGroupParametrization_injective :
    Function.Injective (fun z : RootSlice i j k × ℝ => ((rootPivotHomeomorph hij).symm z).val) := by
  intro z w h
  exact (rootPivotHomeomorph hij).symm.injective (Subtype.ext h)

 

theorem exists_rootTransition_of_quotient_eq
    (z : RootSlice i j k × ℝ) (w : RootSlice i j l × ℝ)
    (he : rootQuotientParametrization hij z = rootQuotientParametrization hij w) :
    ∃ γ : integralGroup n, ∃ h : (γ.val * z.1.val).1 l i ≠ 0,
      baseSubtypeMap {s : RootSlice i j l | (γ.val⁻¹ * s.val).1 k i ≠ 0}
        (rootTransitionCoordinates hij γ.val (⟨z.1,h⟩,z.2)) = w := by
  let g := ((rootPivotHomeomorph hij).symm z).val
  let h := ((rootPivotHomeomorph hij).symm w).val
  let γ := h*g⁻¹
  have hγ : γ ∈ integralGroup n := by
    exact (QuotientGroup.rightRel_apply.mp (Quotient.exact he))
  have heq : γ*g = h := by simp [γ,mul_assoc]
  have hp : (γ*z.1.val).1 l i ≠ 0 := by
    have hc := congrArg (fun q : G n => q.1 l i) heq
    change (γ*(z.1.val*Matrix.SpecialLinearGroup.transvection hij z.2)).1 l i = h.1 l i at hc
    rw [←mul_assoc,root_mul_entry,ite_eq_right hij,add_zero] at hc
    rw [hc]
    exact ((rootPivotHomeomorph hij).symm w).prop
  refine ⟨⟨γ,hγ⟩,hp,?_⟩
  apply rootGroupParametrization_injective hij
  exact (rootTransition_reconstruct hij γ ⟨z.1,hp⟩ z.2).trans heq

end PrimeDegreePackets


namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k l : Fin n} {hij : i ≠ j}

lemma map_transitionOverlapMeasure (A : RootBox hij k) (B : RootBox hij l)
    (γ : G n) (μ : Measure (X n)) :
    (A.transitionOverlapMeasure B γ μ).map
      (baseSubtypeMap {s : RootSlice i j k | (γ * s.val).1 l i ≠ 0}) =
    (A.coordinateMeasure μ).restrict
      (baseSubtypeMap {s : RootSlice i j k | (γ * s.val).1 l i ≠ 0} ''
        ((rootTransitionCoordinates hij γ) ⁻¹' B.overlapDomain γ⁻¹ k)) := by
  let U := {s : RootSlice i j k | (γ * s.val).1 l i ≠ 0}
  let T := (rootTransitionCoordinates hij γ) ⁻¹' B.overlapDomain γ⁻¹ k
  have he := baseSubtypeMap_embedding (β := ℝ) U (rootSliceOverlap_isOpen γ).measurableSet
  change ((A.coordinateMeasure μ).comap (baseSubtypeMap U) |>.restrict T).map (baseSubtypeMap U) = _
  rw [he.restrict_comap,he.map_comap,baseSubtypeMap_range]
  change ((A.coordinateMeasure μ).restrict (baseSubtypeMap U '' T)).restrict (U ×ˢ univ) =
    (A.coordinateMeasure μ).restrict (baseSubtypeMap U '' T)
  rw [Measure.restrict_restrict (MeasurableSet.prod (rootSliceOverlap_isOpen γ).measurableSet MeasurableSet.univ)]
  congr 1
  apply inter_eq_right.mpr
  rw [←baseSubtypeMap_range (β := ℝ) U]
  exact image_subset_range _ _

lemma ae_basedLeaf_lift_transition (A : RootBox hij k) (B : RootBox hij l)
    (R S : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0) (hBS : B.time ⊆ rootLeafWindow S 0)
    (γ : G n) (hγ : γ ∈ integralGroup n) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ, ∀ hp : (γ*z.1.val).1 l i ≠ 0,
      (rootTransitionCoordinates hij γ (⟨z.1,hp⟩,z.2)) ∈ B.overlapDomain γ⁻¹ k →
      A.basedLeaf R μ z = B.basedLeaf S μ
        (baseSubtypeMap {s : RootSlice i j l | (γ⁻¹*s.val).1 k i ≠ 0}
          (rootTransitionCoordinates hij γ (⟨z.1,hp⟩,z.2))) := by
  let U := {s : RootSlice i j k | (γ*s.val).1 l i ≠ 0}
  let T := (rootTransitionCoordinates hij γ) ⁻¹' B.overlapDomain γ⁻¹ k
  let P := fun z : RootSlice i j k × ℝ => ∀ hp : (γ*z.1.val).1 l i ≠ 0,
    (rootTransitionCoordinates hij γ (⟨z.1,hp⟩,z.2)) ∈ B.overlapDomain γ⁻¹ k →
      A.basedLeaf R μ z = B.basedLeaf S μ
        (baseSubtypeMap {s : RootSlice i j l | (γ⁻¹*s.val).1 k i ≠ 0}
          (rootTransitionCoordinates hij γ (⟨z.1,hp⟩,z.2)))
  have H : ∀ᵐ z ∂A.transitionOverlapMeasure B γ μ, P (baseSubtypeMap U z) := by
    have H₀ := ae_of_ae_map measurable_fst.aemeasurable
      (A.ae_basedLeaf_transition B R S hAR hBS γ hγ μ hfree)
    filter_upwards [H₀] with z hz
    intro hp _
    exact hz z.2
  have he := baseSubtypeMap_embedding (β := ℝ) U (rootSliceOverlap_isOpen γ).measurableSet
  have H' := he.ae_map_iff.mpr H
  rw [map_transitionOverlapMeasure] at H'
  have hT : MeasurableSet T :=
    (rootTransitionCoordinates hij γ).measurable (B.overlapDomain_open γ⁻¹ k).measurableSet
  have H'' := (ae_restrict_iff' (he.measurableSet_image.mpr hT)).mp H'
  filter_upwards [H''] with z hz
  intro hp ht
  exact hz ⟨(⟨z.1,hp⟩,z.2),ht,rfl⟩ hp ht

 

theorem ae_basedLeaf_chart_compatibility (A : RootBox hij k) (B : RootBox hij l)
    (R S : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0) (hBS : B.time ⊆ rootLeafWindow S 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ, ∀ w ∈ B.domain,
      rootQuotientParametrization hij z = rootQuotientParametrization hij w →
      A.basedLeaf R μ z = B.basedLeaf S μ w := by
  let : Countable (Matrix.SpecialLinearGroup (Fin n) ℤ) := by
    unfold Matrix.SpecialLinearGroup Matrix
    infer_instance
  let : Countable (integralGroup n) :=
    (Set.countable_range (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) :
      Matrix.SpecialLinearGroup (Fin n) ℤ → G n)).to_subtype
  have H := ae_all_iff.mpr (fun γ : integralGroup n =>
    A.ae_basedLeaf_lift_transition B R S hAR hBS γ.val γ.prop μ hfree)
  filter_upwards [H] with z hz
  intro w hw he
  obtain ⟨γ,hp,heq⟩ := exists_rootTransition_of_quotient_eq hij z w he
  have ht : rootTransitionCoordinates hij γ.val (⟨z.1,hp⟩,z.2) ∈ B.overlapDomain γ.val⁻¹ k := by
    change baseSubtypeMap _ _ ∈ B.domain
    rwa [heq]
  exact (hz γ hp ht).trans (congrArg (B.basedLeaf S μ) heq)

end PrimeDegreePackets.RootBox


namespace PrimeDegreePackets
variable {n : ℕ} {i j : Fin n} (hij : i ≠ j)

structure BoundedRootBox where
  pivot : Fin n
  box : RootBox hij pivot
  radius : ℝ
  time_bound : box.time ⊆ rootLeafWindow radius 0

namespace RootBox
variable {hij} {k : Fin n}

 

def coordinates (A : RootBox hij k) (x : A.range) : A.domain :=
  A.embedding.toIsEmbedding.toHomeomorph.symm x

lemma param_coordinates (A : RootBox hij k) (x : A.range) :
    A.param (A.coordinates x) = x.val := by
  exact congrArg Subtype.val (A.embedding.toIsEmbedding.toHomeomorph.apply_symm_apply x)

lemma coordinates_param (A : RootBox hij k) (z : A.domain) :
    A.coordinates ⟨A.param z,mem_range_self z⟩ = z := by
  exact A.embedding.toIsEmbedding.toHomeomorph_symm_apply z

lemma aemeasurable_of_coordinate (A : RootBox hij k) (μ : Measure (X n))
    {β : Type*} [MeasurableSpace β] {f : X n → β}
    (hf : AEMeasurable (f ∘ rootQuotientParametrization hij) (A.coordinateMeasure μ)) :
    AEMeasurable f (μ.restrict A.range) := by
  have he : (μ.comap A.param).map A.param = μ.restrict A.range :=
    A.embedding.measurableEmbedding.map_comap μ
  rw [←he]
  apply A.embedding.measurableEmbedding.aemeasurable_map_iff.mpr
  exact hf.comp_measurable measurable_subtype_coe

lemma ae_of_coordinate (A : RootBox hij k) (μ : Measure (X n)) {P : X n → Prop}
    (hP : ∀ᵐ z ∂A.coordinateMeasure μ, P (rootQuotientParametrization hij z)) :
    ∀ᵐ x ∂μ.restrict A.range, P x := by
  have he : (μ.comap A.param).map A.param = μ.restrict A.range :=
    A.embedding.measurableEmbedding.map_comap μ
  rw [←he]
  apply A.embedding.measurableEmbedding.ae_map_iff.mpr
  exact ae_of_ae_map measurable_subtype_coe.aemeasurable hP

end RootBox

lemma exists_boundedRootBox_at (x : X n) : ∃ B : BoundedRootBox hij, x ∈ B.box.range := by
  obtain ⟨k,A,⟨z,hz⟩⟩ := exists_rootBox_at hij x
  let V := A.time ∩ Ioo (z.val.2-1) (z.val.2+1)
  let B := A.shrink A.transverse V A.transverse_open
    (A.time_open.inter isOpen_Ioo) Subset.rfl inter_subset_left
  have ht : B.time ⊆ rootLeafWindow (|z.val.2|+2) 0 := by
    intro t ht
    simp only [rootLeafWindow,Nat.cast_zero,add_zero,Set.mem_Ioo]
    have h₁ := le_abs_self z.val.2
    have h₂ := neg_abs_le z.val.2
    obtain ⟨_,hlo,hhi⟩ := ht
    constructor <;> linarith
  refine ⟨⟨k,B,|z.val.2|+2,ht⟩,?_⟩
  refine ⟨⟨z.val,⟨z.prop.1,z.prop.2,by dsimp; constructor <;> linarith⟩⟩,hz⟩

lemma exists_countable_boundedRootBox_cover :
    ∃ C : Set (BoundedRootBox hij), C.Countable ∧
      (univ : Set (X n)) ⊆ ⋃ B ∈ C, B.box.range := by
  apply isLindelof_univ.elim_countable_subcover (fun B : BoundedRootBox hij => B.box.range)
  · exact fun B => B.box.range_open
  · intro x _
    obtain ⟨B,hB⟩ := exists_boundedRootBox_at hij x
    exact mem_iUnion.mpr ⟨B,hB⟩

 

def boundedRootAtlas : Set (BoundedRootBox hij) :=
  (exists_countable_boundedRootBox_cover hij).choose

lemma boundedRootAtlas_countable : (boundedRootAtlas hij).Countable :=
  (exists_countable_boundedRootBox_cover hij).choose_spec.1

lemma boundedRootAtlas_covers (x : X n) : ∃ B : boundedRootAtlas hij, x ∈ B.val.box.range := by
  have H := (exists_countable_boundedRootBox_cover hij).choose_spec.2 (mem_univ x)
  obtain ⟨B,hx⟩ := mem_iUnion.mp H
  obtain ⟨hB,hx⟩ := mem_iUnion.mp hx
  exact ⟨⟨B,hB⟩,hx⟩

end PrimeDegreePackets
end
end

end OAI
