import Mathlib
import OAI.NumberTheory.PrimePackets.LeafAnchors

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
namespace PrimeDegreePackets
variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] [MeasurableSpace δ]

lemma fst_map_fibers_of_measurable (ρ : Measure (α × β))
    (e : α → γ) (he : Measurable e) (F : α × β → δ) (hF : Measurable F) :
    (ρ.map (fun z => (e z.1,F z))).fst = ρ.fst.map e := by
  have hfull : Measurable (fun z : α × β => (e z.1,F z)) := (he.comp measurable_fst).prodMk hF
  rw [Measure.fst,Measure.map_map measurable_fst hfull,
    Measure.fst,Measure.map_map he measurable_fst]
  rfl

lemma compProd_map_fibers_leftInverse (μ : Measure α) [SFinite μ] (κ : Kernel α β)
    [IsFiniteKernel κ] (e : α → γ) (he : Measurable e)
    (r : γ → α) (hr : Measurable r) (hre : Function.LeftInverse r e)
    (F : α × β → δ) (hF : Measurable F) :
    (μ ⊗ₘ κ).map (fun z => (e z.1,F z)) =
      μ.map e ⊗ₘ (mapFibers κ F hF).comap r hr := by
  have hfull : Measurable (fun z : α × β => (e z.1,F z)) := (he.comp measurable_fst).prodMk hF
  ext S hS
  rw [Measure.map_apply hfull hS,Measure.compProd_apply (hfull hS),Measure.compProd_apply hS,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hS) he]
  apply lintegral_congr
  intro a
  rw [Kernel.comap_apply,hre a,mapFibers_apply]
  exact (Measure.map_apply (hF.comp measurable_prodMk_left)
    (show MeasurableSet (Prod.mk (e a) ⁻¹' S) from measurable_prodMk_left hS)).symm

lemma conditional_map_fibers_leftInverse [StandardBorelSpace β] [Nonempty β]
    [StandardBorelSpace δ] [Nonempty δ] (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    (e : α → γ) (he : Measurable e) (r : γ → α) (hr : Measurable r)
    (hre : Function.LeftInverse r e) (F : α × β → δ) (hF : Measurable F) :
    ∀ᵐ a ∂ρ.fst, (ρ.map (fun z => (e z.1,F z))).condKernel (e a) =
      (ρ.condKernel a).map (fun b => F (a,b)) := by
  let κ := (mapFibers ρ.condKernel F hF).comap r hr
  have heq : ρ.map (fun z => (e z.1,F z)) = (ρ.map (fun z => (e z.1,F z))).fst ⊗ₘ κ := by
    rw [fst_map_fibers_of_measurable ρ e he F hF,
      ←compProd_map_fibers_leftInverse ρ.fst ρ.condKernel e he r hr hre F hF,
      Measure.disintegrate]
  have H := eq_condKernel_of_measure_eq_compProd κ heq
  rw [fst_map_fibers_of_measurable ρ e he F hF] at H
  have H' := ae_of_ae_map he.aemeasurable H
  filter_upwards [H'] with a ha
  simpa only [κ,Kernel.comap_apply,hre a,mapFibers_apply] using ha.symm

 

theorem conditional_map_fibers_embedding [StandardBorelSpace β] [Nonempty β]
    [StandardBorelSpace δ] [Nonempty δ] (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    (e : α → γ) (he : MeasurableEmbedding e) (F : α × β → δ) (hF : Measurable F) :
    ∀ᵐ a ∂ρ.fst, (ρ.map (fun z => (e z.1,F z))).condKernel (e a) =
      (ρ.condKernel a).map (fun b => F (a,b)) := by
  cases isEmpty_or_nonempty α with
  | inl h => exact ae_of_all _ (fun a => isEmptyElim a)
  | inr h =>
    exact conditional_map_fibers_leftInverse ρ e he.measurable he.invFun
      he.measurable_invFun he.leftInverse_invFun F hF

end PrimeDegreePackets


namespace PrimeDegreePackets
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

abbrev baseSubtypeMap (U : Set α) : U × β → α × β := fun z => (z.1.val,z.2)

lemma baseSubtypeMap_embedding (U : Set α) (hU : MeasurableSet U) :
    MeasurableEmbedding (baseSubtypeMap (β := β) U) :=
  (MeasurableEmbedding.subtype_coe hU).prodMap MeasurableEmbedding.id

omit [MeasurableSpace α] [MeasurableSpace β] in
lemma baseSubtypeMap_range (U : Set α) :
    Set.range (baseSubtypeMap (β := β) U) = U ×ˢ univ := by
  ext z
  simp only [Set.mem_range,Set.mem_prod,Set.mem_univ,and_true]
  constructor
  · rintro ⟨x,rfl⟩; exact x.1.prop
  · intro hz; exact ⟨(⟨z.1,hz⟩,z.2),Prod.ext rfl rfl⟩

lemma map_comap_baseSubtype (ρ : Measure (α × β)) (U : Set α) (hU : MeasurableSet U) :
    (ρ.comap (baseSubtypeMap U)).map (baseSubtypeMap U) = ρ.restrict (U ×ˢ univ) := by
  rw [(baseSubtypeMap_embedding U hU).map_comap,baseSubtypeMap_range]

lemma fst_map_comap_baseSubtype [StandardBorelSpace β] [Nonempty β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ] (U : Set α) (hU : MeasurableSet U) :
    ((ρ.comap (baseSubtypeMap U)).fst).map Subtype.val = ρ.fst.restrict U := by
  rw [←fst_map_fibers_of_measurable _ Subtype.val measurable_subtype_coe Prod.snd measurable_snd]
  change ((ρ.comap (baseSubtypeMap U)).map (baseSubtypeMap U)).fst = _
  rw [map_comap_baseSubtype ρ U hU,restricted_conditional_marginal ρ hU MeasurableSet.univ]
  simp only [measure_univ]
  exact MeasureTheory.withDensity_one

theorem conditional_comap_baseSubtype [StandardBorelSpace β] [Nonempty β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ] (U : Set α) (hU : MeasurableSet U) :
    ∀ᵐ a ∂(ρ.comap (baseSubtypeMap U)).fst,
      (ρ.comap (baseSubtypeMap U)).condKernel a = ρ.condKernel a.val := by
  have H₁ := conditional_map_fibers_embedding (ρ.comap (baseSubtypeMap U))
    Subtype.val (MeasurableEmbedding.subtype_coe hU) Prod.snd measurable_snd
  have he : (ρ.comap (baseSubtypeMap U)).map (fun z => (z.1.val,Prod.snd z)) =
      ρ.restrict (U ×ˢ univ) := map_comap_baseSubtype ρ U hU
  have H₂ : ∀ᵐ a ∂ρ.fst.restrict U,
      (ρ.restrict (U ×ˢ univ)).condKernel a = ρ.condKernel a := by
    filter_upwards [restricted_conditional_kernel ρ hU MeasurableSet.univ] with a ha
    simpa only [measure_univ,one_smul,Measure.restrict_univ] using ha
  rw [←fst_map_comap_baseSubtype ρ U hU] at H₂
  have H₂' := ae_of_ae_map measurable_subtype_coe.aemeasurable H₂
  filter_upwards [H₁,H₂'] with a ha hb
  simp only [he] at ha
  exact (Measure.map_id (μ := (ρ.comap (baseSubtypeMap U)).condKernel a)).symm.trans
    (ha.symm.trans hb)

end PrimeDegreePackets


namespace PrimeDegreePackets
variable {n : ℕ} {i j k l : Fin n} {hij : i ≠ j}

lemma rootSliceOverlap_isOpen (γ : G n) :
    IsOpen {s : RootSlice i j k | (γ * s.val).1 l i ≠ 0} := by
  apply isOpen_ne_fun _ continuous_const
  have hc : Continuous (fun s : RootSlice i j k =>
      ((γ * s.val) : Matrix (Fin n) (Fin n) ℝ)) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous.comp
      (show Continuous (fun s : RootSlice i j k => γ * s.val) from
        continuous_const.mul continuous_subtype_val)
  exact (continuous_apply i).comp ((continuous_apply l).comp hc)

abbrev rootOverlapParam (hij : i ≠ j) (γ : G n) : RootSliceOverlap i j k l γ × ℝ → X n :=
  fun z => rootQuotientParametrization hij (z.1.val,z.2)

namespace RootBox

abbrev overlapDomain (A : RootBox hij k) (γ : G n) (l : Fin n) :
    Set (RootSliceOverlap i j k l γ × ℝ) :=
  baseSubtypeMap {s : RootSlice i j k | (γ * s.val).1 l i ≠ 0} ⁻¹' A.domain

def overlapMeasure (A : RootBox hij k) (γ : G n) (l : Fin n) (μ : Measure (X n)) :
    Measure (RootSliceOverlap i j k l γ × ℝ) :=
  (A.coordinateMeasure μ).comap (baseSubtypeMap {s : RootSlice i j k | (γ * s.val).1 l i ≠ 0})

instance overlapMeasure_finite (A : RootBox hij k) (γ : G n) (l : Fin n)
    (μ : Measure (X n)) [IsFiniteMeasure μ] : IsFiniteMeasure (A.overlapMeasure γ l μ) := by
  unfold overlapMeasure
  infer_instance

lemma overlapDomain_open (A : RootBox hij k) (γ : G n) (l : Fin n) :
    IsOpen (A.overlapDomain γ l) :=
  (A.transverse_open.prod A.time_open).preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

lemma overlapMeasure_apply (A : RootBox hij k) (γ : G n) (l : Fin n)
    (μ : Measure (X n)) {S : Set (RootSliceOverlap i j k l γ × ℝ)} (hS : MeasurableSet S) :
    A.overlapMeasure γ l μ S =
      μ (rootOverlapParam hij γ '' (S ∩ A.overlapDomain γ l)) := by
  let U := {s : RootSlice i j k | (γ * s.val).1 l i ≠ 0}
  have he := baseSubtypeMap_embedding (β := ℝ) U (rootSliceOverlap_isOpen γ).measurableSet
  rw [overlapMeasure,he.comap_apply,A.coordinateMeasure_apply μ (he.measurableSet_image.mpr hS)]
  congr 1
  ext x
  constructor
  · rintro ⟨z,⟨⟨w,hw,rfl⟩,hd⟩,rfl⟩
    exact ⟨w,⟨hw,hd⟩,rfl⟩
  · rintro ⟨w,⟨hw,hd⟩,rfl⟩
    exact ⟨baseSubtypeMap U w,⟨⟨w,hw,rfl⟩,hd⟩,rfl⟩

lemma overlapMeasure_conditional (A : RootBox hij k) (γ : G n) (l : Fin n)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(A.overlapMeasure γ l μ).fst,
      (A.overlapMeasure γ l μ).condKernel s = A.conditionalKernel μ s.val :=
  conditional_comap_baseSubtype (A.coordinateMeasure μ) _ (rootSliceOverlap_isOpen γ).measurableSet

 

theorem overlapMeasure_transition (A : RootBox hij k) (B : RootBox hij l)
    (γ : G n) (hγ : γ ∈ integralGroup n) (μ : Measure (X n)) :
    ((A.overlapMeasure γ l μ).restrict
      ((rootTransitionCoordinates hij γ) ⁻¹' B.overlapDomain γ⁻¹ k)).map
        (rootTransitionCoordinates hij γ) =
      (B.overlapMeasure γ⁻¹ k μ).restrict
        (rootTransitionCoordinates hij γ '' A.overlapDomain γ l) := by
  let E := rootTransitionCoordinates (k := k) (l := l) hij γ
  ext S hS
  rw [Measure.map_apply E.measurable hS,Measure.restrict_apply (E.measurable hS),
    A.overlapMeasure_apply γ l μ ((E.measurable hS).inter
      (E.measurable (B.overlapDomain_open γ⁻¹ k).measurableSet)),
    Measure.restrict_apply hS,B.overlapMeasure_apply γ⁻¹ k μ
      (hS.inter (E.measurableEmbedding.measurableSet_image.mpr
        (A.overlapDomain_open γ l).measurableSet))]
  congr 1
  ext x
  constructor
  · rintro ⟨z,⟨⟨hzS,hzB⟩,hzA⟩,rfl⟩
    exact ⟨E z,⟨⟨hzS,⟨z,hzA,rfl⟩⟩,hzB⟩,rootTransitionCoordinates_param hij γ hγ z⟩
  · rintro ⟨w,⟨⟨hwS,z,hzA,rfl⟩,hzB⟩,rfl⟩
    exact ⟨z,⟨⟨hwS,hzB⟩,hzA⟩,(rootTransitionCoordinates_param hij γ hγ z).symm⟩

end RootBox
end PrimeDegreePackets


namespace PrimeDegreePackets
variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] [MeasurableSpace δ]

lemma conditional_restrict_normalized [StandardBorelSpace β] [Nonempty β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ] (T : Set (α × β)) (hT : MeasurableSet T) :
    ∀ᵐ a ∂(ρ.restrict T).fst,
      ρ.condKernel a (Prod.mk a ⁻¹' T) ≠ 0 ∧
      (ρ.restrict T).condKernel a =
        (anchorNormalize (ρ.condKernel a) (Prod.mk a ⁻¹' T)).restrict (Prod.mk a ⁻¹' T) := by
  let w := fun a => ρ.condKernel a (Prod.mk a ⁻¹' T)
  have hw : Measurable w := Kernel.measurable_kernel_prodMk_left hT
  have hp : ∀ᵐ a ∂(ρ.restrict T).fst, w a ≠ 0 := by
    rw [conditional_restrict_marginal ρ T hT]
    exact (ae_withDensity_iff hw).mpr (ae_of_all _ fun _ h => h)
  have H : ∀ᵐ a ∂(ρ.restrict T).fst,
      w a • (ρ.restrict T).condKernel a = (ρ.condKernel a).restrict (Prod.mk a ⁻¹' T) := by
    rw [conditional_restrict_marginal ρ T hT]
    exact (withDensity_absolutelyContinuous ρ.fst w).ae_le (conditional_restrict_fibers ρ T hT)
  filter_upwards [hp,H] with a hpa ha
  refine ⟨hpa,?_⟩
  have he := congrArg (fun ν : Measure β => (w a)⁻¹ • ν) ha
  rw [smul_smul,ENNReal.inv_mul_cancel hpa (measure_ne_top _ _),one_smul] at he
  simpa only [anchorNormalize,Measure.restrict_smul] using he

 

theorem conditional_overlap_normalized [StandardBorelSpace β] [Nonempty β]
    [StandardBorelSpace δ] [Nonempty δ]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    (σ : Measure (γ × δ)) [IsFiniteMeasure σ]
    (T : Set (α × β)) (hT : MeasurableSet T)
    (W : Set (γ × δ)) (hW : MeasurableSet W)
    (e : α ≃ᵐ γ) (F : α × β → δ) (hF : Measurable F)
    (he : (ρ.restrict T).map (fun z => (e z.1,F z)) = σ.restrict W) :
    ∀ᵐ a ∂(ρ.restrict T).fst,
      ρ.condKernel a (Prod.mk a ⁻¹' T) ≠ 0 ∧
      σ.condKernel (e a) (Prod.mk (e a) ⁻¹' W) ≠ 0 ∧
      ((anchorNormalize (ρ.condKernel a) (Prod.mk a ⁻¹' T)).restrict (Prod.mk a ⁻¹' T)).map
        (fun b => F (a,b)) =
      (anchorNormalize (σ.condKernel (e a)) (Prod.mk (e a) ⁻¹' W)).restrict (Prod.mk (e a) ⁻¹' W) := by
  have Hρ := conditional_restrict_normalized ρ T hT
  have Hσ := conditional_restrict_normalized σ W hW
  have hm := congrArg Measure.fst he
  rw [fst_map_fibers _ e F hF] at hm
  rw [←hm] at Hσ
  have Hσ' := ae_of_ae_map e.measurable.aemeasurable Hσ
  have Hcov := conditional_map_fibers (ρ.restrict T) e F hF
  filter_upwards [Hρ,Hσ',Hcov] with a ha hb hc
  simp only [he] at hc
  refine ⟨ha.1,hb.1,?_⟩
  rw [←ha.2,←hb.2]
  exact hc.symm

end PrimeDegreePackets


namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k l : Fin n} {hij : i ≠ j}

theorem overlap_conditional_projective (A : RootBox hij k) (B : RootBox hij l)
    (γ : G n) (hγ : γ ∈ integralGroup n) (μ : Measure (X n)) [IsFiniteMeasure μ] :
    let E := rootTransitionCoordinates (k := k) (l := l) hij γ
    let T := E ⁻¹' B.overlapDomain γ⁻¹ k
    let W := E '' A.overlapDomain γ l
    ∀ᵐ s ∂((A.overlapMeasure γ l μ).restrict T).fst,
      A.conditionalKernel μ s.val (Prod.mk s ⁻¹' T) ≠ 0 ∧
      B.conditionalKernel μ (rootTransitionSlice hij γ s).val
        (Prod.mk (rootTransitionSlice hij γ s) ⁻¹' W) ≠ 0 ∧
      ((anchorNormalize (A.conditionalKernel μ s.val) (Prod.mk s ⁻¹' T)).restrict
        (Prod.mk s ⁻¹' T)).map (Homeomorph.addRight (rootTransitionTime γ s)) =
      (anchorNormalize (B.conditionalKernel μ (rootTransitionSlice hij γ s).val)
        (Prod.mk (rootTransitionSlice hij γ s) ⁻¹' W)).restrict
        (Prod.mk (rootTransitionSlice hij γ s) ⁻¹' W) := by
  intro E T W
  let e := (rootSliceTransition (k := k) (l := l) hij γ).toMeasurableEquiv
  let F : RootSliceOverlap i j k l γ × ℝ → ℝ := fun z => z.2 + rootTransitionTime γ z.1
  have hF : Measurable F := measurable_snd.add
    ((continuous_rootTransitionTime γ).measurable.comp measurable_fst)
  have H := conditional_overlap_normalized (A.overlapMeasure γ l μ) (B.overlapMeasure γ⁻¹ k μ)
    T (E.measurable (B.overlapDomain_open γ⁻¹ k).measurableSet)
    W (E.measurableEmbedding.measurableSet_image.mpr (A.overlapDomain_open γ l).measurableSet)
    e F hF (A.overlapMeasure_transition B γ hγ μ)
  have HA : ∀ᵐ s ∂((A.overlapMeasure γ l μ).restrict T).fst,
      (A.overlapMeasure γ l μ).condKernel s = A.conditionalKernel μ s.val :=
    (Measure.absolutelyContinuous_of_le (Measure.fst_mono Measure.restrict_le_self)).ae_le
      (A.overlapMeasure_conditional γ l μ)
  have HB : ∀ᵐ t ∂((B.overlapMeasure γ⁻¹ k μ).restrict W).fst,
      (B.overlapMeasure γ⁻¹ k μ).condKernel t = B.conditionalKernel μ t.val :=
    (Measure.absolutelyContinuous_of_le (Measure.fst_mono Measure.restrict_le_self)).ae_le
      (B.overlapMeasure_conditional γ⁻¹ k μ)
  have hm := congrArg Measure.fst (A.overlapMeasure_transition B γ hγ μ)
  change (((A.overlapMeasure γ l μ).restrict T).map (fun z => (e z.1,F z))).fst = _ at hm
  rw [fst_map_fibers _ e F hF] at hm
  rw [←hm] at HB
  have HB' := ae_of_ae_map e.measurable.aemeasurable HB
  filter_upwards [H,HA,HB'] with s hs ha hb
  rw [ha,hb] at hs
  exact hs

end PrimeDegreePackets.RootBox


namespace PrimeDegreePackets

lemma fst_restrict_base {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ρ : Measure (α × β)) {U : Set α} (hU : MeasurableSet U) :
    (ρ.restrict (Prod.fst ⁻¹' U)).fst = ρ.fst.restrict U := by
  exact (Measure.restrict_map measurable_fst hU).symm

namespace RootBox
variable {n : ℕ} {i j k l : Fin n} {hij : i ≠ j}

abbrev transitionOverlapMeasure (A : RootBox hij k) (B : RootBox hij l)
    (γ : G n) (μ : Measure (X n)) : Measure (RootSliceOverlap i j k l γ × ℝ) :=
  (A.overlapMeasure γ l μ).restrict
    ((rootTransitionCoordinates hij γ) ⁻¹' B.overlapDomain γ⁻¹ k)

lemma transitionOverlapMeasure_apply (A : RootBox hij k) (B : RootBox hij l)
    (γ : G n) (μ : Measure (X n)) {S : Set (RootSliceOverlap i j k l γ × ℝ)}
    (hS : MeasurableSet S) :
    A.transitionOverlapMeasure B γ μ S = μ (rootOverlapParam hij γ ''
      ((S ∩ (rootTransitionCoordinates hij γ) ⁻¹' B.overlapDomain γ⁻¹ k) ∩ A.overlapDomain γ l)) := by
  rw [transitionOverlapMeasure,Measure.restrict_apply hS,A.overlapMeasure_apply γ l μ
    (hS.inter ((rootTransitionCoordinates hij γ).measurable (B.overlapDomain_open γ⁻¹ k).measurableSet))]

 

lemma transitionOverlapMeasure_restrict_le (A D : RootBox hij k) (B F : RootBox hij l)
    (hAD : A.time ⊆ D.time) (hBF : B.time ⊆ F.time)
    (γ : G n) (μ : Measure (X n)) :
    (A.transitionOverlapMeasure B γ μ).restrict (Prod.fst ⁻¹'
      {s | s.val ∈ D.transverse ∧ (rootTransitionSlice hij γ s).val ∈ F.transverse}) ≤
      D.transitionOverlapMeasure F γ μ := by
  let U := {s : RootSliceOverlap i j k l γ |
    s.val ∈ D.transverse ∧ (rootTransitionSlice hij γ s).val ∈ F.transverse}
  have hU : MeasurableSet U :=
    (measurable_subtype_coe D.transverse_open.measurableSet).inter
      ((continuous_rootTransitionSlice hij γ).measurable
        (measurable_subtype_coe F.transverse_open.measurableSet))
  apply Measure.le_iff.mpr
  intro S hS
  have hSU : MeasurableSet (S ∩ Prod.fst ⁻¹' U) := hS.inter (measurable_fst hU)
  rw [Measure.restrict_apply hS,transitionOverlapMeasure_apply _ _ _ _ hSU,
    transitionOverlapMeasure_apply _ _ _ _ hS]
  apply measure_mono
  apply Set.image_mono
  rintro z ⟨⟨⟨hzS,hzD,hzF⟩,hzB⟩,hzA⟩
  exact ⟨⟨hzS,⟨hzF,hBF hzB.2⟩⟩,⟨hzD,hAD hzA.2⟩⟩

lemma transition_base_ae_of_ae (A D : RootBox hij k) (B F : RootBox hij l)
    (hAD : A.time ⊆ D.time) (hBF : B.time ⊆ F.time)
    (γ : G n) (μ : Measure (X n)) {P : RootSliceOverlap i j k l γ → Prop}
    (hP : ∀ᵐ s ∂(D.transitionOverlapMeasure F γ μ).fst, P s) :
    ∀ᵐ s ∂(A.transitionOverlapMeasure B γ μ).fst,
      s.val ∈ D.transverse → (rootTransitionSlice hij γ s).val ∈ F.transverse → P s := by
  let U := {s : RootSliceOverlap i j k l γ |
    s.val ∈ D.transverse ∧ (rootTransitionSlice hij γ s).val ∈ F.transverse}
  have hU : MeasurableSet U :=
    (measurable_subtype_coe D.transverse_open.measurableSet).inter
      ((continuous_rootTransitionSlice hij γ).measurable
        (measurable_subtype_coe F.transverse_open.measurableSet))
  have H := (Measure.absolutelyContinuous_of_le
    (Measure.fst_mono (A.transitionOverlapMeasure_restrict_le D B F hAD hBF γ μ))).ae_le hP
  rw [fst_restrict_base _ hU] at H
  filter_upwards [(ae_restrict_iff' hU).mp H] with s hs
  exact fun hD hF => hs ⟨hD,hF⟩

lemma transition_base_ae_source (A : RootBox hij k) (B : RootBox hij l)
    (γ : G n) (μ : Measure (X n)) [IsFiniteMeasure μ]
    {P : RootSlice i j k → Prop} (hP : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, P s) :
    ∀ᵐ s ∂(A.transitionOverlapMeasure B γ μ).fst, P s.val := by
  let U := {s : RootSlice i j k | (γ*s.val).1 l i ≠ 0}
  have H := (Measure.absolutelyContinuous_of_le (Measure.restrict_le_self (s := U))).ae_le hP
  rw [←fst_map_comap_baseSubtype (A.coordinateMeasure μ) U
    (rootSliceOverlap_isOpen γ).measurableSet] at H
  exact (Measure.absolutelyContinuous_of_le (Measure.fst_mono Measure.restrict_le_self)).ae_le
    (ae_of_ae_map measurable_subtype_coe.aemeasurable H)

lemma transition_base_ae_target (A : RootBox hij k) (B : RootBox hij l)
    (γ : G n) (hγ : γ ∈ integralGroup n) (μ : Measure (X n)) [IsFiniteMeasure μ]
    {P : RootSlice i j l → Prop} (hP : ∀ᵐ s ∂(B.coordinateMeasure μ).fst, P s) :
    ∀ᵐ s ∂(A.transitionOverlapMeasure B γ μ).fst, P (rootTransitionSlice hij γ s).val := by
  let U := {s : RootSlice i j l | (γ⁻¹*s.val).1 k i ≠ 0}
  have H := (Measure.absolutelyContinuous_of_le (Measure.restrict_le_self (s := U))).ae_le hP
  rw [←fst_map_comap_baseSubtype (B.coordinateMeasure μ) U
    (rootSliceOverlap_isOpen γ⁻¹).measurableSet] at H
  have H' := ae_of_ae_map measurable_subtype_coe.aemeasurable H
  have H'' := (Measure.absolutelyContinuous_of_le (Measure.fst_mono
    (Measure.restrict_le_self (s := rootTransitionCoordinates hij γ '' A.overlapDomain γ l)))).ae_le H'
  change ∀ᵐ s ∂((B.overlapMeasure γ⁻¹ k μ).restrict
    (rootTransitionCoordinates hij γ '' A.overlapDomain γ l)).fst, P s.val at H''
  rw [←A.overlapMeasure_transition B γ hγ μ] at H''
  have hm := fst_map_fibers (A.transitionOverlapMeasure B γ μ)
    (rootSliceTransition hij γ).toMeasurableEquiv
    (fun z => z.2 + rootTransitionTime γ z.1)
    (measurable_snd.add ((continuous_rootTransitionTime γ).measurable.comp measurable_fst))
  change ((A.transitionOverlapMeasure B γ μ).map (rootTransitionCoordinates hij γ)).fst = _ at hm
  rw [hm] at H''
  exact ae_of_ae_map (rootSliceTransition hij γ).measurable.aemeasurable H''

end RootBox
end PrimeDegreePackets


namespace PrimeDegreePackets
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma anchorNormalize_map (ν : Measure α) (e : α ≃ᵐ β) {J : Set α}
    (hJ : MeasurableSet J) :
    (anchorNormalize ν J).map e = anchorNormalize (ν.map e) (e '' J) := by
  unfold anchorNormalize
  rw [Measure.map_smul _ e.measurable.aemeasurable,Measure.map_apply e.measurable
    (e.measurableEmbedding.measurableSet_image.mpr hJ),e.preimage_image]

lemma anchorNormalize_congr_restriction (ν p : Measure α) {D J : Set α}
    (hJ : MeasurableSet J) (hJD : J ⊆ D)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcT : c ≠ ∞)
    (he : ν.restrict D = c • p) :
    (anchorNormalize ν J).restrict D = anchorNormalize p J := by
  rw [←anchorNormalize_restrict_comm ν hJ hJD,he,anchorNormalize_smul _ _ _ hc0 hcT]

lemma anchorNormalize_reanchor_map (p : Measure α) (q : Measure β)
    (e : α ≃ᵐ β) {V : Set α} {W : Set β} {J : Set α}
    (hJ : MeasurableSet J) (hJV : J ⊆ V) (hJW : e '' J ⊆ W)
    (hpV0 : p V ≠ 0) (hpVT : p V ≠ ∞) (hqW0 : q W ≠ 0) (hqWT : q W ≠ ∞)
    (he : ((anchorNormalize p V).restrict V).map e = (anchorNormalize q W).restrict W) :
    ((anchorNormalize p J).restrict V).map e = (anchorNormalize q (e '' J)).restrict W := by
  have H := congrArg (fun ρ : Measure β => anchorNormalize ρ (e '' J)) he
  rw [←anchorNormalize_map _ e hJ,anchorNormalize_restrict_comm _ hJ hJV,
    anchorNormalize_twice _ _ _ hpV0 hpVT,
    anchorNormalize_restrict_comm _ (e.measurableEmbedding.measurableSet_image.mpr hJ) hJW,
    anchorNormalize_twice _ _ _ hqW0 hqWT] at H
  exact H

 

theorem projective_extensions_overlap
    (ν p : Measure α) (η q : Measure β) (e : α ≃ᵐ β)
    {D V J : Set α} {E W : Set β}
    (hD : MeasurableSet D) (hE : MeasurableSet E)
    (hJ : MeasurableSet J) (hJD : J ⊆ D) (hJV : J ⊆ V)
    (hJE : e '' J ⊆ E) (hJW : e '' J ⊆ W)
    (c d : ℝ≥0∞) (hc0 : c ≠ 0) (hcT : c ≠ ∞) (hd0 : d ≠ 0) (hdT : d ≠ ∞)
    (hν : ν.restrict D = c • p) (hη : η.restrict E = d • q)
    (hpV0 : p V ≠ 0) (hpVT : p V ≠ ∞) (hqW0 : q W ≠ 0) (hqWT : q W ≠ ∞)
    (he : ((anchorNormalize p V).restrict V).map e = (anchorNormalize q W).restrict W) :
    ((anchorNormalize ν J).restrict (V ∩ D)).map e =
      (anchorNormalize η (e '' J)).restrict (W ∩ E) := by
  have Hν := anchorNormalize_congr_restriction ν p hJ hJD c hc0 hcT hν
  have Hη := anchorNormalize_congr_restriction η q
    (e.measurableEmbedding.measurableSet_image.mpr hJ) hJE d hd0 hdT hη
  have H := anchorNormalize_reanchor_map p q e hJ hJV hJW hpV0 hpVT hqW0 hqWT he
  rw [←Hν,←Hη] at H
  simpa only [Measure.restrict_restrict' hD,Measure.restrict_restrict' hE] using H

end PrimeDegreePackets
end
end

end OAI
