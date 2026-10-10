import Mathlib
import OAI.NumberTheory.PrimePackets.RootRelations

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
namespace PrimeDegreePackets

instance rootGroupMeasurableSpace (n : ℕ) : MeasurableSpace (G n) := borel (G n)
instance rootGroupBorelSpace (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩

lemma rootPivot_isOpen {n : ℕ} (i k : Fin n) :
    IsOpen {g : G n | g.1 k i ≠ 0} := by
  have hc : Continuous (fun g : G n => g.1 k i) :=
    (continuous_apply i).comp ((continuous_apply k).comp
      Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous)
  exact isOpen_ne_fun hc continuous_const

lemma exists_rootPivot {n : ℕ} (i : Fin n) (g : G n) :
    ∃ k : Fin n, g.1 k i ≠ 0 := by
  by_contra h
  push Not at h
  have H := Matrix.det_eq_zero_of_column_eq_zero i h
  rw [g.prop] at H
  exact one_ne_zero H

def rootCoordinateMeasure {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (μ : Measure (RootPivot i k)) : Measure (RootSlice i j k × ℝ) :=
  Measure.map (rootPivotHomeomorph hij) μ

instance rootCoordinateMeasure_isFinite {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (μ : Measure (RootPivot i k)) [IsFiniteMeasure μ] :
    IsFiniteMeasure (rootCoordinateMeasure hij μ) := by
  unfold rootCoordinateMeasure
  infer_instance

 

def rootConditionalKernel {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (μ : Measure (RootPivot i k)) [IsFiniteMeasure μ] : Kernel (RootSlice i j k) ℝ :=
  (rootCoordinateMeasure hij μ).condKernel

instance rootConditionalKernel_isMarkov {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (μ : Measure (RootPivot i k)) [IsFiniteMeasure μ] :
    IsMarkovKernel (rootConditionalKernel hij μ) := by
  unfold rootConditionalKernel
  infer_instance

 
theorem rootConditionalKernel_disintegrate {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (μ : Measure (RootPivot i k)) [IsFiniteMeasure μ] :
    Measure.map (rootPivotHomeomorph hij).symm
      ((rootCoordinateMeasure hij μ).fst ⊗ₘ rootConditionalKernel hij μ) = μ := by
  rw [rootConditionalKernel,Measure.disintegrate]
  rw [rootCoordinateMeasure,Measure.map_map (rootPivotHomeomorph hij).symm.continuous.measurable
    (rootPivotHomeomorph hij).continuous.measurable]
  simpa only [Homeomorph.symm_comp_self] using Measure.map_id (μ := μ)

 
def rootQuotientParametrization {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (z : RootSlice i j k × ℝ) : X n :=
  Quotient.mk _ ((rootPivotHomeomorph hij).symm z).val

lemma rootQuotientParametrization_localHomeomorph {n : ℕ} {i j k : Fin n} (hij : i ≠ j) :
    IsLocalHomeomorph (rootQuotientParametrization (k := k) hij) := by
  have H := ((quotient_covering n).isLocalHomeomorph.comp
    (rootPivot_isOpen i k).isOpenEmbedding_subtypeVal.isLocalHomeomorph).comp
    (rootPivotHomeomorph (k := k) hij).symm.isLocalHomeomorph
  exact H

 

theorem rootQuotientParametrization_localEmbedding {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (z : RootSlice i j k × ℝ) :
    ∃ U ∈ 𝓝 z, Topology.IsOpenEmbedding (U.domRestrict (rootQuotientParametrization hij)) :=
  isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp
    (rootQuotientParametrization_localHomeomorph hij) z

lemma rootQuotientParametrization_add {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (s : RootSlice i j k) (a t : ℝ) :
    rootQuotientParametrization hij (s,a+t) =
      rightAction (rootQuotientParametrization hij (s,a))
        (Matrix.SpecialLinearGroup.transvection hij t) := by
  change Quotient.mk _ (s.val * Matrix.SpecialLinearGroup.transvection hij (a+t)) =
    Quotient.mk _ ((s.val * Matrix.SpecialLinearGroup.transvection hij a) *
      Matrix.SpecialLinearGroup.transvection hij t)
  rw [Matrix.SpecialLinearGroup.transvection_add,mul_assoc]

end PrimeDegreePackets


namespace PrimeDegreePackets

structure RootBox {n : ℕ} {i j : Fin n} (hij : i ≠ j) (k : Fin n) where
  transverse : Set (RootSlice i j k)
  time : Set ℝ
  transverse_open : IsOpen transverse
  time_open : IsOpen time
  embedding : Topology.IsOpenEmbedding
    ((transverse ×ˢ time).domRestrict (rootQuotientParametrization hij))

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

abbrev domain (B : RootBox hij k) := B.transverse ×ˢ B.time
abbrev param (B : RootBox hij k) := B.domain.domRestrict (rootQuotientParametrization hij)
def range (B : RootBox hij k) := Set.range B.param

lemma range_open (B : RootBox hij k) : IsOpen B.range := B.embedding.isOpen_range

 

def coordinateMeasure (B : RootBox hij k) (μ : Measure (X n)) :
    Measure (RootSlice i j k × ℝ) :=
  Measure.map Subtype.val (Measure.comap B.param μ)

instance coordinateMeasure_finite (B : RootBox hij k) (μ : Measure (X n))
    [IsFiniteMeasure μ] : IsFiniteMeasure (B.coordinateMeasure μ) := by
  have he := B.embedding.measurableEmbedding
  have : IsFiniteMeasure (Measure.comap B.param μ) := ⟨by
    rw [he.comap_apply]
    exact lt_of_le_of_lt (measure_mono (subset_univ _)) (measure_lt_top μ univ)⟩
  unfold coordinateMeasure
  infer_instance

lemma map_coordinateMeasure (B : RootBox hij k) (μ : Measure (X n)) :
    Measure.map (rootQuotientParametrization hij) (B.coordinateMeasure μ) =
      μ.restrict B.range := by
  rw [coordinateMeasure,Measure.map_map]
  · exact B.embedding.measurableEmbedding.map_comap μ
  · exact (rootQuotientParametrization_localHomeomorph hij).continuous.measurable
  · exact measurable_subtype_coe

def conditionalKernel (B : RootBox hij k) (μ : Measure (X n)) [IsFiniteMeasure μ] :
    Kernel (RootSlice i j k) ℝ := (B.coordinateMeasure μ).condKernel

instance conditionalKernel_markov (B : RootBox hij k) (μ : Measure (X n))
    [IsFiniteMeasure μ] : IsMarkovKernel (B.conditionalKernel μ) := by
  unfold conditionalKernel
  infer_instance

 

theorem disintegrate (B : RootBox hij k) (μ : Measure (X n)) [IsFiniteMeasure μ] :
    Measure.map (rootQuotientParametrization hij)
      ((B.coordinateMeasure μ).fst ⊗ₘ B.conditionalKernel μ) = μ.restrict B.range := by
  rw [conditionalKernel,Measure.disintegrate]
  exact B.map_coordinateMeasure μ

end RootBox

theorem exists_rootBox_at_coordinates {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (z : RootSlice i j k × ℝ) : ∃ B : RootBox hij k, z ∈ B.domain := by
  obtain ⟨U,hUz,hU⟩ := rootQuotientParametrization_localEmbedding hij z
  obtain ⟨V,W,hVo,hVz,hWo,hWz,hsub⟩ := mem_nhds_prod_iff'.mp hUz
  have he := hU.comp (Topology.IsOpenEmbedding.inclusion hsub
    ((hVo.prod hWo).preimage continuous_subtype_val))
  exact ⟨⟨V,W,hVo,hWo,he⟩,hVz,hWz⟩

 

theorem exists_rootBox_at {n : ℕ} {i j : Fin n} (hij : i ≠ j) (x : X n) :
    ∃ k : Fin n, ∃ B : RootBox hij k, x ∈ B.range := by
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨k,hk⟩ := exists_rootPivot i g
    let g' : RootPivot i k := ⟨g,hk⟩
    let z := rootPivotHomeomorph hij g'
    obtain ⟨B,hB⟩ := exists_rootBox_at_coordinates hij z
    refine ⟨k,B,⟨⟨z,hB⟩,?_⟩⟩
    change Quotient.mk _ ((rootPivotHomeomorph hij).symm ((rootPivotHomeomorph hij) g')).val = _
    rw [Homeomorph.symm_apply_apply]

 

theorem exists_countable_rootBox_cover {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ∃ C : Set (Σ k : Fin n, RootBox hij k), C.Countable ∧
      (univ : Set (X n)) ⊆ ⋃ B ∈ C, B.2.range := by
  apply isLindelof_univ.elim_countable_subcover (fun B : Σ k : Fin n, RootBox hij k => B.2.range)
  · exact fun B => B.2.range_open
  · intro x _
    obtain ⟨k,B,hB⟩ := exists_rootBox_at hij x
    exact mem_iUnion.mpr ⟨⟨k,B⟩,hB⟩

end PrimeDegreePackets


namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

lemma coordinateMeasure_ae_domain (B : RootBox hij k) (μ : Measure (X n)) :
    ∀ᵐ z ∂B.coordinateMeasure μ, z ∈ B.domain := by
  rw [coordinateMeasure]
  exact (ae_map_iff measurable_subtype_coe.aemeasurable
    (B.transverse_open.prod B.time_open).measurableSet).mpr
      (ae_of_all _ fun z => z.prop)

lemma coordinateMeasure_fst_ae_transverse (B : RootBox hij k) (μ : Measure (X n)) :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst, s ∈ B.transverse := by
  rw [Measure.fst]
  apply (ae_map_iff measurable_fst.aemeasurable B.transverse_open.measurableSet).mpr
  filter_upwards [B.coordinateMeasure_ae_domain μ] with z hz
  exact hz.1

 

lemma conditionalKernel_ae_time (B : RootBox hij k) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst, ∀ᵐ t ∂B.conditionalKernel μ s, t ∈ B.time := by
  have H : ∀ᵐ z ∂((B.coordinateMeasure μ).fst ⊗ₘ B.conditionalKernel μ), z.2 ∈ B.time := by
    rw [conditionalKernel,Measure.disintegrate]
    filter_upwards [B.coordinateMeasure_ae_domain μ] with z hz
    exact hz.2
  exact Measure.ae_ae_of_ae_compProd H

lemma conditionalKernel_time_mass (B : RootBox hij k) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst, B.conditionalKernel μ s B.time = 1 := by
  filter_upwards [B.conditionalKernel_ae_time μ] with s hs
  rw [← measure_univ (μ := B.conditionalKernel μ s)]
  exact measure_congr (ae_eq_univ.mpr hs)

 

lemma coordinateMeasure_apply (B : RootBox hij k) (μ : Measure (X n))
    {S : Set (RootSlice i j k × ℝ)} (hS : MeasurableSet S) :
    B.coordinateMeasure μ S =
      μ (rootQuotientParametrization hij '' (S ∩ B.domain)) := by
  rw [coordinateMeasure,Measure.map_apply measurable_subtype_coe hS,
    B.embedding.measurableEmbedding.comap_apply]
  congr 1
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z.val,⟨hz,z.prop⟩,rfl⟩
  · rintro ⟨z,⟨hz,hzd⟩,rfl⟩
    exact ⟨⟨z,hzd⟩,hz,rfl⟩

 

theorem root_window_integral (B : RootBox hij k) (μ : Measure (X n))
    [IsFiniteMeasure μ] {S : Set (RootSlice i j k)} {T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    μ (rootQuotientParametrization hij '' ((S ×ˢ T) ∩ B.domain)) =
      ∫⁻ s in S, B.conditionalKernel μ s T ∂(B.coordinateMeasure μ).fst := by
  rw [← B.coordinateMeasure_apply μ (hS.prod hT)]
  calc
    B.coordinateMeasure μ (S ×ˢ T) =
        ((B.coordinateMeasure μ).fst ⊗ₘ B.conditionalKernel μ) (S ×ˢ T) := by
      rw [conditionalKernel,Measure.disintegrate]
    _ = _ := Measure.compProd_apply_prod hS hT

end PrimeDegreePackets.RootBox

open scoped ENNReal ProbabilityTheory
namespace PrimeDegreePackets

lemma compProd_map_measurableEquiv
    {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    (e : α ≃ᵐ γ) (f : β ≃ᵐ δ) :
    (μ ⊗ₘ κ).map (Prod.map e f) =
      μ.map e ⊗ₘ (κ.map f).comap e.symm e.symm.measurable := by
  ext S hS
  rw [Measure.map_apply (e.measurable.prodMap f.measurable) hS,
    Measure.compProd_apply ((e.measurable.prodMap f.measurable) hS),
    Measure.compProd_apply hS]
  rw [lintegral_map (Kernel.measurable_kernel_prodMk_left hS) e.measurable]
  apply lintegral_congr
  intro a
  rw [Kernel.comap_apply, e.symm_apply_apply,
    Kernel.map_apply' _ f.measurable _ (measurable_prodMk_left hS)]
  rfl

lemma fst_map_measurableEquiv
    {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (ρ : Measure (α × β)) (e : α ≃ᵐ γ) (f : β ≃ᵐ δ) :
    (ρ.map (Prod.map e f)).fst = ρ.fst.map e := by
  rw [Measure.fst, Measure.map_map measurable_fst (e.measurable.prodMap f.measurable),
    Measure.fst, Measure.map_map e.measurable measurable_fst]
  rfl

 

theorem condKernel_map_measurableEquiv
    {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace δ] [Nonempty δ]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    (e : α ≃ᵐ γ) (f : β ≃ᵐ δ) :
    ∀ᵐ a ∂ρ.fst,
      (ρ.map (Prod.map e f)).condKernel (e a) = (ρ.condKernel a).map f := by
  let κ := (ρ.condKernel.map f).comap e.symm e.symm.measurable
  have hrec : ρ.map (Prod.map e f) = (ρ.map (Prod.map e f)).fst ⊗ₘ κ := by
    rw [fst_map_measurableEquiv, ← compProd_map_measurableEquiv,Measure.disintegrate]
  have H := eq_condKernel_of_measure_eq_compProd κ hrec
  rw [fst_map_measurableEquiv] at H
  have H' := ae_of_ae_map e.measurable.aemeasurable H
  filter_upwards [H'] with a ha
  simpa only [κ,Kernel.comap_apply,e.symm_apply_apply,Kernel.map_apply _ f.measurable] using ha.symm

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma mul_diagonalOneParameter_entry {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (g : G n) (r s : Fin n) (t : ℝ) :
    (g * diagonalOneParameter ell hell t).1 r s = g.1 r s * Real.exp (ell s*t) := by
  exact Matrix.mul_diagonal _ _ _ _

 
def rootSliceDiagonal {n : ℕ} {i j k : Fin n} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) (s : RootSlice i j k) : RootSlice i j k :=
  ⟨s.val * diagonalOneParameter ell hell t, by
    constructor
    · rw [mul_diagonalOneParameter_entry]
      exact mul_ne_zero s.prop.1 (Real.exp_ne_zero _)
    · rw [mul_diagonalOneParameter_entry,s.prop.2,zero_mul]⟩

lemma rootSliceDiagonal_add {n : ℕ} {i j k : Fin n} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t u : ℝ) (s : RootSlice i j k) :
    rootSliceDiagonal ell hell (t+u) s =
      rootSliceDiagonal ell hell u (rootSliceDiagonal ell hell t s) := by
  apply Subtype.ext
  exact congrArg (s.val * ·) (diagonalOneParameter_add ell hell t u) |>.trans (mul_assoc _ _ _).symm

lemma rootSliceDiagonal_zero {n : ℕ} {i j k : Fin n} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (s : RootSlice i j k) :
    rootSliceDiagonal ell hell 0 s = s := by
  apply Subtype.ext
  simp only [rootSliceDiagonal,diagonalOneParameter_zero,mul_one]

def rootSliceDiagonalHomeomorph {n : ℕ} {i j k : Fin n} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) : RootSlice i j k ≃ₜ RootSlice i j k where
  toFun := rootSliceDiagonal ell hell t
  invFun := rootSliceDiagonal ell hell (-t)
  left_inv s := by rw [← rootSliceDiagonal_add,add_neg_cancel,rootSliceDiagonal_zero]
  right_inv s := by rw [← rootSliceDiagonal_add,neg_add_cancel,rootSliceDiagonal_zero]
  continuous_toFun := (continuous_subtype_val.mul continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.mul continuous_const).subtype_mk _

def rootTimeScaling {n : ℕ} (ell : Fin n → ℝ) (i j : Fin n) (t : ℝ) : ℝ ≃ₜ ℝ :=
  Homeomorph.mulLeft₀ (Real.exp ((ell j-ell i)*t)) (Real.exp_ne_zero _)

 

lemma rootQuotientParametrization_diagonal {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (s : RootSlice i j k) (a t : ℝ) :
    rootQuotientParametrization hij
      (rootSliceDiagonal ell hell t s, rootTimeScaling ell i j t a) =
      rightAction (rootQuotientParametrization hij (s,a)) (diagonalOneParameter ell hell t) := by
  have hC := diagonal_conjugation_transvection ell hell hij a (-t)
  have he : (ell i-ell j)*(-t) = (ell j-ell i)*t := by ring
  rw [he,diagonalOneParameter_neg,neg_neg] at hC
  change Quotient.mk _ ((s.val * diagonalOneParameter ell hell t) *
    Matrix.SpecialLinearGroup.transvection hij (Real.exp ((ell j-ell i)*t)*a)) =
    Quotient.mk _ ((s.val * Matrix.SpecialLinearGroup.transvection hij a) *
      diagonalOneParameter ell hell t)
  rw [← hC]
  congr 1
  group

 

theorem root_conditional_scaling {n : ℕ} {i j k : Fin n}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ)
    (ρ : Measure (RootSlice i j k × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ s ∂ρ.fst,
      (ρ.map (Prod.map (rootSliceDiagonalHomeomorph ell hell t)
        (rootTimeScaling ell i j t))).condKernel (rootSliceDiagonal ell hell t s) =
        (ρ.condKernel s).map (rootTimeScaling ell i j t) := by
  exact condKernel_map_measurableEquiv ρ
    (rootSliceDiagonalHomeomorph ell hell t).toMeasurableEquiv
    (rootTimeScaling ell i j t).toMeasurableEquiv

end PrimeDegreePackets


namespace PrimeDegreePackets

abbrev rootDiagonalCoordinates {n : ℕ} {i j k : Fin n} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) :
    (RootSlice i j k × ℝ) ≃ₜ (RootSlice i j k × ℝ) :=
  (rootSliceDiagonalHomeomorph ell hell t).prodCongr (rootTimeScaling ell i j t)

lemma rootDiagonalCoordinates_param {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ)
    (z : RootSlice i j k × ℝ) :
    rootQuotientParametrization hij (rootDiagonalCoordinates ell hell t z) =
      rightAction (rootQuotientParametrization hij z) (diagonalOneParameter ell hell t) :=
  rootQuotientParametrization_diagonal hij ell hell z.1 z.2 t

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

def diagonal (B : RootBox hij k) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) : RootBox hij k := by
  let e := rootSliceDiagonalHomeomorph (i := i) (j := j) (k := k) ell hell t
  let f := rootTimeScaling ell i j t
  let E := e.prodCongr f
  have hiff (z : RootSlice i j k × ℝ) :
      z ∈ B.domain ↔ E z ∈ (e '' B.transverse) ×ˢ (f '' B.time) := by
    change (z.1 ∈ B.transverse ∧ z.2 ∈ B.time) ↔
      (e z.1 ∈ e '' B.transverse ∧ f z.2 ∈ f '' B.time)
    rw [e.injective.mem_set_image,f.injective.mem_set_image]
  let eb := E.subtype hiff
  refine ⟨e '' B.transverse,f '' B.time,
    e.isOpenMap _ B.transverse_open,f.isOpenMap _ B.time_open,?_⟩
  have H := (rightActionHomeomorph (diagonalOneParameter ell hell t)).isOpenEmbedding.comp
    (B.embedding.comp eb.symm.isOpenEmbedding)
  convert H using 1
  funext z
  have he : E (eb.symm z).val = z.val := congrArg Subtype.val (eb.apply_symm_apply z)
  change rootQuotientParametrization hij z.val =
    rightAction (rootQuotientParametrization hij (eb.symm z).val) (diagonalOneParameter ell hell t)
  rw [←he]
  exact rootDiagonalCoordinates_param hij ell hell t _

lemma diagonal_domain (B : RootBox hij k) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) :
    (B.diagonal ell hell t).domain = rootDiagonalCoordinates ell hell t '' B.domain := by
  exact prod_image_image_eq

 

theorem diagonal_coordinateMeasure (B : RootBox hij k) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) (μ : Measure (X n))
    (hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ) :
    (B.diagonal ell hell t).coordinateMeasure μ =
      (B.coordinateMeasure μ).map (rootDiagonalCoordinates ell hell t) := by
  let E := rootDiagonalCoordinates (i := i) (j := j) (k := k) ell hell t
  let H := rightActionHomeomorph (diagonalOneParameter ell hell t)
  have hμ (S : Set (X n)) : μ (H '' S) = μ S := by
    calc
      μ (H '' S) = (μ.map H) (H '' S) := congrArg (fun ν => ν (H '' S)) hinv.symm
      _ = μ S := by rw [H.isOpenEmbedding.measurableEmbedding.map_apply,
        H.injective.preimage_image]
  ext S hS
  rw [Measure.map_apply E.continuous.measurable hS,
    coordinateMeasure_apply _ μ hS,
    coordinateMeasure_apply _ μ (E.continuous.measurable hS),diagonal_domain]
  rw [←hμ (rootQuotientParametrization hij '' (E ⁻¹' S ∩ B.domain))]
  congr 1
  ext x
  constructor
  · rintro ⟨z,⟨hzS,w,hw,rfl⟩,rfl⟩
    refine ⟨rootQuotientParametrization hij w,⟨w,⟨hzS,hw⟩,rfl⟩,?_⟩
    exact (rootDiagonalCoordinates_param hij ell hell t w).symm
  · rintro ⟨_,⟨w,⟨hwS,hw⟩,rfl⟩,rfl⟩
    exact ⟨E w,⟨hwS,⟨w,hw,rfl⟩⟩,rootDiagonalCoordinates_param hij ell hell t w⟩

 

theorem diagonal_conditionalKernel (B : RootBox hij k) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ) :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
      (B.diagonal ell hell t).conditionalKernel μ (rootSliceDiagonal ell hell t s) =
        (B.conditionalKernel μ s).map (rootTimeScaling ell i j t) := by
  simp only [conditionalKernel,diagonal_coordinateMeasure B ell hell t μ hinv]
  exact root_conditional_scaling ell hell t (B.coordinateMeasure μ)

end RootBox
end PrimeDegreePackets
end
end

end OAI
