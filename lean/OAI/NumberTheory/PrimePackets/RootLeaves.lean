import Mathlib
import OAI.NumberTheory.PrimePackets.LeafNormalization

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
namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 
def IsNormalizedRootLeaf (A : RootBox hij k) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : RootSlice i j k) (ν : Measure ℝ) : Prop :=
  IsLocallyFiniteMeasure ν ∧ ν A.time = 1 ∧
    ν.restrict A.time = A.conditionalKernel μ s ∧
    ∀ (m : ℕ) (B : RootBox hij k), B ∈ rootLongBoxFamily hij k R m →
      s ∈ B.transverse → ν.restrict (rootLeafWindow R m) =
        (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (rootLeafWindow R m)

 

def leafMeasure (A : RootBox hij k) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : RootSlice i j k) : Measure ℝ :=
  if h : ∃ ν : Measure ℝ, A.IsNormalizedRootLeaf R μ s ν then h.choose else 0

lemma leafMeasure_spec_of_exists (A : RootBox hij k) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : RootSlice i j k)
    (h : ∃ ν, A.IsNormalizedRootLeaf R μ s ν) :
    A.IsNormalizedRootLeaf R μ s (A.leafMeasure R μ s) := by
  simpa only [leafMeasure,dite_eq_left h] using h.choose_spec

 
theorem ae_leafMeasure_spec (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      A.IsNormalizedRootLeaf R μ s (A.leafMeasure R μ s) := by
  filter_upwards [A.ae_exists_rootLeafMeasure R hAR μ hfree] with s hs
  exact A.leafMeasure_spec_of_exists R μ s hs

lemma IsNormalizedRootLeaf.unique (A : RootBox hij k) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : RootSlice i j k)
    (hs : Function.Injective (fun t : ℝ => rootQuotientParametrization hij (s,t)))
    {ν ρ : Measure ℝ} (hν : A.IsNormalizedRootLeaf R μ s ν)
    (hρ : A.IsNormalizedRootLeaf R μ s ρ) : ν = ρ :=
  A.rootLeafMeasure_unique R μ s hs ν ρ hν.2.2.2 hρ.2.2.2

lemma IsNormalizedRootLeaf.ne_zero (A : RootBox hij k) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : RootSlice i j k)
    {ν : Measure ℝ} (hν : A.IsNormalizedRootLeaf R μ s ν) : ν ≠ 0 := by
  intro hz
  have H := hν.2.1
  simp only [hz,Measure.coe_zero,Pi.zero_apply,zero_ne_one] at H

end PrimeDegreePackets.RootBox


namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

theorem ae_leafMeasure_restrict (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (D : RootBox hij k) (hAD : A.time ⊆ D.time) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ D.transverse →
      D.conditionalKernel μ s A.time ≠ 0 ∧
      (A.leafMeasure R μ s).restrict D.time =
        (anchorNormalize (D.conditionalKernel μ s) A.time).restrict D.time := by
  let C := rootLongBoxFamily hij k R
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k R m).to_subtype
  have hT (m : ℕ) (B : C m) : B.val.time = rootLeafWindow R m :=
    rootLongBoxFamily_time hij k R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (rootLeafWindow_mono R (Nat.zero_le m))
  have hp : ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      ∀ (m : ℕ) (B : C m), s ∈ B.val.transverse → s ∈ D.transverse →
        (anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict (B.val.time ∩ D.time) =
          (anchorNormalize (D.conditionalKernel μ s) A.time).restrict (B.val.time ∩ D.time) := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    filter_upwards [base_overlap_anchorNormalize A B.val D (hinc m B) hAD μ] with s hs
    exact fun hB hD => (hs hB hD).2.2
  filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree,
    A.ae_injective_root_slice_of_ae_free μ hfree,hp,base_anchor_restrict A D hAD μ]
      with s hs hi hp ha
  intro hsD
  refine ⟨(ha hsD).1,?_⟩
  apply measure_eq_of_restrictionChain (rootLeafWindow R) (rootLeafWindow_mono R)
    (rootLeafWindow_cover R)
  intro m
  obtain ⟨B,hBC,hsB⟩ := rootLongBoxFamily_covers hij k R m s hi
  let B' : C m := ⟨B,hBC⟩
  have H := hp m B' hsB hsD
  rw [hT m B'] at H
  calc
    ((A.leafMeasure R μ s).restrict D.time).restrict (rootLeafWindow R m) =
        ((A.leafMeasure R μ s).restrict (rootLeafWindow R m)).restrict D.time :=
      Measure.restrict_comm (rootLeafWindow_open R m).measurableSet
    _ = ((anchorNormalize (B.conditionalKernel μ s) A.time).restrict (rootLeafWindow R m)).restrict D.time := by
      rw [hs.2.2.2 m B hBC hsB]
    _ = (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (rootLeafWindow R m ∩ D.time) := by
      rw [Measure.restrict_restrict D.time_open.measurableSet,inter_comm]
    _ = (anchorNormalize (D.conditionalKernel μ s) A.time).restrict (rootLeafWindow R m ∩ D.time) := H
    _ = ((anchorNormalize (D.conditionalKernel μ s) A.time).restrict D.time).restrict (rootLeafWindow R m) :=
      (Measure.restrict_restrict (rootLeafWindow_open R m).measurableSet).symm

 
theorem ae_leafMeasure_radius_independent (A : RootBox hij k) (R S : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0) (hAS : A.time ⊆ rootLeafWindow S 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    A.leafMeasure R μ =ᵐ[(A.coordinateMeasure μ).fst] A.leafMeasure S μ := by
  let C := rootLongBoxFamily hij k S
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k S m).to_subtype
  have hT (m : ℕ) (B : C m) : B.val.time = rootLeafWindow S m :=
    rootLongBoxFamily_time hij k S m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAS.trans (rootLeafWindow_mono S (Nat.zero_le m))
  have H : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ (m : ℕ) (B : C m),
      s ∈ B.val.transverse →
      (A.leafMeasure R μ s).restrict (rootLeafWindow S m) =
        (anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict (rootLeafWindow S m) := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    filter_upwards [A.ae_leafMeasure_restrict R hAR μ hfree B.val (hinc m B)] with s hs
    intro hsB
    simpa only [hT m B] using (hs hsB).2
  filter_upwards [A.ae_leafMeasure_spec S hAS μ hfree,
    A.ae_injective_root_slice_of_ae_free μ hfree,H] with s hs hi hR
  apply A.rootLeafMeasure_unique S μ s hi _ _ _ hs.2.2.2
  intro m B hB hsB
  exact hR m ⟨B,hB⟩ hsB

end PrimeDegreePackets.RootBox


namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

theorem aemeasurable_leafMeasure_apply (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    {S : Set ℝ} (hS : MeasurableSet S) :
    AEMeasurable (fun s => A.leafMeasure R μ s S) (A.coordinateMeasure μ).fst := by
  let C := rootLongBoxFamily hij k R
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k R m).to_subtype
  have hm (m : ℕ) : AEMeasurable
      (fun s => A.leafMeasure R μ s (S ∩ rootLeafWindow R m)) (A.coordinateMeasure μ).fst := by
    let U := ⋃ B : C m, B.val.transverse
    have hU : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ U := by
      filter_upwards [A.ae_injective_root_slice_of_ae_free μ hfree] with s hs
      obtain ⟨B,hB,hsB⟩ := rootLongBoxFamily_covers hij k R m s hs
      exact mem_iUnion.mpr ⟨⟨B,hB⟩,hsB⟩
    have H : AEMeasurable (fun s => A.leafMeasure R μ s (S ∩ rootLeafWindow R m))
        ((A.coordinateMeasure μ).fst.restrict U) := by
      apply aemeasurable_iUnion_iff.mpr
      intro B
      have hM : Measurable (fun s =>
          anchorNormalize (B.val.conditionalKernel μ s) A.time (S ∩ rootLeafWindow R m)) := by
        simp only [anchorNormalize,Measure.smul_apply,smul_eq_mul]
        exact ((B.val.conditionalKernel μ).measurable_coe A.time_open.measurableSet).inv.mul
          ((B.val.conditionalKernel μ).measurable_coe (hS.inter (rootLeafWindow_open R m).measurableSet))
      apply hM.aemeasurable.congr
      change ∀ᵐ s ∂(A.coordinateMeasure μ).fst.restrict B.val.transverse,
        anchorNormalize (B.val.conditionalKernel μ s) A.time (S ∩ rootLeafWindow R m) =
          A.leafMeasure R μ s (S ∩ rootLeafWindow R m)
      rw [ae_restrict_iff' B.val.transverse_open.measurableSet]
      filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree] with s hs
      intro hsB
      have H := congrArg (fun ξ : Measure ℝ => ξ S) (hs.2.2.2 m B.val B.prop hsB)
      simpa only [Measure.restrict_apply hS] using H.symm
    simpa only [Measure.restrict_eq_self_of_ae_mem hU] using H
  have he (s : RootSlice i j k) : A.leafMeasure R μ s S =
      ⨆ m, A.leafMeasure R μ s (S ∩ rootLeafWindow R m) := by
    have hset : S = ⋃ m, S ∩ rootLeafWindow R m := by
      rw [←inter_iUnion,rootLeafWindow_cover,inter_univ]
    conv_lhs => rw [hset]
    exact (show Monotone (fun m => S ∩ rootLeafWindow R m) from
      fun a b hab => inter_subset_inter_right S (rootLeafWindow_mono R hab)).measure_iUnion
  simp_rw [he]
  exact AEMeasurable.iSup hm

 

theorem aemeasurable_log_leafMeasure (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    {S : Set ℝ} (hS : MeasurableSet S) :
    AEMeasurable (fun s => Real.log (A.leafMeasure R μ s S).toReal) (A.coordinateMeasure μ).fst :=
  (A.aemeasurable_leafMeasure_apply R hAR μ hfree hS).ennreal_toReal.log

end PrimeDegreePackets.RootBox

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
namespace PrimeDegreePackets

 

lemma normalized_translation_invariant_measure (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (J : Set ℝ) (hJ : ν J = 1)
    (hinv : ∀ a : ℝ, Measure.map (fun t : ℝ => t+a) ν = ν) :
    ∃ c : ℝ≥0, ν = c • (volume : Measure ℝ) ∧ (c : ℝ≥0∞) = (volume J)⁻¹ := by
  let : ν.IsAddLeftInvariant := ⟨fun a => by simpa only [add_comm] using hinv a⟩
  let c := addHaarScalarFactor ν (volume : Measure ℝ)
  have he : ν = c • (volume : Measure ℝ) := isAddLeftInvariant_eq_smul ν volume
  refine ⟨c,he,?_⟩
  apply ENNReal.eq_inv_of_mul_eq_one_left
  have H := hJ
  rw [he,Measure.smul_apply] at H
  simpa only [ENNReal.smul_def,smul_eq_mul] using H

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

theorem hasHaarConditionals_of_invariant_leafMeasure (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (hinv : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ a : ℝ,
      Measure.map (fun t : ℝ => t+a) (A.leafMeasure R μ s) = A.leafMeasure R μ s) :
    A.HasHaarConditionals μ := by
  have H : ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      ∃ c : ℝ≥0, A.conditionalKernel μ s = c • volume.restrict A.time ∧
        (c : ℝ≥0∞) = (volume A.time)⁻¹ := by
    filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree,hinv] with s hs hi
    let := hs.1
    obtain ⟨c,hc,hcV⟩ := normalized_translation_invariant_measure
      (A.leafMeasure R μ s) A.time hs.2.1 hi
    refine ⟨c,?_,hcV⟩
    rw [←hs.2.2.1,hc,Measure.restrict_smul]
  by_cases hz : (A.coordinateMeasure μ).fst = 0
  · exact ⟨0,by simp only [hz,ae_zero,Filter.eventually_bot]⟩
  · let : NeZero (A.coordinateMeasure μ).fst := ⟨hz⟩
    obtain ⟨s,hs⟩ := H.exists
    obtain ⟨c,hc,hcV⟩ := hs
    refine ⟨c,?_⟩
    filter_upwards [H] with t ht
    obtain ⟨d,hd,hdV⟩ := ht
    have hdc : d = c := ENNReal.coe_injective (hdV.trans hcV.symm)
    simpa only [hdc] using hd

end RootBox
end PrimeDegreePackets


namespace PrimeDegreePackets

lemma anchorNormalize_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) (e : α ≃ᵐ β) (J : Set α) :
    anchorNormalize (ν.map e) (e '' J) = (anchorNormalize ν J).map e := by
  unfold anchorNormalize
  rw [e.measurableEmbedding.map_apply,e.injective.preimage_image,
    Measure.map_smul _ e.measurable.aemeasurable]

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

lemma base_ae_of_ae (A B : RootBox hij k) (hAB : A.time ⊆ B.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ] {p : RootSlice i j k → Prop}
    (hp : ∀ᵐ s ∂(B.coordinateMeasure μ).fst, p s) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ B.transverse → p s := by
  let U := A.transverse ∩ B.transverse
  have hU : IsOpen U := A.transverse_open.inter B.transverse_open
  have H := (B.shrink_marginal_absolutelyContinuous U A.time hU A.time_open
    inter_subset_right hAB μ).ae_le (ae_restrict_of_ae hp)
  have hE : B.shrink U A.time hU A.time_open inter_subset_right hAB =
      A.shrink U A.time hU A.time_open inter_subset_left subset_rfl := rfl
  rw [hE,A.shrink_full_time_marginal] at H
  have H' := (ae_restrict_iff' hU.measurableSet).mp H
  filter_upwards [H',A.coordinateMeasure_fst_ae_transverse μ] with s hs hsA
  exact fun hsB => hs ⟨hsA,hsB⟩

lemma diagonal_marginal (A : RootBox hij k) (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) (μ : Measure (X n))
    (hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ) :
    ((A.diagonal ell hell t).coordinateMeasure μ).fst =
      (A.coordinateMeasure μ).fst.map (rootSliceDiagonalHomeomorph ell hell t) := by
  rw [A.diagonal_coordinateMeasure ell hell t μ hinv]
  exact fst_map_measurableEquiv (A.coordinateMeasure μ)
    (rootSliceDiagonalHomeomorph ell hell t).toMeasurableEquiv
    (rootTimeScaling ell i j t).toMeasurableEquiv

 

theorem ae_leafMeasure_diagonal (A : RootBox hij k) (R S : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0) (t : ℝ)
    (hAS : (A.diagonal ell hell t).time ⊆ rootLeafWindow S 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (hinv : μ.map (fun x => rightAction x (diagonalOneParameter ell hell t)) = μ) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      (A.diagonal ell hell t).leafMeasure S μ (rootSliceDiagonal ell hell t s) =
        (A.leafMeasure R μ s).map (rootTimeScaling ell i j t) := by
  let C := rootLongBoxFamily hij k R
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k R m).to_subtype
  let e := rootSliceDiagonalHomeomorph (i := i) (j := j) (k := k) ell hell t
  let f := rootTimeScaling ell i j t
  let AD := A.diagonal ell hell t
  have hT (m : ℕ) (B : C m) : B.val.time = rootLeafWindow R m :=
    rootLongBoxFamily_time hij k R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (rootLeafWindow_mono R (Nat.zero_le m))
  have hincD (m : ℕ) (B : C m) : AD.time ⊆ (B.val.diagonal ell hell t).time :=
    image_mono (hinc m B)
  have hcov : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ (m : ℕ) (B : C m),
      s ∈ B.val.transverse →
      (B.val.diagonal ell hell t).conditionalKernel μ (e s) =
        (B.val.conditionalKernel μ s).map f := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    exact base_ae_of_ae A B.val (hinc m B) μ
      (B.val.diagonal_conditionalKernel ell hell t μ hinv)
  have hD : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ (m : ℕ) (B : C m),
      s ∈ B.val.transverse →
      (AD.leafMeasure S μ (e s)).restrict (f '' B.val.time) =
        (anchorNormalize ((B.val.diagonal ell hell t).conditionalKernel μ (e s))
          (f '' A.time)).restrict (f '' B.val.time) := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    have H := AD.ae_leafMeasure_restrict S hAS μ hfree
      (B.val.diagonal ell hell t) (hincD m B)
    rw [A.diagonal_marginal ell hell t μ hinv] at H
    have H' := e.toMeasurableEquiv.measurableEmbedding.ae_map_iff.mp H
    filter_upwards [H'] with s hs
    intro hsB
    exact (hs (mem_image_of_mem e hsB)).2
  filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree,
    A.ae_injective_root_slice_of_ae_free μ hfree,hcov,hD] with s hs hi hc hd
  apply measure_eq_of_restrictionChain (fun m => f '' rootLeafWindow R m)
    (fun a b hab => image_mono (rootLeafWindow_mono R hab))
    (by rw [←image_iUnion,rootLeafWindow_cover,image_univ,f.surjective.range_eq])
  intro m
  obtain ⟨B,hBC,hsB⟩ := rootLongBoxFamily_covers hij k R m s hi
  let B' : C m := ⟨B,hBC⟩
  have H := hd m B' hsB
  rw [hc m B' hsB] at H
  have ha : anchorNormalize ((B.conditionalKernel μ s).map f) (f '' A.time) =
      (anchorNormalize (B.conditionalKernel μ s) A.time).map f :=
    anchorNormalize_map_equiv (B.conditionalKernel μ s) f.toMeasurableEquiv A.time
  change (AD.leafMeasure S μ (e s)).restrict (f '' B.time) =
    (anchorNormalize ((B.conditionalKernel μ s).map f) (f '' A.time)).restrict (f '' B.time) at H
  rw [ha] at H
  change (AD.leafMeasure S μ (e s)).restrict (f '' rootLeafWindow R m) =
    ((A.leafMeasure R μ s).map f).restrict (f '' rootLeafWindow R m)
  have hmap (ν : Measure ℝ) (J : Set ℝ) :
      (ν.map f).restrict (f '' J) = (ν.restrict J).map f := by
    exact (f.toMeasurableEquiv.restrict_map ν (f '' J)).trans
      (congrArg (fun T : Set ℝ => (ν.restrict T).map f) (f.injective.preimage_image J))
  rw [hmap,hs.2.2.2 m B hBC hsB]
  rw [hmap] at H
  simpa only [rootLongBoxFamily_time hij k R m B hBC] using H

end RootBox
end PrimeDegreePackets


namespace PrimeDegreePackets

lemma measurable_measure_restrict {α : Type*} [MeasurableSpace α]
    {S : Set α} (hS : MeasurableSet S) :
    Measurable (fun ν : Measure α => ν.restrict S) := by
  apply Measure.measurable_of_measurable_coe
  intro T hT
  simp only [Measure.restrict_apply hT]
  exact Measure.measurable_coe (hT.inter hS)

lemma measurable_measure_sum {α : Type*} [MeasurableSpace α] :
    Measurable (fun ν : ℕ → Measure α => Measure.sum ν) := by
  apply Measure.measurable_of_measurable_coe
  intro T hT
  simp only [Measure.sum_apply _ hT]
  exact Measurable.tsum (fun m => (Measure.measurable_coe hT).comp (measurable_pi_apply m))

lemma measure_eq_sum_disjointed {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (W : ℕ → Set α) (hW : ∀ m, MeasurableSet (W m))
    (hcov : ⋃ m, W m = univ) :
    ν = Measure.sum (fun m => ν.restrict (disjointed W m)) := by
  have H := ν.restrict_iUnion (disjoint_disjointed W) (MeasurableSet.disjointed hW)
  rw [iUnion_disjointed,hcov,Measure.restrict_univ] at H
  exact H

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

lemma aemeasurable_leafMeasure_restrict_window (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (m : ℕ) :
    AEMeasurable (fun s => (A.leafMeasure R μ s).restrict (rootLeafWindow R m))
      (A.coordinateMeasure μ).fst := by
  let C := rootLongBoxFamily hij k R
  let : Countable (C m) := (rootLongBoxFamily_countable hij k R m).to_subtype
  let U := ⋃ B : C m, B.val.transverse
  have hU : ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ U := by
    filter_upwards [A.ae_injective_root_slice_of_ae_free μ hfree] with s hs
    obtain ⟨B,hB,hsB⟩ := rootLongBoxFamily_covers hij k R m s hs
    exact mem_iUnion.mpr ⟨⟨B,hB⟩,hsB⟩
  have H : AEMeasurable (fun s => (A.leafMeasure R μ s).restrict (rootLeafWindow R m))
      ((A.coordinateMeasure μ).fst.restrict U) := by
    apply aemeasurable_iUnion_iff.mpr
    intro B
    have hM : Measurable (fun s =>
        (anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict (rootLeafWindow R m)) := by
      apply Measure.measurable_of_measurable_coe
      intro T hT
      simp only [Measure.restrict_apply hT,anchorNormalize,Measure.smul_apply,smul_eq_mul]
      exact ((B.val.conditionalKernel μ).measurable_coe A.time_open.measurableSet).inv.mul
        ((B.val.conditionalKernel μ).measurable_coe (hT.inter (rootLeafWindow_open R m).measurableSet))
    apply hM.aemeasurable.congr
    change ∀ᵐ s ∂(A.coordinateMeasure μ).fst.restrict B.val.transverse, _
    rw [ae_restrict_iff' B.val.transverse_open.measurableSet]
    filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree] with s hs
    intro hsB
    exact (hs.2.2.2 m B.val B.prop hsB).symm
  simpa only [Measure.restrict_eq_self_of_ae_mem hU] using H

 

theorem aemeasurable_leafMeasure (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    AEMeasurable (A.leafMeasure R μ) (A.coordinateMeasure μ).fst := by
  let W := rootLeafWindow R
  let V := disjointed W
  have hV (m : ℕ) : MeasurableSet (V m) :=
    MeasurableSet.disjointed (fun m => (rootLeafWindow_open R m).measurableSet) m
  have hM (m : ℕ) : AEMeasurable
      (fun s => (A.leafMeasure R μ s).restrict (V m)) (A.coordinateMeasure μ).fst := by
    have H := (measurable_measure_restrict (hV m)).comp_aemeasurable
      (A.aemeasurable_leafMeasure_restrict_window R hAR μ hfree m)
    change AEMeasurable (fun s => ((A.leafMeasure R μ s).restrict (W m)).restrict (V m))
      (A.coordinateMeasure μ).fst at H
    have hVW : V m ∩ W m = V m := inter_eq_left.mpr (disjointed_subset W m)
    simpa only [Measure.restrict_restrict (hV m),hVW] using H
  have hE (s : RootSlice i j k) : A.leafMeasure R μ s =
      Measure.sum (fun m => (A.leafMeasure R μ s).restrict (V m)) := by
    exact measure_eq_sum_disjointed (A.leafMeasure R μ s) W
      (fun m => (rootLeafWindow_open R m).measurableSet) (rootLeafWindow_cover R)
  exact (measurable_measure_sum.comp_aemeasurable (aemeasurable_pi_iff.mpr hM)).congr
    (ae_of_all _ fun s => (hE s).symm)

 

def leafKernel (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    Kernel (RootSlice i j k) ℝ where
  toFun := (A.aemeasurable_leafMeasure R hAR μ hfree).mk (A.leafMeasure R μ)
  measurable' := (A.aemeasurable_leafMeasure R hAR μ hfree).measurable_mk

lemma ae_leafKernel_eq (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      A.leafKernel R hAR μ hfree s = A.leafMeasure R μ s :=
  (A.aemeasurable_leafMeasure R hAR μ hfree).ae_eq_mk.symm

end RootBox
end PrimeDegreePackets
end
end

end OAI
