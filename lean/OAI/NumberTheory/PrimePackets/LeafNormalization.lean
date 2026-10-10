import Mathlib
import OAI.NumberTheory.PrimePackets.ZeroSeparation

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
namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

lemma shrink_marginal_absolutelyContinuous (B : RootBox hij k)
    (U : Set (RootSlice i j k)) (J : Set ℝ) (hU : IsOpen U) (hJ : IsOpen J)
    (hUB : U ⊆ B.transverse) (hJB : J ⊆ B.time) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ((B.shrink U J hU hJ hUB hJB).coordinateMeasure μ).fst ≪
      (B.coordinateMeasure μ).fst.restrict U := by
  rw [shrink_marginal]
  exact withDensity_absolutelyContinuous _ _

lemma shrink_marginal_ae_anchor_pos (B : RootBox hij k)
    (U : Set (RootSlice i j k)) (J : Set ℝ) (hU : IsOpen U) (hJ : IsOpen J)
    (hUB : U ⊆ B.transverse) (hJB : J ⊆ B.time) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ∀ᵐ s ∂((B.shrink U J hU hJ hUB hJB).coordinateMeasure μ).fst,
      B.conditionalKernel μ s J ≠ 0 := by
  rw [shrink_marginal]
  exact (ae_withDensity_iff (B.conditionalKernel μ |>.measurable_coe hJ.measurableSet)).mpr
    (ae_of_all _ fun _ h => h)

 

theorem overlap_anchorNormalize (B C : RootBox hij k)
    (U : Set (RootSlice i j k)) (J : Set ℝ) (hU : IsOpen U) (hJ : IsOpen J)
    (hUB : U ⊆ B.transverse) (hUC : U ⊆ C.transverse)
    (hJB : J ⊆ B.time) (hJC : J ⊆ C.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ s ∂((B.shrink U J hU hJ hUB hJB).coordinateMeasure μ).fst,
      B.conditionalKernel μ s J ≠ 0 ∧ C.conditionalKernel μ s J ≠ 0 ∧
      (anchorNormalize (B.conditionalKernel μ s) J).restrict (B.time ∩ C.time) =
        (anchorNormalize (C.conditionalKernel μ s) J).restrict (B.time ∩ C.time) := by
  let V := B.time ∩ C.time
  have hV : IsOpen V := B.time_open.inter C.time_open
  let D := B.shrink U V hU hV hUB inter_subset_left
  have hD : D = C.shrink U V hU hV hUC inter_subset_right := rfl
  have hA : B.shrink U J hU hJ hUB hJB = C.shrink U J hU hJ hUC hJC := rfl
  have hB := (B.shrink_marginal_absolutelyContinuous U J hU hJ hUB hJB μ).ae_le
    (B.shrink_conditionalKernel U V hU hV hUB inter_subset_left μ)
  have hC := (C.shrink_marginal_absolutelyContinuous U J hU hJ hUC hJC μ).ae_le
    (C.shrink_conditionalKernel U V hU hV hUC inter_subset_right μ)
  rw [←hA] at hC
  have hpB := B.shrink_marginal_ae_anchor_pos U J hU hJ hUB hJB μ
  have hpC := C.shrink_marginal_ae_anchor_pos U J hU hJ hUC hJC μ
  rw [←hA] at hpC
  filter_upwards [hB,hC,hpB,hpC] with s hsB hsC hpB hpC
  have hJV : J ⊆ V := subset_inter hJB hJC
  have H₁ := (anchorNormalize_restrict _ _ hJ.measurableSet hJV hsB hpB).2
  have H₂ := (anchorNormalize_restrict _ _ hJ.measurableSet hJV hsC hpC).2
  refine ⟨hpB,hpC,?_⟩
  exact H₁.symm.trans H₂

 
theorem overlap_anchorNormalize_restrict (B C : RootBox hij k)
    (U : Set (RootSlice i j k)) (J : Set ℝ) (hU : IsOpen U) (hJ : IsOpen J)
    (hUB : U ⊆ B.transverse) (hUC : U ⊆ C.transverse)
    (hJB : J ⊆ B.time) (hJC : J ⊆ C.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    {W : Set ℝ} (hW : MeasurableSet W) (hWB : W ⊆ B.time) (hWC : W ⊆ C.time) :
    ∀ᵐ s ∂((B.shrink U J hU hJ hUB hJB).coordinateMeasure μ).fst,
      (anchorNormalize (B.conditionalKernel μ s) J).restrict W =
        (anchorNormalize (C.conditionalKernel μ s) J).restrict W := by
  filter_upwards [overlap_anchorNormalize B C U J hU hJ hUB hUC hJB hJC μ] with s hs
  have H := congrArg (fun ξ : Measure ℝ => ξ.restrict W) hs.2.2
  simpa only [Measure.restrict_restrict hW,inter_eq_left.mpr (subset_inter hWB hWC)] using H

end PrimeDegreePackets.RootBox

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
namespace PrimeDegreePackets

instance rootSliceSecondCountable {n : ℕ} (i j k : Fin n) :
    SecondCountableTopology (RootSlice i j k) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

 

theorem exists_countable_rootBoxes_exact_time {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (a b : ℝ) :
    ∃ C : Set (RootBox hij k), C.Countable ∧
      (∀ B ∈ C, B.time = Ioo a b) ∧
      ∀ s : RootSlice i j k,
        Function.Injective (fun t : ℝ => rootQuotientParametrization hij (s,t)) →
        ∃ B ∈ C, s ∈ B.transverse := by
  let Good := {B : RootBox hij k | B.time = Ioo a b}
  obtain ⟨C,hCG,hCc,hC⟩ := isOpen_biUnion_countable Good
    (fun B : RootBox hij k => B.transverse) (fun B _ => B.transverse_open)
  refine ⟨C,hCc,fun B hB => hCG hB,?_⟩
  intro s hs
  obtain ⟨B,hsB,hT⟩ := rootBox_contains_compact_time hij s hs a b
  let D := B.shrink B.transverse (Ioo a b) B.transverse_open isOpen_Ioo
    subset_rfl (Ioo_subset_Icc_self.trans hT)
  have hD : D ∈ Good := rfl
  have H : s ∈ ⋃ B ∈ Good, B.transverse := mem_iUnion.mpr ⟨D,mem_iUnion.mpr ⟨hD,hsB⟩⟩
  rw [←hC] at H
  simpa only [mem_iUnion,exists_prop] using H

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

theorem ae_injective_root_slice_of_ae_free (B : RootBox hij k)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
      Function.Injective (fun t : ℝ => rootQuotientParametrization hij (s,t)) := by
  have hf : ∀ᵐ z ∂B.coordinateMeasure μ, ∀ v : ℝ,
      rightAction (rootQuotientParametrization hij z)
        (Matrix.SpecialLinearGroup.transvection hij v) = rootQuotientParametrization hij z →
          v = 0 := by
    apply ae_of_ae_map (μ := B.coordinateMeasure μ)
      (f := rootQuotientParametrization (k := k) hij)
      (p := fun x => ∀ v : ℝ,
        rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
      (rootQuotientParametrization_localHomeomorph hij).continuous.measurable.aemeasurable
    rw [B.map_coordinateMeasure]
    exact ae_restrict_of_ae hfree
  rw [←Measure.disintegrate (B.coordinateMeasure μ) (B.coordinateMeasure μ).condKernel] at hf
  have H := Measure.ae_ae_of_ae_compProd hf
  filter_upwards [H] with s hs
  obtain ⟨t,ht⟩ := hs.exists
  exact root_time_injective_of_free hij s t ht

 
theorem ae_injective_root_slice (d : ℕ) {i j k : Fin (d+1)} (hij : i ≠ j)
    (B : RootBox hij k) (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) μ = μ) :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
      Function.Injective (fun t : ℝ => rootQuotientParametrization hij (s,t)) := by
  apply B.ae_injective_root_slice_of_ae_free μ
  filter_upwards [ae_root_stabilizer_trivial d μ hA] with x hx
  exact hx i j hij

 

lemma shrink_full_time_marginal (B : RootBox hij k)
    (U : Set (RootSlice i j k)) (hU : IsOpen U) (hUB : U ⊆ B.transverse)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ((B.shrink U B.time hU B.time_open hUB subset_rfl).coordinateMeasure μ).fst =
      (B.coordinateMeasure μ).fst.restrict U := by
  rw [shrink_marginal]
  calc
    _ = ((B.coordinateMeasure μ).fst.restrict U).withDensity 1 := by
      apply withDensity_congr_ae
      exact ae_restrict_of_ae (B.conditionalKernel_time_mass μ)
    _ = _ := withDensity_one

end RootBox
end PrimeDegreePackets


namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

theorem base_overlap_anchorNormalize (A B C : RootBox hij k)
    (hAB : A.time ⊆ B.time) (hAC : A.time ⊆ C.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      s ∈ B.transverse → s ∈ C.transverse →
      B.conditionalKernel μ s A.time ≠ 0 ∧ C.conditionalKernel μ s A.time ≠ 0 ∧
      (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (B.time ∩ C.time) =
        (anchorNormalize (C.conditionalKernel μ s) A.time).restrict (B.time ∩ C.time) := by
  let U := A.transverse ∩ B.transverse ∩ C.transverse
  have hU : IsOpen U := (A.transverse_open.inter B.transverse_open).inter C.transverse_open
  have hUA : U ⊆ A.transverse := inter_subset_left.trans inter_subset_left
  have hUB : U ⊆ B.transverse := inter_subset_left.trans inter_subset_right
  have hUC : U ⊆ C.transverse := inter_subset_right
  have H := overlap_anchorNormalize B C U A.time hU A.time_open hUB hUC hAB hAC μ
  have hD : B.shrink U A.time hU A.time_open hUB hAB =
      A.shrink U A.time hU A.time_open hUA subset_rfl := rfl
  rw [hD,A.shrink_full_time_marginal] at H
  have H' := (ae_restrict_iff' hU.measurableSet).mp H
  filter_upwards [H',A.coordinateMeasure_fst_ae_transverse μ] with s hs hsA
  intro hsB hsC
  exact hs ⟨⟨hsA,hsB⟩,hsC⟩

 

theorem base_anchor_restrict (A B : RootBox hij k) (hAB : A.time ⊆ B.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, s ∈ B.transverse →
      B.conditionalKernel μ s A.time ≠ 0 ∧
      (anchorNormalize (B.conditionalKernel μ s) A.time).restrict A.time =
        A.conditionalKernel μ s := by
  filter_upwards [base_overlap_anchorNormalize A A B subset_rfl hAB μ,
    A.coordinateMeasure_fst_ae_transverse μ,A.conditionalKernel_time_mass μ,
    A.conditionalKernel_ae_time μ] with s hs hsA hm ht
  intro hsB
  have H := hs hsA hsB
  refine ⟨H.2.1,?_⟩
  rw [inter_eq_left.mpr hAB] at H
  rw [←H.2.2]
  have hn : anchorNormalize (A.conditionalKernel μ s) A.time = A.conditionalKernel μ s := by
    simp only [anchorNormalize,hm,inv_one,one_smul]
  rw [hn]
  exact Measure.restrict_eq_self_of_ae_mem ht

 
theorem base_overlap_restrict (A B C : RootBox hij k)
    (hAB : A.time ⊆ B.time) (hAC : A.time ⊆ C.time)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    {W : Set ℝ} (hW : MeasurableSet W) (hWB : W ⊆ B.time) (hWC : W ⊆ C.time) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      s ∈ B.transverse → s ∈ C.transverse →
      (anchorNormalize (B.conditionalKernel μ s) A.time).restrict W =
        (anchorNormalize (C.conditionalKernel μ s) A.time).restrict W := by
  filter_upwards [base_overlap_anchorNormalize A B C hAB hAC μ] with s hs
  intro hsB hsC
  have H := congrArg (fun ν : Measure ℝ => ν.restrict W) (hs hsB hsC).2.2
  simpa only [Measure.restrict_restrict hW,inter_eq_left.mpr (subset_inter hWB hWC)] using H

end PrimeDegreePackets.RootBox


namespace PrimeDegreePackets

 
def rootLeafWindow (R : ℝ) (m : ℕ) : Set ℝ := Ioo (-(R+m)) (R+m)

lemma rootLeafWindow_open (R : ℝ) (m : ℕ) : IsOpen (rootLeafWindow R m) := isOpen_Ioo

lemma rootLeafWindow_mono (R : ℝ) : Monotone (rootLeafWindow R) := by
  intro a b hab
  have h : (a : ℝ) ≤ b := Nat.cast_le.mpr hab
  exact Ioo_subset_Ioo (by linarith) (by linarith)

lemma rootLeafWindow_cover (R : ℝ) : ⋃ m, rootLeafWindow R m = univ := by
  apply Set.eq_univ_of_forall
  intro t
  obtain ⟨m,hm⟩ := exists_nat_gt (|t|+|R|)
  apply mem_iUnion.mpr
  refine ⟨m,?_,?_⟩
  · have h₁ := neg_abs_le t
    have h₂ := neg_abs_le R
    linarith
  · have h₁ := le_abs_self t
    have h₂ := neg_abs_le R
    linarith

variable {n : ℕ} {i j k : Fin n}

 
def rootLongBoxFamily (hij : i ≠ j) (k : Fin n) (R : ℝ) (m : ℕ) : Set (RootBox hij k) :=
  (exists_countable_rootBoxes_exact_time (k := k) hij (-(R+m)) (R+m)).choose

lemma rootLongBoxFamily_countable (hij : i ≠ j) (k : Fin n) (R : ℝ) (m : ℕ) :
    (rootLongBoxFamily hij k R m).Countable :=
  (exists_countable_rootBoxes_exact_time (k := k) hij (-(R+m)) (R+m)).choose_spec.1

lemma rootLongBoxFamily_time (hij : i ≠ j) (k : Fin n) (R : ℝ) (m : ℕ)
    (B : RootBox hij k) (hB : B ∈ rootLongBoxFamily hij k R m) :
    B.time = rootLeafWindow R m :=
  (exists_countable_rootBoxes_exact_time (k := k) hij (-(R+m)) (R+m)).choose_spec.2.1 B hB

lemma rootLongBoxFamily_covers (hij : i ≠ j) (k : Fin n) (R : ℝ) (m : ℕ)
    (s : RootSlice i j k)
    (hs : Function.Injective (fun t : ℝ => rootQuotientParametrization hij (s,t))) :
    ∃ B ∈ rootLongBoxFamily hij k R m, s ∈ B.transverse :=
  (exists_countable_rootBoxes_exact_time (k := k) hij (-(R+m)) (R+m)).choose_spec.2.2 s hs

end PrimeDegreePackets


namespace PrimeDegreePackets

variable {α : Type*} [MeasurableSpace α]

 
def increasingMeasureLimit (ν : ℕ → Measure α) (hν : Monotone ν) : Measure α :=
  Measure.ofMeasurable (fun S _ => ⨆ m, ν m S) (by simp) (by
    intro S hS hdis
    simp_rw [measure_iUnion hdis hS]
    have h := lintegral_iSup (μ := Measure.count)
      (fun m => measurable_of_countable (f := fun k : ℕ => ν m (S k)))
      (show Monotone (fun m k => ν m (S k)) from fun a b hab k => hν hab (S k))
    simpa only [lintegral_count] using h.symm)

lemma increasingMeasureLimit_apply (ν : ℕ → Measure α) (hν : Monotone ν)
    {S : Set α} (hS : MeasurableSet S) :
    increasingMeasureLimit ν hν S = ⨆ m, ν m S :=
  Measure.ofMeasurable_apply S hS

lemma le_increasingMeasureLimit (ν : ℕ → Measure α) (hν : Monotone ν) (m : ℕ) :
    ν m ≤ increasingMeasureLimit ν hν := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [increasingMeasureLimit_apply ν hν hS]
  exact le_iSup (fun j => ν j S) m

lemma increasingMeasureLimit_le (ν : ℕ → Measure α) (hν : Monotone ν)
    (ρ : Measure α) (h : ∀ m, ν m ≤ ρ) : increasingMeasureLimit ν hν ≤ ρ := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [increasingMeasureLimit_apply ν hν hS]
  exact iSup_le fun m => h m S

 

lemma restrictionChain_monotone (ν : ℕ → Measure α) (W : ℕ → Set α)
    (hcompat : ∀ a b, a ≤ b → (ν b).restrict (W a) = ν a) : Monotone ν := by
  intro a b hab
  rw [←hcompat a b hab]
  exact Measure.restrict_le_self

 
theorem increasingMeasureLimit_restrict (ν : ℕ → Measure α) (W : ℕ → Set α)
    (hW : ∀ m, MeasurableSet (W m))
    (hcompat : ∀ a b, a ≤ b → (ν b).restrict (W a) = ν a) (m : ℕ) :
    (increasingMeasureLimit ν (restrictionChain_monotone ν W hcompat)).restrict (W m) = ν m := by
  let hν := restrictionChain_monotone ν W hcompat
  apply le_antisymm
  · apply Measure.le_iff.mpr
    intro S hS
    rw [Measure.restrict_apply hS,increasingMeasureLimit_apply ν hν (hS.inter (hW m))]
    apply iSup_le
    intro a
    by_cases ham : a ≤ m
    · exact (hν ham _) |>.trans (measure_mono inter_subset_left)
    · have hm : m ≤ a := le_of_not_ge ham
      have he := congrArg (fun ρ : Measure α => ρ S) (hcompat m a hm)
      simpa only [Measure.restrict_apply hS] using he.le
  · rw [←hcompat m m le_rfl]
    exact Measure.restrict_mono subset_rfl (le_increasingMeasureLimit ν hν m)

 
theorem measure_eq_of_restrictionChain (W : ℕ → Set α)
    (hW : Monotone W) (hcover : ⋃ m, W m = univ)
    (ν ρ : Measure α) (heq : ∀ m, ν.restrict (W m) = ρ.restrict (W m)) : ν = ρ := by
  ext S hS
  have he : S = ⋃ m, S ∩ W m := by rw [←inter_iUnion,hcover,inter_univ]
  rw [he,(show Monotone (fun m => S ∩ W m) from fun a b hab => inter_subset_inter_right S (hW hab)).measure_iUnion,
    (show Monotone (fun m => S ∩ W m) from fun a b hab => inter_subset_inter_right S (hW hab)).measure_iUnion]
  congr 1
  funext m
  simpa only [Measure.restrict_apply hS] using congrArg (fun ξ : Measure α => ξ S) (heq m)

 
theorem increasingMeasureLimit_locallyFinite [TopologicalSpace α]
    (ν : ℕ → Measure α) [∀ m, IsFiniteMeasure (ν m)] (W : ℕ → Set α)
    (hW : ∀ m, IsOpen (W m)) (hWm : ∀ m, MeasurableSet (W m))
    (hcover : ⋃ m, W m = univ)
    (hcompat : ∀ a b, a ≤ b → (ν b).restrict (W a) = ν a) :
    IsLocallyFiniteMeasure (increasingMeasureLimit ν (restrictionChain_monotone ν W hcompat)) := by
  constructor
  intro x
  have hx : x ∈ ⋃ m, W m := by rw [hcover]; trivial
  obtain ⟨m,hm⟩ := mem_iUnion.mp hx
  refine ⟨W m,(hW m).mem_nhds hm,?_⟩
  have H := congrArg (fun ρ : Measure α => ρ univ)
    (increasingMeasureLimit_restrict ν W hWm hcompat m)
  rw [Measure.restrict_apply MeasurableSet.univ,univ_inter] at H
  rw [H]
  exact measure_lt_top _ _

end PrimeDegreePackets


namespace PrimeDegreePackets.RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

theorem ae_exists_rootLeafMeasure (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∃ ν : Measure ℝ,
      IsLocallyFiniteMeasure ν ∧ ν A.time = 1 ∧
      ν.restrict A.time = A.conditionalKernel μ s ∧
      ∀ (m : ℕ) (B : RootBox hij k), B ∈ rootLongBoxFamily hij k R m →
        s ∈ B.transverse →
        ν.restrict (rootLeafWindow R m) =
          (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (rootLeafWindow R m) := by
  let C := rootLongBoxFamily hij k R
  have hCc (m : ℕ) : (C m).Countable := rootLongBoxFamily_countable hij k R m
  let (m : ℕ) : Countable (C m) := (hCc m).to_subtype
  have hT (m : ℕ) (B : C m) : B.val.time = rootLeafWindow R m :=
    rootLongBoxFamily_time hij k R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (rootLeafWindow_mono R (Nat.zero_le m))
  have hp : ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      ∀ (a b : ℕ) (B : C a) (D : C b), s ∈ B.val.transverse → s ∈ D.val.transverse →
        B.val.conditionalKernel μ s A.time ≠ 0 ∧ D.val.conditionalKernel μ s A.time ≠ 0 ∧
        (anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict (B.val.time ∩ D.val.time) =
          (anchorNormalize (D.val.conditionalKernel μ s) A.time).restrict (B.val.time ∩ D.val.time) := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro b
    apply ae_all_iff.mpr
    intro B
    apply ae_all_iff.mpr
    intro D
    exact base_overlap_anchorNormalize A B.val D.val (hinc a B) (hinc b D) μ
  have ha : ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      ∀ (m : ℕ) (B : C m), s ∈ B.val.transverse →
        B.val.conditionalKernel μ s A.time ≠ 0 ∧
        (anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict A.time =
          A.conditionalKernel μ s := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro B
    exact base_anchor_restrict A B.val (hinc m B) μ
  filter_upwards [A.ae_injective_root_slice_of_ae_free μ hfree,hp,ha] with s hs hp ha
  have hcover (m : ℕ) : ∃ B : C m, s ∈ B.val.transverse := by
    obtain ⟨B,hB,hsB⟩ := rootLongBoxFamily_covers hij k R m s hs
    exact ⟨⟨B,hB⟩,hsB⟩
  choose B hB using hcover
  let N (m : ℕ) : Measure ℝ :=
    (anchorNormalize ((B m).val.conditionalKernel μ s) A.time).restrict (rootLeafWindow R m)
  have hpos (m : ℕ) : (B m).val.conditionalKernel μ s A.time ≠ 0 := (ha m (B m) (hB m)).1
  let (m : ℕ) : IsFiniteMeasure (anchorNormalize ((B m).val.conditionalKernel μ s) A.time) :=
    anchorNormalize_finite _ _ (hpos m)
  let (m : ℕ) : IsFiniteMeasure (N m) := by dsimp [N]; infer_instance
  have hc : ∀ a b, a ≤ b → (N b).restrict (rootLeafWindow R a) = N a := by
    intro a b hab
    have H := (hp a b (B a) (B b) (hB a) (hB b)).2.2
    rw [hT a (B a),hT b (B b),inter_eq_left.mpr (rootLeafWindow_mono R hab)] at H
    dsimp [N]
    rw [Measure.restrict_restrict (rootLeafWindow_open R a).measurableSet,
      inter_eq_left.mpr (rootLeafWindow_mono R hab)]
    exact H.symm
  let ν := increasingMeasureLimit N (restrictionChain_monotone N (rootLeafWindow R) hc)
  have hν (m : ℕ) : ν.restrict (rootLeafWindow R m) = N m :=
    increasingMeasureLimit_restrict N (rootLeafWindow R)
      (fun m => (rootLeafWindow_open R m).measurableSet) hc m
  have hνA : ν.restrict A.time = A.conditionalKernel μ s := by
    have H := congrArg (fun ξ : Measure ℝ => ξ.restrict A.time) (hν 0)
    dsimp [N] at H
    rw [Measure.restrict_restrict A.time_open.measurableSet,inter_eq_left.mpr hAR,
      Measure.restrict_restrict A.time_open.measurableSet,inter_eq_left.mpr hAR] at H
    exact H.trans (ha 0 (B 0) (hB 0)).2
  refine ⟨ν,increasingMeasureLimit_locallyFinite N (rootLeafWindow R)
    (rootLeafWindow_open R) (fun m => (rootLeafWindow_open R m).measurableSet)
    (rootLeafWindow_cover R) hc,?_,hνA,?_⟩
  · have H := congrArg (fun ξ : Measure ℝ => ξ univ) hνA
    simpa only [Measure.restrict_apply MeasurableSet.univ,univ_inter,measure_univ] using H
  · intro m D hD hsD
    let D' : C m := ⟨D,hD⟩
    have H := (hp m m (B m) D' (hB m) hsD).2.2
    rw [hT m (B m),hT m D',inter_self] at H
    exact (hν m).trans H

 

theorem rootLeafMeasure_unique (A : RootBox hij k) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (s : RootSlice i j k)
    (hs : Function.Injective (fun t : ℝ => rootQuotientParametrization hij (s,t)))
    (ν ρ : Measure ℝ)
    (hν : ∀ (m : ℕ) (B : RootBox hij k), B ∈ rootLongBoxFamily hij k R m →
      s ∈ B.transverse → ν.restrict (rootLeafWindow R m) =
        (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (rootLeafWindow R m))
    (hρ : ∀ (m : ℕ) (B : RootBox hij k), B ∈ rootLongBoxFamily hij k R m →
      s ∈ B.transverse → ρ.restrict (rootLeafWindow R m) =
        (anchorNormalize (B.conditionalKernel μ s) A.time).restrict (rootLeafWindow R m)) : ν = ρ := by
  apply measure_eq_of_restrictionChain (rootLeafWindow R) (rootLeafWindow_mono R)
    (rootLeafWindow_cover R)
  intro m
  obtain ⟨B,hB,hsB⟩ := rootLongBoxFamily_covers hij k R m s hs
  exact (hν m B hB hsB).trans (hρ m B hB hsB).symm

end PrimeDegreePackets.RootBox
end
end

end OAI
