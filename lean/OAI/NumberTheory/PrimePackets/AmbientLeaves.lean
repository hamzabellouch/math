import Mathlib
import OAI.NumberTheory.PrimePackets.IntrinsicLeaves

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
namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

lemma ae_coordinate_of_ambient (A : RootBox hij k) (μ : Measure (X n))
    {P : X n → Prop} (hp : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ z ∂A.coordinateMeasure μ, P (rootQuotientParametrization hij z) := by
  have H : ∀ᵐ x ∂μ.restrict A.range, P x := ae_restrict_of_ae hp
  rw [←A.map_coordinateMeasure μ] at H
  exact ae_of_ae_map (rootQuotientParametrization_localHomeomorph hij).continuous.measurable.aemeasurable H

 

theorem ae_leafMeasure_of_ambient (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    {P : X n → Prop} (hp : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ᵐ t ∂A.leafMeasure R μ s,
      P (rootQuotientParametrization hij (s,t)) := by
  let C := rootLongBoxFamily hij k R
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k R m).to_subtype
  have hT (m : ℕ) (B : C m) : B.val.time = rootLeafWindow R m :=
    rootLongBoxFamily_time hij k R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (rootLeafWindow_mono R (Nat.zero_le m))
  have HD (D : RootBox hij k) : ∀ᵐ s ∂(D.coordinateMeasure μ).fst,
      ∀ᵐ t ∂D.conditionalKernel μ s, P (rootQuotientParametrization hij (s,t)) := by
    have H : ∀ᵐ z ∂(D.coordinateMeasure μ).fst ⊗ₘ D.conditionalKernel μ,
        P (rootQuotientParametrization hij z) := by
      simpa only [conditionalKernel,Measure.disintegrate] using D.ae_coordinate_of_ambient μ hp
    exact Measure.ae_ae_of_ae_compProd H
  have H (m : ℕ) (B : C m) : ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      s ∈ B.val.transverse → ∀ᵐ t ∂(A.leafMeasure R μ s).restrict (rootLeafWindow R m),
        P (rootQuotientParametrization hij (s,t)) := by
    filter_upwards [A.ae_leafMeasure_restrict R hAR μ hfree B.val (hinc m B),
      A.base_ae_of_ae B.val (hinc m B) μ (HD B.val)] with s hs hd hsb
    have hh := ae_restrict_of_ae (s := B.val.time) (Measure.ae_smul_measure (hd hsb)
      ((B.val.conditionalKernel μ s A.time)⁻¹))
    change ∀ᵐ t ∂(anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict B.val.time,
      P (rootQuotientParametrization hij (s,t)) at hh
    rw [←(hs hsb).2,hT m B] at hh
    exact hh
  have Hall := ae_all_iff.mpr (fun m => ae_all_iff.mpr (H m))
  filter_upwards [Hall,A.ae_injective_root_slice_of_ae_free μ hfree] with s hs hi
  have HW (m : ℕ) : ∀ᵐ t ∂(A.leafMeasure R μ s).restrict (rootLeafWindow R m),
      P (rootQuotientParametrization hij (s,t)) := by
    obtain ⟨B,hBC,hsB⟩ := rootLongBoxFamily_covers hij k R m s hi
    exact hs m ⟨B,hBC⟩ hsB
  have HH := (ae_restrict_iUnion_iff (μ := A.leafMeasure R μ s) (rootLeafWindow R) _).mpr HW
  simpa only [rootLeafWindow_cover,Measure.restrict_univ] using HH

lemma ae_basedLeaf_of_ambient (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    {P : X n → Prop} (hp : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ z ∂A.coordinateMeasure μ, ∀ᵐ t ∂A.basedLeaf R μ z,
      P (rightAction (rootQuotientParametrization hij z)
        (Matrix.SpecialLinearGroup.transvection hij t)) := by
  have H := ae_of_ae_map measurable_fst.aemeasurable (A.ae_leafMeasure_of_ambient R hAR μ hfree hp)
  filter_upwards [H] with z hz
  apply Measure.ae_smul_measure
  apply (Homeomorph.subRight z.2).measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hz] with t ht
  change P (rightAction (rootQuotientParametrization hij z)
    (Matrix.SpecialLinearGroup.transvection hij (t-z.2)))
  rw [←rootQuotientParametrization_add]
  simpa only [←add_sub_assoc,add_sub_cancel_left] using ht

end RootBox

 

theorem ae_intrinsicRootLeaf_of_ambient {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    {P : X n → Prop} (hp : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ x ∂μ, ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
      P (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H (B : boundedRootAtlas hij) : ∀ᵐ x ∂μ.restrict B.val.box.range,
      ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
        P (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) := by
    apply B.val.box.ae_of_coordinate μ
    filter_upwards [B.val.box.ae_intrinsicRootLeaf_coordinates B.val.radius B.val.time_bound μ hfree,
      B.val.box.ae_basedLeaf_of_ambient B.val.radius B.val.time_bound μ hfree hp] with z he hz
    rwa [he]
  have HH := (ae_restrict_iUnion_iff (μ := μ) (fun B : boundedRootAtlas hij => B.val.box.range) _).mpr H
  simpa only [boundedRootAtlas_iUnion,Measure.restrict_univ] using HH

end PrimeDegreePackets


namespace PrimeDegreePackets
namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

theorem ae_leafMeasure_intrinsic (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst, ∀ᵐ t ∂A.leafMeasure R μ s,
      intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s,t)) =
        basedRealMeasure (A.leafMeasure R μ s) t := by
  let C := rootLongBoxFamily hij k R
  let (m : ℕ) : Countable (C m) := (rootLongBoxFamily_countable hij k R m).to_subtype
  have hT (m : ℕ) (B : C m) : B.val.time = rootLeafWindow R m :=
    rootLongBoxFamily_time hij k R m B.val B.prop
  have hinc (m : ℕ) (B : C m) : A.time ⊆ B.val.time := by
    rw [hT m B]
    exact hAR.trans (rootLeafWindow_mono R (Nat.zero_le m))
  have hbound (m : ℕ) (B : C m) : B.val.time ⊆ rootLeafWindow (R+m) 0 := by
    rw [hT m B]
    simp only [rootLeafWindow,Nat.cast_zero,add_zero,subset_refl]
  have HD (m : ℕ) (B : C m) : ∀ᵐ s ∂(B.val.coordinateMeasure μ).fst,
      ∀ᵐ t ∂B.val.conditionalKernel μ s,
      intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s,t)) =
        basedRealMeasure (B.val.leafMeasure (R+m) μ s) t := by
    have H : ∀ᵐ z ∂(B.val.coordinateMeasure μ).fst ⊗ₘ B.val.conditionalKernel μ,
        intrinsicRootLeaf hij μ (rootQuotientParametrization hij z) = B.val.basedLeaf (R+m) μ z := by
      simpa only [conditionalKernel,Measure.disintegrate] using
        B.val.ae_intrinsicRootLeaf_coordinates (R+m) (hbound m B) μ hfree
    exact Measure.ae_ae_of_ae_compProd H
  have H (m : ℕ) (B : C m) : ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      s ∈ B.val.transverse → ∀ᵐ t ∂(A.leafMeasure R μ s).restrict (rootLeafWindow R m),
      intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s,t)) =
        basedRealMeasure (A.leafMeasure R μ s) t := by
    filter_upwards [A.ae_leafMeasure_restrict R hAR μ hfree B.val (hinc m B),
      A.base_ae_of_ae B.val (hinc m B) μ (HD m B),
      A.ae_leafMeasure_change_anchor B.val R (R+m) hAR (hbound m B) (hinc m B) μ hfree,
      A.ae_change_anchor_mass B.val R (R+m) hAR (hbound m B) (hinc m B) μ hfree]
      with s hs hd he hm hsb
    have he' (t : ℝ) : basedRealMeasure (A.leafMeasure R μ s) t =
        basedRealMeasure (B.val.leafMeasure (R+m) μ s) t := by
      rw [he hsb]
      exact basedRealMeasure_smul _ _ (ENNReal.inv_ne_zero.mpr (hm hsb).2)
        (ENNReal.inv_ne_top.mpr (hm hsb).1) _
    have hh := ae_restrict_of_ae (s := B.val.time) (Measure.ae_smul_measure (hd hsb)
      ((B.val.conditionalKernel μ s A.time)⁻¹))
    change ∀ᵐ t ∂(anchorNormalize (B.val.conditionalKernel μ s) A.time).restrict B.val.time,
      intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s,t)) =
        basedRealMeasure (B.val.leafMeasure (R+m) μ s) t at hh
    rw [←(hs hsb).2,hT m B] at hh
    simpa only [he'] using hh
  have Hall := ae_all_iff.mpr (fun m => ae_all_iff.mpr (H m))
  filter_upwards [Hall,A.ae_injective_root_slice_of_ae_free μ hfree] with s hs hi
  have HW (m : ℕ) : ∀ᵐ t ∂(A.leafMeasure R μ s).restrict (rootLeafWindow R m),
      intrinsicRootLeaf hij μ (rootQuotientParametrization hij (s,t)) =
        basedRealMeasure (A.leafMeasure R μ s) t := by
    obtain ⟨B,hBC,hsB⟩ := rootLongBoxFamily_covers hij k R m s hi
    exact hs m ⟨B,hBC⟩ hsB
  have HH := (ae_restrict_iUnion_iff (μ := A.leafMeasure R μ s) (rootLeafWindow R) _).mpr HW
  simpa only [rootLeafWindow_cover,Measure.restrict_univ] using HH

lemma ae_basedLeaf_rebase (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ z ∂A.coordinateMeasure μ, ∀ᵐ t ∂A.basedLeaf R μ z,
      intrinsicRootLeaf hij μ (rightAction (rootQuotientParametrization hij z)
        (Matrix.SpecialLinearGroup.transvection hij t)) = basedRealMeasure (A.basedLeaf R μ z) t := by
  have H := ae_of_ae_map measurable_fst.aemeasurable (A.ae_leafMeasure_intrinsic R hAR μ hfree)
  have HL := ae_of_ae_map measurable_fst.aemeasurable
    ((A.ae_leafMeasure_spec R hAR μ hfree).mono fun _ h => h.1)
  filter_upwards [H,HL,A.ae_leafMeasure_ball_pos R hAR μ hfree] with z hz hlf hp
  let : IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) := hlf
  apply Measure.ae_smul_measure
  apply (Homeomorph.subRight z.2).measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hz] with t ht
  change intrinsicRootLeaf hij μ (rightAction (rootQuotientParametrization hij z)
    (Matrix.SpecialLinearGroup.transvection hij (t-z.2))) =
      basedRealMeasure (basedRealMeasure (A.leafMeasure R μ z.1) z.2) (t-z.2)
  rw [←rootQuotientParametrization_add,basedRealMeasure_rebase _ _ _ (hp 1 zero_lt_one),←add_sub_assoc,add_sub_cancel_left]
  exact ht

end RootBox

 

theorem ae_intrinsicRootLeaf_rebase {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ x ∂μ, ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
      intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
        basedRealMeasure (intrinsicRootLeaf hij μ x) t := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H (B : boundedRootAtlas hij) : ∀ᵐ x ∂μ.restrict B.val.box.range,
      ∀ᵐ t ∂intrinsicRootLeaf hij μ x,
        intrinsicRootLeaf hij μ (rightAction x (Matrix.SpecialLinearGroup.transvection hij t)) =
          basedRealMeasure (intrinsicRootLeaf hij μ x) t := by
    apply B.val.box.ae_of_coordinate μ
    filter_upwards [B.val.box.ae_intrinsicRootLeaf_coordinates B.val.radius B.val.time_bound μ hfree,
      B.val.box.ae_basedLeaf_rebase B.val.radius B.val.time_bound μ hfree] with z he hz
    rwa [he]
  have HH := (ae_restrict_iUnion_iff (μ := μ) (fun B : boundedRootAtlas hij => B.val.box.range) _).mpr H
  simpa only [boundedRootAtlas_iUnion,Measure.restrict_univ] using HH

end PrimeDegreePackets

open scoped Topology ENNReal
namespace PrimeDegreePackets

lemma centerRealMeasure_singleton (ν : Measure ℝ) (t u : ℝ) :
    centerRealMeasure ν t {u} = ν {u+t} := by
  rw [centerRealMeasure,Measure.map_apply (Homeomorph.subRight t).measurable (measurableSet_singleton u)]
  congr 1
  ext v
  simp only [Set.mem_preimage,mem_singleton_iff,Homeomorph.coe_subRight]
  exact sub_eq_iff_eq_add

lemma basedRealMeasure_atom_ne_zero (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (t : ℝ) (ht : ν {t} ≠ 0) : basedRealMeasure ν t {0} ≠ 0 := by
  change (centerRealMeasure ν t (Metric.ball 0 1))⁻¹ * centerRealMeasure ν t {0} ≠ 0
  rw [centerRealMeasure_ball,centerRealMeasure_singleton,zero_add]
  exact mul_ne_zero (ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne) ht

lemma ae_property_at_atom {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {P : α → Prop} (hP : ∀ᵐ x ∂ν, P x) {t : α} (ht : ν {t} ≠ 0) : P t := by
  by_contra h
  exact ht (measure_mono_null (singleton_subset_iff.mpr h) (ae_iff.mp hP))

 

theorem realLeaf_nullSingleton_or_dirac (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (hunit : ν (Metric.ball 0 1) = 1)
    (hsupport : ∀ r : ℝ, 0 < r → 0 < ν (Metric.ball 0 r))
    (hbase : ∀ᵐ t ∂ν, basedRealMeasure ν t {0} ≠ 0 →
      basedRealMeasure ν t = Measure.dirac 0) :
    NullSingletonClass ν ∨ ν = Measure.dirac 0 := by
  classical
  by_cases h : ∀ t : ℝ, ν {t} = 0
  · exact Or.inl ⟨h⟩
  · right
    obtain ⟨t,ht⟩ := not_forall.mp h
    have hb := (ae_property_at_atom ν hbase ht) (basedRealMeasure_atom_ne_zero ν t ht)
    have hball : ν (Metric.ball t 1) ≠ 0 :=
      (lt_of_lt_of_le (pos_iff_ne_zero.mpr ht)
        (measure_mono (singleton_subset_iff.mpr (Metric.mem_ball_self zero_lt_one)))).ne'
    have hcomp : centerRealMeasure ν t ({0}ᶜ) = ν ({t}ᶜ) := by
      rw [centerRealMeasure,Measure.map_apply (Homeomorph.subRight t).measurable
        (measurableSet_singleton 0).compl]
      congr 1
      ext v
      simp [sub_eq_zero]
    have hh := congrArg (fun ρ : Measure ℝ => ρ ({0}ᶜ)) hb
    change (centerRealMeasure ν t (Metric.ball 0 1))⁻¹ * centerRealMeasure ν t ({0}ᶜ) = _ at hh
    rw [centerRealMeasure_ball,hcomp] at hh
    have hc : ν ({t}ᶜ) = 0 := by
      have hz : (ν (Metric.ball t 1))⁻¹ * ν ({t}ᶜ) = 0 := by simpa using hh
      exact (mul_eq_zero.mp hz).resolve_left (ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne)
    have ht0 : t = 0 := by
      by_contra hne
      have hsub : Metric.ball (0:ℝ) (|t|/2) ⊆ {t}ᶜ := by
        intro v hv he
        have hvt : v = t := he
        subst v
        have hav := Metric.mem_ball.mp hv
        rw [Real.dist_eq,sub_zero] at hav
        linarith [abs_nonneg t]
      exact (hsupport _ (half_pos (abs_pos.mpr hne))).ne' (measure_mono_null hsub hc)
    subst t
    have hdir : ν = ν {0} • Measure.dirac 0 := by
      have ha : ∀ᵐ t ∂ν, t ∈ ({0} : Finset ℝ) := by
        have ha' : ∀ᵐ x ∂ν, x ∈ ({0} : Set ℝ) := mem_ae_iff.mpr hc
        filter_upwards [ha'] with x hx
        simpa only [mem_singleton_iff,Finset.mem_singleton] using hx
      simpa using Measure.ae_mem_finset_iff.mp ha
    have hmass : ν {0} = 1 := by
      rw [hdir,Measure.smul_apply] at hunit
      simpa using hunit
    rwa [hmass,one_smul] at hdir

end PrimeDegreePackets

open scoped Matrix Topology ENNReal ProbabilityTheory
namespace PrimeDegreePackets

lemma basedRealMeasure_ball_pos (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (t r : ℝ) (hr : 0 < ν (Metric.ball t r)) :
    0 < basedRealMeasure ν t (Metric.ball 0 r) := by
  change 0 < (centerRealMeasure ν t (Metric.ball 0 1))⁻¹ * centerRealMeasure ν t (Metric.ball 0 r)
  rw [centerRealMeasure_ball,centerRealMeasure_ball]
  exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne) hr.ne'

 

theorem ae_intrinsicRootLeaf_ball_pos {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0) :
    ∀ᵐ x ∂μ, ∀ r : ℝ, 0 < r → 0 < intrinsicRootLeaf hij μ x (Metric.ball 0 r) := by
  let : Countable (boundedRootAtlas hij) := (boundedRootAtlas_countable hij).to_subtype
  have H (B : boundedRootAtlas hij) : ∀ᵐ x ∂μ.restrict B.val.box.range,
      ∀ r : ℝ, 0 < r → 0 < intrinsicRootLeaf hij μ x (Metric.ball 0 r) := by
    apply B.val.box.ae_of_coordinate μ
    have Hlf := ae_of_ae_map measurable_fst.aemeasurable
      ((B.val.box.ae_leafMeasure_spec B.val.radius B.val.time_bound μ hfree).mono fun _ h => h.1)
    filter_upwards [B.val.box.ae_intrinsicRootLeaf_coordinates B.val.radius B.val.time_bound μ hfree,
      B.val.box.ae_leafMeasure_ball_pos B.val.radius B.val.time_bound μ hfree,Hlf] with z he hp hf
    let : IsLocallyFiniteMeasure (B.val.box.leafMeasure B.val.radius μ z.1) := hf
    intro r hr
    rw [he]
    exact basedRealMeasure_ball_pos _ _ _ (hp r hr)
  have HH := (ae_restrict_iUnion_iff (μ := μ) (fun B : boundedRootAtlas hij => B.val.box.range) _).mpr H
  simpa only [boundedRootAtlas_iUnion,Measure.restrict_univ] using HH

 

theorem ae_intrinsicRootLeaf_nullSingleton_or_dirac (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, NullSingletonClass (intrinsicRootLeaf hij μ x) ∨
      intrinsicRootLeaf hij μ x = Measure.dirac 0 := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  have HA := ae_intrinsicRootLeaf_of_ambient hij μ hfree
    (ae_intrinsicRootLeaf_atom_dirac d hij μ hA)
  filter_upwards [HA,ae_intrinsicRootLeaf_rebase hij μ hfree,
    ae_intrinsicRootLeaf_spec hij μ hfree,ae_intrinsicRootLeaf_ball_pos hij μ hfree] with x ha hr hs hp
  let : IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) := hs.1
  apply realLeaf_nullSingleton_or_dirac _ hs.2 hp
  filter_upwards [ha,hr] with t ht he
  rwa [he] at ht

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma translation_invariant_of_based (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    (t : ℝ) (ht : 0 < ν (Metric.ball t 1))
    (hinv : ∀ a : ℝ, (basedRealMeasure ν t).map (fun u => u+a) = basedRealMeasure ν t) :
    ∀ a : ℝ, ν.map (fun u => u+a) = ν := by
  have hnorm : centerRealMeasure ν t = ν (Metric.ball t 1) • basedRealMeasure ν t := by
    unfold basedRealMeasure anchorNormalize
    rw [centerRealMeasure_ball,smul_smul,ENNReal.mul_inv_cancel ht.ne' measure_ball_lt_top.ne,one_smul]
  intro a
  apply (Homeomorph.subRight t).measurableEmbedding.map_injective
  change centerRealMeasure (ν.map (fun u => u+a)) t = centerRealMeasure ν t
  have hcomm : centerRealMeasure (ν.map (fun u => u+a)) t =
      (centerRealMeasure ν t).map (fun u => u+a) := by
    unfold centerRealMeasure
    rw [Measure.map_map (Homeomorph.subRight t).measurable (by fun_prop),
      Measure.map_map (by fun_prop) (Homeomorph.subRight t).measurable]
    congr 1
    funext u
    change u+a-t=(u-t)+a
    ring
  rw [hcomm,hnorm,Measure.map_smul _ (f := fun value : ℝ => value+a) (by fun_prop),hinv a]

namespace RootBox
variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

 

theorem hasHaarConditionals_of_intrinsic (A : RootBox hij k) (R : ℝ)
    (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0)
    (hinv : ∀ᵐ x ∂μ, ∀ a : ℝ,
      (intrinsicRootLeaf hij μ x).map (fun t => t+a) = intrinsicRootLeaf hij μ x) :
    A.HasHaarConditionals μ := by
  apply A.hasHaarConditionals_of_invariant_leafMeasure R hAR μ hfree
  have H : ∀ᵐ z ∂A.coordinateMeasure μ, ∀ a : ℝ,
      (A.leafMeasure R μ z.1).map (fun t => t+a) = A.leafMeasure R μ z.1 := by
    have Hlf := ae_of_ae_map measurable_fst.aemeasurable
      ((A.ae_leafMeasure_spec R hAR μ hfree).mono fun _ h => h.1)
    filter_upwards [A.ae_coordinate_of_ambient μ hinv,
      A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree,
      A.ae_leafMeasure_ball_pos R hAR μ hfree,Hlf] with z hi he hp hf
    let : IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) := hf
    apply translation_invariant_of_based _ z.2 (hp 1 zero_lt_one)
    rwa [he] at hi
  have HC : ∀ᵐ z ∂(A.coordinateMeasure μ).fst ⊗ₘ A.conditionalKernel μ, ∀ a : ℝ,
      (A.leafMeasure R μ z.1).map (fun t => t+a) = A.leafMeasure R μ z.1 := by
    simpa only [conditionalKernel,Measure.disintegrate] using H
  filter_upwards [Measure.ae_ae_of_ae_compProd HC] with s hs
  obtain ⟨t,ht⟩ := hs.exists
  exact ht

end RootBox

 

theorem root_invariant_of_intrinsic (d : ℕ) {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hinv : ∀ᵐ x ∂μ, ∀ a : ℝ,
      (intrinsicRootLeaf hij μ x).map (fun t => t+a) = intrinsicRootLeaf hij μ x)
    (a : ℝ) : μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ := by
  have hfree : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  apply (homeomorph_measurePreserving_of_ae_local μ
    (rightActionHomeomorph (Matrix.SpecialLinearGroup.transvection hij a)) ?_).map_eq
  filter_upwards [ae_rootBox_arbitrary_length d μ hA] with x hx
  obtain ⟨k,B,s,t,hs,hI,hx⟩ := hx i j hij (|a|+1)
  let W := Ioo (t-(|a|+1)) (t+(|a|+1))
  let C := B.shrink B.transverse W B.transverse_open isOpen_Ioo subset_rfl (Ioo_subset_Icc_self.trans hI)
  have hbound : C.time ⊆ rootLeafWindow (|t|+|a|+2) 0 := by
    intro u hu
    change u ∈ W at hu
    change -((|t|+|a|+2)+(0:ℕ)) < u ∧ u < (|t|+|a|+2)+(0:ℕ)
    dsimp [W] at hu
    constructor <;> push_cast <;> linarith [hu.1,hu.2,neg_abs_le t,le_abs_self t]
  have ht : t ∈ C.time := by
    change t ∈ W
    dsimp [W]
    constructor <;> linarith [abs_nonneg a]
  have hta : t+a ∈ C.time := by
    change t+a ∈ W
    dsimp [W]
    constructor <;> linarith [neg_abs_le a,le_abs_self a]
  change ∃ U : Set (X (d+1)), IsOpen U ∧ x ∈ U ∧
    ∀ S : Set (X (d+1)), MeasurableSet S → S ⊆ U →
      μ ((fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) '' S) = μ S
  simpa only [hx] using C.local_mass_translate_of_endpoints μ
    (C.hasHaarConditionals_of_intrinsic _ hbound μ hfree hinv) a s t hs ht hta

 

theorem measure_eq_haar_of_intrinsic_roots (d : ℕ) (hd : 1 ≤ d)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (m : Measure (X (d+1))) (hm : IsHaarProbability m)
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (hinv : ∀ (i j : Fin (d+1)) (hij : i ≠ j), ∀ᵐ x ∂μ, ∀ a : ℝ,
      (intrinsicRootLeaf hij μ x).map (fun t => t+a) = intrinsicRootLeaf hij μ x) : μ = m := by
  apply isHaarProbability_unique ⟨inferInstance,?_⟩ hm
  apply right_invariant_of_all_roots (by omega)
  intro i j hij a
  exact root_invariant_of_intrinsic d hij μ hA (hinv i j hij) a

end PrimeDegreePackets
end
end

end OAI
