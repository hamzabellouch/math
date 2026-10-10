import Mathlib
import OAI.Geometry.BallPacking.Fredholm.NonlinearReduction

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {D : X →L[ℝ] Y} (pkg : D.FredholmPackage)
local instance sprK : FiniteDimensional ℝ pkg.decDom.X₀ := pkg.decDom.finite_X₀
local instance sprC : FiniteDimensional ℝ pkg.decCodom.X₀ := pkg.decCodom.finite_X₀
local instance sprX : CompleteSpace pkg.decDom.X₁ := pkg.decDom.isTopCompl.isClosed.completeSpace_coe
local instance sprY : CompleteSpace pkg.decCodom.X₁ := pkg.decCodom.isTopCompl.isClosed.completeSpace_coe

omit [CompleteSpace Y] in
lemma surjective_package_coker_subsingleton [CompleteSpace Y] (hD : Surjective D) : Subsingleton pkg.decCodom.X₀ := by
  have hc (c : pkg.decCodom.X₀) : c=0 := by
    obtain ⟨x,hx⟩ := hD ((codCoords pkg).symm (0,c))
    have hh := congrArg (fun y => ((codCoords pkg) y).2) hx
    rw [fredholm_original_coords,(codCoords pkg).apply_symm_apply] at hh
    exact hh.symm
  exact ⟨fun x y => (hc x).trans (hc y).symm⟩

variable {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F) {t : ℝ} {x : X}
  (hD : HasFDerivAt (fun y => F (t,y)) D x)

lemma parametricSolution_kernel_coordinate (v : ℝ × pkg.decDom.X₀) :
    ((domCoords pkg) (parametricSolution pkg hF hD v)).2=v.2 := by
  exact congrArg Prod.snd ((domCoords pkg).apply_symm_apply _)

include hD in
lemma parametricSolution_graph_injective :
    Injective (fun v : ℝ × pkg.decDom.X₀ => (v.1,parametricSolution pkg hF hD v)) := by
  intro v w hw
  have ht : v.1=w.1 := congrArg (Prod.fst : ℝ × X → ℝ) hw
  have hx := congrArg (fun z : ℝ × X => ((domCoords pkg) z.2).2) hw
  rw [parametricSolution_kernel_coordinate,parametricSolution_kernel_coordinate] at hx
  exact Prod.ext ht hx

include hD in
lemma surjective_parametricSolution_zero (hs : Surjective D) (hz : F (t,x)=0) :
    ∀ᶠ v in 𝓝 (t,((domCoords pkg) x).2),F (v.1,parametricSolution pkg hF hD v)=0 := by
  let := surjective_package_coker_subsingleton pkg hs
  filter_upwards [parametricSolution_zero_iff pkg hF hD hz] with v hv
  exact hv.mpr (Subsingleton.elim _ _)

include pkg hF hD in

theorem surjective_zero_chart (hs : Surjective D) (hz : F (t,x)=0) :
    ∃ K : Submodule ℝ X,FiniteDimensional ℝ K ∧
      ∃ P : X →L[ℝ] K,∃ ψ : ℝ × K → X,
        ψ (t,P x)=x ∧
        ContDiffAt ℝ ∞ ψ (t,P x) ∧
        (∀ v,P (ψ v)=v.2) ∧
        (∀ᶠ v in 𝓝 (t,P x),F (v.1,ψ v)=0) ∧
        (∀ᶠ v in 𝓝 (t,x),F v=0 → ψ (v.1,P v.2)=v.2) := by
  let P : X →L[ℝ] pkg.decDom.X₀ :=
    (ContinuousLinearMap.snd ℝ pkg.decDom.X₁ pkg.decDom.X₀).comp (domCoords pkg).toContinuousLinearMap
  exact ⟨pkg.decDom.X₀,inferInstance,P,parametricSolution pkg hF hD,
    parametricSolution_base pkg hF hD,parametricSolution_smooth pkg hF hD,
    parametricSolution_kernel_coordinate pkg hF hD,
    surjective_parametricSolution_zero pkg hF hD hs hz,parametric_zero_is_solution pkg hF hD hz⟩


end
section
open scoped Topology
open Set Function
open HolderCompletion
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {D : X →L[ℝ] Y} (pkg : D.FredholmPackage)
  (E : Submodule ℝ Y) [FiniteDimensional ℝ E]
local instance akdK : FiniteDimensional ℝ pkg.decDom.X₀ := pkg.decDom.finite_X₀
local instance akdC : FiniteDimensional ℝ pkg.decCodom.X₀ := pkg.decCodom.finite_X₀

def augmentedCokerMap : E →L[ℝ] pkg.decCodom.X₀ :=
  (ContinuousLinearMap.snd ℝ pkg.decCodom.X₁ pkg.decCodom.X₀).comp
    ((codCoords pkg).toContinuousLinearMap.comp E.subtypeL)

omit [CompleteSpace Y] [FiniteDimensional ℝ E] in
lemma augmented_kernel_coker_zero [CompleteSpace Y] [FiniteDimensional ℝ E]
    (v : (D.coprod E.subtypeL).ker) :
    augmentedCokerMap pkg E v.val.2=0 := by
  have hv : D v.val.1+(v.val.2:Y)=0 := v.property
  have hh := congrArg (fun y => ((codCoords pkg) y).2) hv
  change ((codCoords pkg) (v.val.2:Y)).2=0
  simpa only [map_add,fredholm_original_coords,Prod.snd_add,zero_add,map_zero,Prod.snd_zero] using hh

omit [CompleteSpace Y] [FiniteDimensional ℝ E] in
lemma augmented_kernel_first_coordinate [CompleteSpace Y] [FiniteDimensional ℝ E]
    (v : (D.coprod E.subtypeL).ker) :
    ((domCoords pkg) v.val.1).1= -pkg.equiv.symm ((codCoords pkg) (v.val.2:Y)).1 := by
  have hv : D v.val.1+(v.val.2:Y)=0 := v.property
  have hh := congrArg (fun y => ((codCoords pkg) y).1) hv
  simp only [map_add,fredholm_original_coords,Prod.fst_add,map_zero,Prod.fst_zero] at hh
  apply pkg.equiv.injective
  rw [map_neg,pkg.equiv.apply_symm_apply]
  exact eq_neg_of_add_eq_zero_left hh

def augmentedKernelRead : (D.coprod E.subtypeL).ker →ₗ[ℝ]
    pkg.decDom.X₀ × (augmentedCokerMap pkg E).ker where
  toFun v := (((domCoords pkg) v.val.1).2,⟨v.val.2,augmented_kernel_coker_zero pkg E v⟩)
  map_add' v w := by
    apply Prod.ext
    · exact congrArg Prod.snd ((domCoords pkg).map_add v.val.1 w.val.1)
    · rfl
  map_smul' a v := by
    apply Prod.ext
    · exact congrArg Prod.snd ((domCoords pkg).map_smul a v.val.1)
    · rfl

lemma augmentedKernelRead_injective : Injective (augmentedKernelRead pkg E) := by
  intro v w he
  have hk : ((domCoords pkg) v.val.1).2=((domCoords pkg) w.val.1).2 :=
    congrArg (Prod.fst : pkg.decDom.X₀ × (augmentedCokerMap pkg E).ker → pkg.decDom.X₀) he
  have hee : v.val.2=w.val.2 := congrArg (fun z : pkg.decDom.X₀ × (augmentedCokerMap pkg E).ker => z.2.val) he
  apply Subtype.ext
  apply Prod.ext _ hee
  apply (domCoords pkg).injective
  apply Prod.ext _ hk
  rw [augmented_kernel_first_coordinate,augmented_kernel_first_coordinate,hee]

lemma augmentedKernelRead_surjective : Surjective (augmentedKernelRead pkg E) := by
  rintro ⟨k,e⟩
  let x := (domCoords pkg).symm (-pkg.equiv.symm ((codCoords pkg) (e.val:Y)).1,k)
  have hxe : D x+(e.val:Y)=0 := by
    apply (codCoords pkg).injective
    rw [map_add,map_zero,fredholm_original_coords]
    change (pkg.equiv ((domCoords pkg) ((domCoords pkg).symm _)).1,0)+(codCoords pkg) (e.val:Y)=0
    rw [(domCoords pkg).apply_symm_apply]
    apply Prod.ext
    · change pkg.equiv (-pkg.equiv.symm ((codCoords pkg) (e.val:Y)).1)+((codCoords pkg) (e.val:Y)).1=0
      rw [map_neg,pkg.equiv.apply_symm_apply,neg_add_cancel]
    · change 0+((codCoords pkg) (e.val:Y)).2=0
      exact (zero_add _).trans e.property
  refine ⟨⟨(x,e.val),hxe⟩,?_⟩
  apply Prod.ext
  · change ((domCoords pkg) ((domCoords pkg).symm _)).2=k
    rw [(domCoords pkg).apply_symm_apply]
  · rfl

omit [CompleteSpace Y] [FiniteDimensional ℝ E] in
lemma augmentedCokerMap_surjective [CompleteSpace Y] [FiniteDimensional ℝ E]
    (hs : Surjective (D.coprod E.subtypeL)) :
    Surjective (augmentedCokerMap pkg E) := by
  intro c
  obtain ⟨⟨x,e⟩,he⟩ := hs ((codCoords pkg).symm (0,c))
  refine ⟨e,?_⟩
  have hh := congrArg (fun y => ((codCoords pkg) y).2) he
  change ((codCoords pkg) (D x+(e:Y))).2=((codCoords pkg) ((codCoords pkg).symm (0,c))).2 at hh
  change ((codCoords pkg) (e:Y)).2=c
  simpa only [map_add,fredholm_original_coords,Prod.snd_add,zero_add,
    (codCoords pkg).apply_symm_apply] using hh

include pkg in
lemma augmentedKernel_finrank (hD : IsIndexZeroFredholm D)
    (hs : Surjective (D.coprod E.subtypeL)) :
    Module.finrank ℝ (D.coprod E.subtypeL).ker=Module.finrank ℝ E := by
  let L := LinearEquiv.ofBijective (augmentedKernelRead pkg E)
    ⟨augmentedKernelRead_injective pkg E,augmentedKernelRead_surjective pkg E⟩
  have hB := augmentedCokerMap_surjective pkg E hs
  have hr := LinearMap.finrank_range_add_finrank_ker (augmentedCokerMap pkg E).toLinearMap
  rw [LinearMap.range_eq_top.mpr hB] at hr
  simp only [finrank_top] at hr
  calc
    Module.finrank ℝ (D.coprod E.subtypeL).ker =
        Module.finrank ℝ (pkg.decDom.X₀ × (augmentedCokerMap pkg E).ker) := L.finrank_eq
    _ = Module.finrank ℝ pkg.decDom.X₀+Module.finrank ℝ (augmentedCokerMap pkg E).ker := Module.finrank_prod
    _ = Module.finrank ℝ pkg.decCodom.X₀+Module.finrank ℝ (augmentedCokerMap pkg E).ker := by
      rw [fredholmPackage_balanced pkg hD]
    _ = Module.finrank ℝ E := hr


end
section
open scoped ContDiff Topology
open Set Function Filter
open HolderCompletion
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

structure FiniteZeroGerm (F : ℝ × X → Y) (t : ℝ) (x : X) (m : ℕ) where
  kernelSpace : Submodule ℝ X
  finite_kernel : FiniteDimensional ℝ kernelSpace
  dimension : Module.finrank ℝ kernelSpace=m
  coordinate : X →L[ℝ] kernelSpace
  reconstruct : ℝ × kernelSpace → X
  base : reconstruct (t,coordinate x)=x
  smooth : ContDiffAt ℝ ∞ reconstruct (t,coordinate x)
  left_inv : ∀ v,coordinate (reconstruct v)=v.2
  zero : ∀ᶠ v in 𝓝 (t,coordinate x),F (v.1,reconstruct v)=0
  complete : ∀ᶠ v in 𝓝 (t,x),F v=0 → reconstruct (v.1,coordinate v.2)=v.2

lemma finiteZeroGerm_of_surjective {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F)
    {t : ℝ} {x : X} {D : X →L[ℝ] Y} (hD : HasFDerivAt (fun y => F (t,y)) D x)
    (hFred : D.IsFredholm) (hs : Surjective D) (hz : F (t,x)=0) :
    Nonempty (FiniteZeroGerm F t x (Module.finrank ℝ D.ker)) := by
  obtain ⟨pkg⟩ := hFred.nonempty_fredholmPackage
  let : FiniteDimensional ℝ pkg.decDom.X₀ := pkg.decDom.finite_X₀
  let P : X →L[ℝ] pkg.decDom.X₀ :=
    (ContinuousLinearMap.snd ℝ pkg.decDom.X₁ pkg.decDom.X₀).comp (domCoords pkg).toContinuousLinearMap
  refine ⟨⟨pkg.decDom.X₀,inferInstance,?_,P,parametricSolution pkg hF hD,
    parametricSolution_base pkg hF hD,parametricSolution_smooth pkg hF hD,
    parametricSolution_kernel_coordinate pkg hF hD,
    surjective_parametricSolution_zero pkg hF hD hs hz,parametric_zero_is_solution pkg hF hD hz⟩⟩
  rw [pkg.ker_eq]

lemma finiteTargetAugment_zero_germ {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F)
    (E : Submodule ℝ Y) [FiniteDimensional ℝ E] {t : ℝ} {x : X} {e : E}
    (hFred : IsIndexZeroFredholm (pathSpatialDerivative F (t,x)))
    (hs : Surjective ((pathSpatialDerivative F (t,x)).coprod E.subtypeL))
    (hz : finiteTargetAugment F E (t,(x,e))=0) :
    Nonempty (FiniteZeroGerm (finiteTargetAugment F E) t (x,e) (Module.finrank ℝ E)) := by
  let G := (pathSpatialDerivative F (t,x)).coprod E.subtypeL
  have hd : HasFDerivAt (fun v : X × E => finiteTargetAugment F E (t,v)) G (x,e) := by
    have hsli : ContDiff ℝ ∞ (fun v : X × E => finiteTargetAugment F E (t,v)) :=
      (finiteTargetAugment_smooth hF E).comp (contDiff_const.prodMk contDiff_id)
    have h := (hsli.differentiable (by simp) (x,e)).hasFDerivAt
    rwa [finiteTargetAugment_spatial_derivative hF E t x e] at h
  have hg := augment_fredholm hFred.1 E hs
  obtain ⟨pkg⟩ := hFred.1.nonempty_fredholmPackage
  have hdim := augmentedKernel_finrank pkg E hFred hs
  rw [←hdim]
  exact finiteZeroGerm_of_surjective (finiteTargetAugment_smooth hF E) hd hg hs hz

theorem ProperIndexZeroPath.stabilized_zero_germs {F : ℝ × X → Y} {U : Set X}
    (h : ProperIndexZeroPath F U) :
    ∃ E : Submodule ℝ Y,∃ _ : FiniteDimensional ℝ E,
      ∃ V : Set (ℝ × X),IsOpen V ∧
        {v : ℝ × X | v.1∈Icc (0:ℝ) 1 ∧ v.2∈U ∧ F v=0}⊆V ∧
        ∀ t∈Icc (0:ℝ) 1,∀ x∈U,(t,x)∈V → ∀ e : E,
          finiteTargetAugment F E (t,(x,e))=0 →
          Nonempty (FiniteZeroGerm (finiteTargetAugment F E) t (x,e) (Module.finrank ℝ E)) := by
  obtain ⟨E,hE,V,hVo,hZ,hV⟩ := h.finite_target_supplement
  let := hE
  refine ⟨E,hE,V,hVo,hZ,?_⟩
  intro t ht x hx hv e hz
  have hf : IsIndexZeroFredholm (pathSpatialDerivative F (t,x)) := by
    rw [pathSpatialDerivative_eq h.smooth]
    exact h.fredholm t ht x hx
  apply finiteTargetAugment_zero_germ h.smooth E hf _ hz
  have hs := hV t x hv e
  rwa [finiteTargetAugment_spatial_derivative h.smooth] at hs

omit [CompleteSpace X] [CompleteSpace Y] in
lemma ProperIndexZeroPath.stabilized_initial_graph [CompleteSpace X] [CompleteSpace Y]
    {F : ℝ × X → Y} {U : Set X}
    (h : ProperIndexZeroPath F U) (E : Submodule ℝ Y) :
    ∃ L : X ≃L[ℝ] Y,∀ x : X,∀ e : E,
      finiteTargetAugment F E (0,(x,e))=0 ↔ x= -L.symm (e:Y) := by
  obtain ⟨L,hL⟩ := h.initial
  refine ⟨L,?_⟩
  intro x e
  change F (0,x)+(e:Y)=0 ↔ _
  rw [hL]
  constructor
  · intro hx
    apply L.injective
    rw [map_neg,L.apply_symm_apply]
    exact eq_neg_of_add_eq_zero_left hx
  · rintro rfl
    rw [map_neg,L.apply_symm_apply,neg_add_cancel]


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma surjective_fredholm_right_inverse {D : X →L[ℝ] Y}
    (hD : D.IsFredholm) (hs : Surjective D) : D.HasRightInverse := by
  obtain ⟨pkg⟩ := hD.nonempty_fredholmPackage
  let := surjective_package_coker_subsingleton pkg hs
  let R : Y →L[ℝ] X := (domCoords pkg).symm.toContinuousLinearMap.comp
    ((pkg.equiv.symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.fst ℝ pkg.decCodom.X₁ pkg.decCodom.X₀).comp
        (codCoords pkg).toContinuousLinearMap)).prod 0)
  refine ⟨R,?_⟩
  intro y
  apply (codCoords pkg).injective
  change (codCoords pkg) (D ((domCoords pkg).symm (pkg.equiv.symm ((codCoords pkg) y).1,0)))=(codCoords pkg) y
  rw [fredholm_original_coords,(domCoords pkg).apply_symm_apply,pkg.equiv.apply_symm_apply]
  exact Prod.ext rfl (Subsingleton.elim _ _)

omit [CompleteSpace X] in
lemma local_continuous_right_inverse [CompleteSpace X] {Z : Type*} [TopologicalSpace Z]
    {A : Z → X →L[ℝ] Y} (hA : Continuous A) {z : Z}
    (hs : (A z).HasRightInverse) :
    ∃ V : Set Z,IsOpen V ∧ z∈V ∧ ∃ R : Z → Y →L[ℝ] X,
      ContinuousOn R V ∧ ∀ v∈V,(A v).comp (R v)=ContinuousLinearMap.id ℝ Y := by
  obtain ⟨R₀,hR₀⟩ := hs
  let B : Z → Y →L[ℝ] Y := fun v => (A v).comp R₀
  have hB : Continuous B := hA.clm_comp continuous_const
  have hBz : B z=ContinuousLinearMap.id ℝ Y := ContinuousLinearMap.ext hR₀
  let V := {v : Z | (B v).IsInvertible}
  have hV : IsOpen V := ContinuousLinearEquiv.isOpen.preimage hB
  refine ⟨V,hV,?_,fun v => R₀.comp (B v).inverse,?_,?_⟩
  · change (B z).IsInvertible
    rw [hBz]
    exact ⟨ContinuousLinearEquiv.refl ℝ Y,rfl⟩
  · intro v hv
    exact (continuousAt_const.clm_comp
      ((hv.contDiffAt_map_inverse (n := ∞)).continuousAt.comp hB.continuousAt)).continuousWithinAt
  · intro v hv
    rw [←ContinuousLinearMap.comp_assoc]
    exact hv.self_comp_inverse

lemma compact_continuous_right_inverse {Z : Type*} [MetricSpace Z]
    {A : Z → X →L[ℝ] Y} (hA : Continuous A) {K : Set Z} (hK : IsCompact K)
    (hs : ∀ z∈K,(A z).HasRightInverse) :
    ∃ V : Set Z,IsOpen V ∧ K⊆V ∧ ∃ R : Z → Y →L[ℝ] X,
      ContinuousOn R V ∧ ∀ v∈V,(A v).comp (R v)=ContinuousLinearMap.id ℝ Y := by
  classical
  choose O hO hz R hR hAR using fun z : K => local_continuous_right_inverse hA (hs z.val z.property)
  obtain ⟨s,hsO⟩ := hK.elim_finite_subcover O hO (by
    intro z hzK
    exact mem_iUnion.mpr ⟨⟨z,hzK⟩,hz ⟨z,hzK⟩⟩)
  let I := {z : K // z∈s}
  let : Fintype I := inferInstance
  obtain ⟨ρ,hρ⟩ := PartitionOfUnity.exists_isSubordinate hK.isClosed
    (fun i : I => O i.val) (fun i => hO i.val) (by
      intro z hzk
      obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp (hsO hzk)
      exact mem_iUnion.mpr ⟨⟨i,hi⟩,hzi⟩)
  let R₁ : Z → Y →L[ℝ] X := fun z => ∑ i : I,ρ i z • R i.val z
  have hR₁ : Continuous R₁ := by
    simpa only [finsum_eq_sum_of_fintype] using
      (PartitionOfUnity.IsSubordinate.continuous_finsum_smul (fun i : I => hO i.val) hρ
        (fun i : I => hR i.val))
  have hAR₁ : ∀ z∈K,(A z).comp (R₁ z)=ContinuousLinearMap.id ℝ Y := by
    intro z hzk
    have hsum : ∑ i : I,ρ i z=1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hzk
    calc
      (A z).comp (R₁ z) = ∑ i : I,ρ i z • ((A z).comp (R i.val z)) := by
        apply ContinuousLinearMap.ext
        intro y
        simp [R₁]
      _ = ∑ i : I,ρ i z • ContinuousLinearMap.id ℝ Y := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hzi : ρ i z=0
        · simp [hzi]
        · rw [hAR i.val z (hρ i (subset_closure hzi))]
      _ = ContinuousLinearMap.id ℝ Y := by rw [←Finset.sum_smul,hsum,one_smul]
  let B : Z → Y →L[ℝ] Y := fun z => (A z).comp (R₁ z)
  have hB : Continuous B := hA.clm_comp hR₁
  let V := {z : Z | (B z).IsInvertible}
  refine ⟨V,ContinuousLinearEquiv.isOpen.preimage hB,?_,
    fun z => (R₁ z).comp (B z).inverse,?_,?_⟩
  · intro z hzK
    change (B z).IsInvertible
    rw [show B z=ContinuousLinearMap.id ℝ Y from hAR₁ z hzK]
    exact ⟨ContinuousLinearEquiv.refl ℝ Y,rfl⟩
  · intro z hzV
    exact (hR₁.continuousAt.clm_comp
      ((hzV.contDiffAt_map_inverse (n := ∞)).continuousAt.comp hB.continuousAt)).continuousWithinAt
  · intro z hzV
    rw [←ContinuousLinearMap.comp_assoc]
    exact hzV.self_comp_inverse

lemma ProperIndexZeroPath.cylinder_supplement {F : ℝ × X → Y} {U : Set X}
    (h : ProperIndexZeroPath F U) :
    ∃ K : Set X,IsCompact K ∧ K⊆U ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x∈U,F (t,x)=0 →x∈K) ∧
      ∃ E : Submodule ℝ Y,∃ _ : FiniteDimensional ℝ E,
        ∃ V : Set (ℝ × X),IsOpen V ∧ Icc (0:ℝ) 1 ×ˢ K⊆V ∧
          ∀ v∈V,Surjective ((pathSpatialDerivative F v).coprod E.subtypeL) := by
  let Z := {v : ℝ × X | v.1∈Icc (0:ℝ) 1 ∧ v.2∈U ∧ F v=0}
  let K := Prod.snd '' Z
  have hK : IsCompact K := h.zeroSet_compact.image continuous_snd
  have hKU : K⊆U := by rintro _ ⟨v,hv,rfl⟩; exact hv.2.1
  obtain ⟨E,hE,V,hVo,hKV,hVs⟩ := compact_indexZero_supplement
    (pathSpatialDerivative_continuous h.smooth) (isCompact_Icc.prod hK) (by
      intro v hv
      rw [pathSpatialDerivative_eq h.smooth]
      exact h.fredholm v.1 hv.1 v.2 (hKU hv.2))
  exact ⟨K,hK,hKU,(fun t ht x hx hz => ⟨(t,x),⟨ht,hx,hz⟩,rfl⟩),E,hE,V,hVo,hKV,hVs⟩


end
section
open scoped ContDiff Topology
open Set Function Filter
open HolderCompletion
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

def splitKernelProjection (A : X →L[ℝ] Y) (R : Y →L[ℝ] X) : X →L[ℝ] X :=
  ContinuousLinearMap.id ℝ X-R.comp A

omit [CompleteSpace X] [CompleteSpace Y] in
lemma splitKernelProjection_apply [CompleteSpace X] [CompleteSpace Y]
    (A : X →L[ℝ] Y) (R : Y →L[ℝ] X) (x : X) :
    splitKernelProjection A R x=x-R (A x) := rfl

omit [CompleteSpace X] [CompleteSpace Y] in
lemma splitKernelProjection_mem_ker [CompleteSpace X] [CompleteSpace Y]
    {A : X →L[ℝ] Y} {R : Y →L[ℝ] X}
    (h : A.comp R=ContinuousLinearMap.id ℝ Y) (x : X) :
    A (splitKernelProjection A R x)=0 := by
  change A (x-R (A x))=0
  rw [map_sub,show A (R (A x))=A x from congrArg (fun T : Y →L[ℝ] Y => T (A x)) h,sub_self]

omit [CompleteSpace X] [CompleteSpace Y] in
lemma splitKernelProjection_fixed [CompleteSpace X] [CompleteSpace Y]
    {A : X →L[ℝ] Y} {R : Y →L[ℝ] X} {x : X}
    (hx : A x=0) : splitKernelProjection A R x=x := by
  simp only [splitKernelProjection_apply,hx,map_zero,sub_zero]

lemma splitKernelProjection_idempotent {A : X →L[ℝ] Y} {R : Y →L[ℝ] X}
    (h : A.comp R=ContinuousLinearMap.id ℝ Y) :
    (splitKernelProjection A R).comp (splitKernelProjection A R)=splitKernelProjection A R := by
  apply ContinuousLinearMap.ext
  intro x
  exact splitKernelProjection_fixed (splitKernelProjection_mem_ker h x)

lemma splitKernelProjection_range {A : X →L[ℝ] Y} {R : Y →L[ℝ] X}
    (h : A.comp R=ContinuousLinearMap.id ℝ Y) :
    (splitKernelProjection A R).range=A.ker := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    exact splitKernelProjection_mem_ker h x
  · intro x hx
    exact ⟨x,splitKernelProjection_fixed hx⟩

lemma ProperIndexZeroPath.cylinder_kernel_projection {F : ℝ × X → Y} {U : Set X}
    (h : ProperIndexZeroPath F U) :
    ∃ K : Set X,IsCompact K ∧ K⊆U ∧ (0:X)∈K ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x∈U,F (t,x)=0 →x∈K) ∧
      ∃ E : Submodule ℝ Y,∃ _ : FiniteDimensional ℝ E,
        ∃ V : Set (ℝ × X),IsOpen V ∧ Icc (0:ℝ) 1 ×ˢ K⊆V ∧
          ∃ P : (ℝ × X) → (X × E) →L[ℝ] (X × E),ContinuousOn P V ∧
            ∀ v∈V,Surjective ((pathSpatialDerivative F v).coprod E.subtypeL) ∧
              (P v).comp (P v)=P v ∧ (P v).range=((pathSpatialDerivative F v).coprod E.subtypeL).ker := by
  obtain ⟨K,hK,hKU,hZ,E,hE,V,hVo,hKV,hVs⟩ := h.cylinder_supplement
  let := hE
  let A : ℝ × X → (X × E) →L[ℝ] Y := fun v => (pathSpatialDerivative F v).coprod E.subtypeL
  have heA : A=(fun v => (pathSpatialDerivative F v).comp (ContinuousLinearMap.fst ℝ X E)+
      E.subtypeL.comp (ContinuousLinearMap.snd ℝ X E)) := by
    funext v
    apply ContinuousLinearMap.ext
    intro w
    rfl
  have hA : Continuous A := by
    rw [heA]
    exact ((pathSpatialDerivative_continuous h.smooth).clm_comp continuous_const).add continuous_const
  have hs : ∀ v∈Icc (0:ℝ) 1 ×ˢ K,(A v).HasRightInverse := by
    intro v hv
    have hf : IsIndexZeroFredholm (pathSpatialDerivative F v) := by
      rw [pathSpatialDerivative_eq h.smooth]
      exact h.fredholm v.1 hv.1 v.2 (hKU hv.2)
    exact surjective_fredholm_right_inverse (augment_fredholm hf.1 E (hVs v (hKV hv))) (hVs v (hKV hv))
  obtain ⟨W,hWo,hKW,R,hR,hAR⟩ := compact_continuous_right_inverse hA (isCompact_Icc.prod hK) hs
  have h0 : (0:X)∈K := by
    obtain ⟨L,hL⟩ := h.initial
    exact hZ 0 (by constructor <;> norm_num) 0 h.origin_mem ((hL 0).trans (map_zero L))
  refine ⟨K,hK,hKU,h0,hZ,E,hE,W,hWo,hKW,fun v => splitKernelProjection (A v) (R v),?_,?_⟩
  · exact continuousOn_const.sub (hR.clm_comp hA.continuousOn)
  · intro v hv
    refine ⟨?_,splitKernelProjection_idempotent (hAR v hv),splitKernelProjection_range (hAR v hv)⟩
    intro y
    exact ⟨R v y,congrArg (fun L : Y →L[ℝ] Y => L y) (hAR v hv)⟩


end
open scoped Topology
open Set Function Filter
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

def projectionTransport (P Q : X →L[ℝ] X) : X →L[ℝ] X :=
  Q*P+(1-Q)*(1-P)

omit [CompleteSpace X] in
lemma projectionTransport_self [CompleteSpace X] {P : X →L[ℝ] X} (hP : P*P=P) :
    projectionTransport P P=1 := by
  unfold projectionTransport
  calc
    P*P+(1-P)*(1-P)=1+(P*P-P)+(P*P-P) := by noncomm_ring
    _ = 1 := by rw [hP,sub_self]; simp

omit [CompleteSpace X] in
lemma projectionTransport_comp [CompleteSpace X] {P Q : X →L[ℝ] X} (hP : P*P=P) :
    projectionTransport P Q*P=Q*P := by
  unfold projectionTransport
  calc
    (Q*P+(1-Q)*(1-P))*P=Q*(P*P)+(1-Q)*(P-P*P) := by noncomm_ring
    _ = Q*P := by rw [hP,sub_self,mul_zero,add_zero]

omit [CompleteSpace X] in
lemma comp_projectionTransport [CompleteSpace X] {P Q : X →L[ℝ] X} (hQ : Q*Q=Q) :
    Q*projectionTransport P Q=Q*P := by
  unfold projectionTransport
  calc
    Q*(Q*P+(1-Q)*(1-P))=(Q*Q)*P+(Q-Q*Q)*(1-P) := by noncomm_ring
    _ = Q*P := by rw [hQ,sub_self,zero_mul,add_zero]

lemma projectionTransport_intertwines {P Q : X →L[ℝ] X} (hP : P*P=P) (hQ : Q*Q=Q) :
    projectionTransport P Q*P=Q*projectionTransport P Q :=
  (projectionTransport_comp hP).trans (comp_projectionTransport hQ).symm

lemma projectionTransport_fixed {P Q : X →L[ℝ] X} (hP : P*P=P) (hQ : Q*Q=Q)
    {x : X} (hx : P x=x) : Q (projectionTransport P Q x)=projectionTransport P Q x := by
  have hh := congrArg (fun T : X →L[ℝ] X => T x) (projectionTransport_intertwines hP hQ)
  change projectionTransport P Q (P x)=Q (projectionTransport P Q x) at hh
  rwa [hx,eq_comm] at hh

lemma projectionTransport_fixed_surjective {P Q : X →L[ℝ] X} (hP : P*P=P) (hQ : Q*Q=Q)
    (hi : (projectionTransport P Q).IsInvertible) {y : X} (hy : Q y=y) :
    ∃ x : X,P x=x ∧ projectionTransport P Q x=y := by
  obtain ⟨x,hx⟩ := hi.surjective y
  refine ⟨x,hi.injective ?_,hx⟩
  have hh := congrArg (fun T : X →L[ℝ] X => T x) (projectionTransport_intertwines hP hQ)
  change projectionTransport P Q (P x)=Q (projectionTransport P Q x) at hh
  rw [hx,hy] at hh
  exact hh.trans hx.symm

omit [CompleteSpace X] in
lemma projectionTransport_continuousOn [CompleteSpace X] {Z : Type*} [TopologicalSpace Z]
    {P Q : Z → X →L[ℝ] X} {S : Set Z} (hP : ContinuousOn P S) (hQ : ContinuousOn Q S) :
    ContinuousOn (fun z => projectionTransport (P z) (Q z)) S :=
  (hQ.mul hP).add ((continuousOn_const.sub hQ).mul (continuousOn_const.sub hP))

lemma compact_projection_transport {Z : Type*} [MetricSpace Z]
    {P : Z → X →L[ℝ] X} {K : Set Z} (hK : IsCompact K) (hP : ContinuousOn P K)
    (hp : ∀ z∈K,P z*P z=P z) :
    ∃ δ : ℝ,0<δ ∧ ∀ z∈K,∀ w∈K,dist z w<δ →(projectionTransport (P z) (P w)).IsInvertible := by
  have h1 : (1:X →L[ℝ] X).IsInvertible := ⟨ContinuousLinearEquiv.refl ℝ X,rfl⟩
  have ho : IsOpen {A : X →L[ℝ] X | A.IsInvertible} := ContinuousLinearEquiv.isOpen
  obtain ⟨ε,hε,hεi⟩ := Metric.isOpen_iff.mp ho 1 h1
  let H : Z × Z → X →L[ℝ] X := fun v => projectionTransport (P v.1) (P v.2)
  have hH : ContinuousOn H (K ×ˢ K) := projectionTransport_continuousOn
    (hP.comp continuous_fst.continuousOn (fun v hv => hv.1))
    (hP.comp continuous_snd.continuousOn (fun v hv => hv.2))
  obtain ⟨δ,hδ,hδH⟩ := Metric.uniformContinuousOn_iff.mp
    ((hK.prod hK).uniformContinuousOn_of_continuous hH) ε hε
  refine ⟨δ,hδ,?_⟩
  intro z hz w hw hzw
  apply hεi
  rw [Metric.mem_ball]
  have hd : dist (z,w) (z,z)<δ := by simpa [dist_comm] using hzw
  have hh := hδH (z,w) ⟨hz,hw⟩ (z,z) ⟨hz,hz⟩ hd
  simpa only [H,projectionTransport_self (hp z hz)] using hh



end HigherDimensionalBallPacking.Rigidity
end

end OAI
