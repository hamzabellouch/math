import Mathlib
import OAI.Geometry.CubicTorus.Profiles.FirstAxisShift

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_selected_nodal_irreducible {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) :
    ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      ∀ (v : Cover) (D A : Set Torus),
        IsPositiveNodalPiece (directionalNormalScalar N hN hp v) (frontier (openRepresentative E)) D →
        IsPositiveNodalPiece (directionalNormalScalar N hN hp v) (frontier (openRepresentative E)) A →
        D.Nonempty → A.Nonempty → ¬Disjoint D A := by
  obtain ⟨μ,H,N,hN,hp,hμ,hae,hb,hs,hj,hunused⟩ := isMinimizerAt_H1_translation_jacobi hV hE hmin
  refine ⟨μ,N,hN,hp,hμ,hae,?_⟩
  intro v D A hD hA hDn hAn hDA
  let f := directionalNormalScalar N hN hp v
  have hjN := directionalNormalScalar_global_jacobi μ N hN hp (fun i ↦ (hj i).2)
  have hjf := hjN v
  obtain ⟨hDm,hdmem⟩ := isMinimizerAt_positive_nodal_piece_H1 hV hE hmin hμ f hD
  obtain ⟨hAm,hamem⟩ := isMinimizerAt_positive_nodal_piece_H1 hV hE hmin hμ f hA
  let d := nodalSurfaceJet μ f D hDm
  let a := nodalSurfaceJet μ f A hAm
  let u := surfaceNodalBalance μ d a
  have hdnull := nodalSurfaceJet_null μ (surfaceCurvatureLp μ N hN) f D hDm hdmem hjf
  have hanull := nodalSurfaceJet_null μ (surfaceCurvatureLp μ N hN) f A hAm hamem hjf
  have horth := surfaceJacobiB_disjoint_nodal μ (surfaceCurvatureLp μ N hN) f f D A hDm hAm hDA
  have humem : u∈surfaceH1 μ := surfaceNodalBalance_mem μ hdmem hamem
  have hunull : surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u=0 :=
    surfaceNodalBalance_null μ _ hdnull hanull horth
  obtain ⟨U,hU,hUn,hUD,hUA⟩ := isMinimizerAt_negative_unused_patch hV hE hmin hμ f
    (sibling_directionalNormalScalar_mean_zero hμ hN hp hae v) hD hA hDn
  have hju : ∀ t∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u t=0 :=
    hunused u humem (surfaceNodalBalance_mean μ d a) hunull U hU hUn
      (surfaceNodalBalance_zero_patch μ (nodalSurfaceJet_zero_outside μ f D U hDm hUD)
        (nodalSurfaceJet_zero_outside μ f A U hAm hUA))
  let F : Torus → ℝ := fun x ↦ surfaceMean μ a*nodalTorusScalar f D x-
    surfaceMean μ d*nodalTorusScalar f A x
  have hFm : Measurable F :=
    (measurable_const.mul (nodalTorusScalar_measurable f hDm)).sub
      (measurable_const.mul (nodalTorusScalar_measurable f hAm))
  have hFc : ContinuousOn F (frontier (openRepresentative E)) :=
    (continuousOn_const.mul (positiveNodalPiece_continuousOn f hD)).sub
      (continuousOn_const.mul (positiveNodalPiece_continuousOn f hA))
  have hFa : ∀ᵐ z ∂(μ : Measure NormalBundle),u.1 z=F (normalProjection z) :=
    surfaceNodalBalance_scalar_ae μ f f D A hDm hAm
  have hother : (frontier (openRepresentative E)\D).Nonempty := by
    obtain ⟨x,hx⟩ := hAn
    exact ⟨x,positiveNodalPiece_subset f hA hx,fun hd ↦ Set.disjoint_left.mp hDA hd hx⟩
  obtain ⟨x,hcl,hnot⟩ := positiveNodalPiece_boundary_nonempty f hc hD hDn hother
  have hk : surfaceMean μ a≠0 := (isMinimizerAt_nodal_mean_pos hV hE hmin hμ f hAm hA hAn).ne'
  apply isMinimizerAt_nodal_truncation_impossible hV hE hmin hμ hN hp hae hjN f hjf
    humem hju hFm hFc hFa hD hcl hnot hk
  · intro x hx
    have hxA : x∉A := fun ha ↦ Set.disjoint_left.mp hDA hx ha
    simp only [F,nodalTorusScalar,Set.indicator_of_mem hx,Set.indicator_of_notMem hxA,
      mul_zero,sub_zero]
  · intro x hx hle
    have hxD : x∉D := fun hd ↦ ((positiveNodalPiece_superlevels f isClosed_frontier hD).2.1 x hd).not_ge hle
    have hxA : x∉A := fun ha ↦ ((positiveNodalPiece_superlevels f isClosed_frontier hA).2.1 x ha).not_ge hle
    simp only [F,nodalTorusScalar,Set.indicator_of_notMem hxD,Set.indicator_of_notMem hxA,
      mul_zero,sub_zero]

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma positiveNodalPiece_relative_compl (f : smoothPeriodicScalars) {S D : Set Torus}
    (hD : IsPositiveNodalPiece f S D) :
    IsPositiveNodalPiece f S ({x | x∈S ∧ 0<f.val (representative x)}\D) := by
  obtain ⟨⟨U,hU,hDU⟩,⟨C,hC,hDC⟩⟩ := hD
  constructor
  · refine ⟨Cᶜ,hC.isOpen_compl,?_⟩
    rw [hDC]
    ext x
    simp only [Set.mem_sdiff,mem_inter_iff,mem_ofPred_eq,mem_compl_iff]
    tauto
  · refine ⟨Uᶜ,hU.isClosed_compl,?_⟩
    rw [hDU]
    ext x
    simp only [Set.mem_sdiff,mem_inter_iff,mem_ofPred_eq,mem_compl_iff]
    tauto

lemma positiveBoundaryDomain_preconnected (f : smoothPeriodicScalars) (S : Set Torus)
    (a : positiveBoundaryLocus f S) : IsPreconnected (positiveBoundaryDomain f S a) :=
  isPreconnected_connectedComponent.image _
    (continuous_subtype_val.comp continuous_subtype_val).continuousOn

lemma positiveNodalPiece_eq_positive_locus (f : smoothPeriodicScalars) {S D : Set Torus}
    (hD : IsPositiveNodalPiece f S D) (_hDn : D.Nonempty)
    (hirr : ∀ A : Set Torus,IsPositiveNodalPiece f S A → A.Nonempty → ¬Disjoint D A) :
    D={x | x∈S ∧ 0<f.val (representative x)} := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [hD.1.choose_spec.2] at hx
    exact hx.1
  · intro x hx
    by_contra hxD
    apply hirr _ (positiveNodalPiece_relative_compl f hD) ⟨x,hx,hxD⟩
    exact Set.disjoint_left.mpr (fun y hy hA ↦ hA.2 hy)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_translation_signs_preconnected {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) :
    ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (_hN : ContDiff ℝ (⊤ : ℕ∞) N) (_hp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      ∀ v : Cover,
        IsPreconnected {x : Torus | x∈frontier (openRepresentative E) ∧
          0<⟪v,N (representative x)⟫} ∧
        IsPreconnected {x : Torus | x∈frontier (openRepresentative E) ∧
          ⟪v,N (representative x)⟫<0} := by
  obtain ⟨μ,N,hN,hp,hμ,hae,hirr⟩ :=
    isMinimizerAt_selected_nodal_irreducible hV hE hmin hc
  have hpos (v : Cover) :
      IsPreconnected {x : Torus | x∈frontier (openRepresentative E) ∧
        0<⟪v,N (representative x)⟫} := by
    let f := directionalNormalScalar N hN hp v
    by_cases hn : ({x : Torus | x∈frontier (openRepresentative E) ∧
        0<f.val (representative x)} : Set Torus).Nonempty
    · obtain ⟨x,hxS,hxp⟩ := hn
      let a : positiveBoundaryLocus f (frontier (openRepresentative E)) := ⟨⟨x,hxS⟩,hxp⟩
      let D := positiveBoundaryDomain f (frontier (openRepresentative E)) a
      have hD := isMinimizerAt_actual_nodal_piece hV hE hmin f a
      have hDn := positiveBoundaryDomain_nonempty f (frontier (openRepresentative E)) a
      have heq := positiveNodalPiece_eq_positive_locus f hD hDn (fun A hA hAn ↦
        hirr v D A hD hA hDn hAn)
      have hpD := positiveBoundaryDomain_preconnected f (frontier (openRepresentative E)) a
      rw [heq] at hpD
      simpa only [f,directionalNormalScalar_apply] using hpD
    · have he := Set.not_nonempty_iff_eq_empty.mp hn
      have hem : IsPreconnected {x : Torus | x∈frontier (openRepresentative E) ∧
        0<f.val (representative x)} := he ▸ isPreconnected_empty
      simpa only [f,directionalNormalScalar_apply] using hem
  refine ⟨μ,N,hN,hp,hμ,hae,fun v ↦ ⟨hpos v,?_⟩⟩
  simpa only [inner_neg_left,neg_pos] using hpos (-v)

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_slab_or_translation_signs {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) :
    (perimeter E=2 ∧ 1/Real.pi≤ min V (1-V) ∧ StandardRegionAt V E) ∨
    (IsPreconnected (frontier (openRepresentative E)) ∧
      ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
        (_hN : ContDiff ℝ (⊤ : ℕ∞) N) (_hp : ∀ m x,N (x+latticeVector m)=N x),
        IsNormalMeasure E μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
        ∀ v : Cover,
          IsPreconnected {x : Torus | x∈frontier (openRepresentative E) ∧
            0<⟪v,N (representative x)⟫} ∧
          IsPreconnected {x : Torus | x∈frontier (openRepresentative E) ∧
            ⟪v,N (representative x)⟫<0}) := by
  rcases isMinimizerAt_connected_or_standard_slab hV hmin with hc | hsl
  · right
    refine ⟨hc,?_⟩
    let F := toMeasurable torusVolume E
    have hF : MeasurableSet F := measurableSet_toMeasurable _ _
    have hae : F =ᵐ[torusVolume] E := hmin.1.1.toMeasurable_ae_eq
    have hminF : IsMinimizerAt V F := (isMinimizerAt_congr_ae hae).mpr hmin
    have hcF : IsPreconnected (frontier (openRepresentative F)) := by
      rwa [openRepresentative_congr_ae hae]
    obtain ⟨μ,N,hN,hp,hμ,hn,hsg⟩ :=
      isMinimizerAt_translation_signs_preconnected hV hF hminF hcF
    refine ⟨μ,N,hN,hp,hμ.congr_ae hae,hn,?_⟩
    simpa only [openRepresentative_congr_ae hae] using hsg
  · exact Or.inl hsl

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma odd_preconnected_sign_half {X : Type*} [TopologicalSpace X]
    {S : Set X} {R : X → X} {s u : X → ℝ} (hs : Continuous s)
    (hR : ∀ x∈S,R x∈S) (hsR : ∀ x,s (R x)= -s x)
    (huR : ∀ x∈S,u (R x)= -u x)
    (hz : ∀ x∈S,s x=0 → u x=0)
    (hc : IsPreconnected {x | x∈S ∧ 0<u x}) :
    (∀ x∈S,s x<0 → u x≤0) ∨ (∀ x∈S,s x<0 → 0≤u x) := by
  classical
  by_cases hn : ∃ x∈S,s x<0 ∧ 0<u x
  · right
    obtain ⟨a,ha,has,hau⟩ := hn
    have hP : {x | x∈S ∧ 0<u x}⊆{x | s x<0}∪{x | 0<s x} := by
      rintro x ⟨hx,hu⟩
      have hne : s x≠0 := fun h ↦ hu.ne' (hz x hx h)
      rcases lt_or_gt_of_ne hne with h|h
      · exact Or.inl h
      · exact Or.inr h
    have hsep : Disjoint {x | s x<0} {x | 0<s x} := by
      rw [Set.disjoint_left]
      intro x hx hy
      exact (show s x<0 from hx).not_gt (show 0<s x from hy)
    have hsub := hc.subset_left_of_subset_union (isOpen_lt hs continuous_const)
      (isOpen_lt continuous_const hs) hsep hP ⟨a,⟨ha,hau⟩,has⟩
    intro x hx hxs
    by_contra hneg
    have hu : u x<0 := lt_of_not_ge hneg
    have hh := hsub (show R x∈{x | x∈S ∧ 0<u x} from
      ⟨hR x hx,by rw [huR x hx]; exact neg_pos.mpr hu⟩)
    change s (R x)<0 at hh
    rw [hsR] at hh
    linarith
  · left
    intro x hx hxs
    exact le_of_not_gt (fun hu ↦ hn ⟨x,hx,hxs,hu⟩)

theorem isMinimizerAt_any_normal_signs {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (v : Cover) :
    IsPreconnected {x : Torus | x∈frontier (openRepresentative E) ∧
      0<⟪v,N (representative x)⟫} ∧
    IsPreconnected {x : Torus | x∈frontier (openRepresentative E) ∧
      ⟪v,N (representative x)⟫<0} := by
  obtain ⟨ν,M,hM,hpM,hν,haM,hs⟩ :=
    Periodic.isMinimizerAt_translation_signs_preconnected hV hE hmin hc
  have he : ∀ x∈frontier (openRepresentative E),N (representative x)=M (representative x) := by
    intro x hx
    obtain ⟨w,hw⟩ := isMinimizerAt_normal_unique hV hE hmin (representative x)
      (by simpa only [quotientMap_representative] using hx)
    exact (hw μ hμ N hN hp hae).trans (hw ν hν M hM hpM haM).symm
  have hpos : {x : Torus | x∈frontier (openRepresentative E) ∧ 0<⟪v,N (representative x)⟫}=
      {x : Torus | x∈frontier (openRepresentative E) ∧ 0<⟪v,M (representative x)⟫} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    by_cases hx : x∈frontier (openRepresentative E)
    · simp only [hx,true_and,he x hx]
    · simp only [hx,false_and]
  have hneg : {x : Torus | x∈frontier (openRepresentative E) ∧ ⟪v,N (representative x)⟫<0}=
      {x : Torus | x∈frontier (openRepresentative E) ∧ ⟪v,M (representative x)⟫<0} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    by_cases hx : x∈frontier (openRepresentative E)
    · simp only [hx,true_and,he x hx]
    · simp only [hx,false_and]
  rw [hpos,hneg]
  exact hs v

theorem isMinimizerAt_reflection_weak_normal_sign {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    (hR : E=ᵐ[torusVolume](torusFirstReflection ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    (∀ x∈frontier (openRepresentative E),firstSeamFunction (representative x)<0 →
      N (representative x) 0≤0) ∨
    (∀ x∈frontier (openRepresentative E),firstSeamFunction (representative x)<0 →
      0≤N (representative x) 0) := by
  have hsign := (isMinimizerAt_any_normal_signs hV hE hmin hc hμ hN hp hae
    (EuclideanSpace.single 0 1)).1
  have hsign' : IsPreconnected {x : Torus | x∈frontier (openRepresentative E) ∧
      0<N (representative x) 0} := by
    simpa only [EuclideanSpace.inner_single_left,map_one,one_mul] using hsign
  exact odd_preconnected_sign_half
    (continuous_periodic_descent firstSeamFunction_contDiff.continuous firstSeamFunction_periodic)
    (fun x hx ↦ (isMinimizerAt_reflection_boundary hV hE hmin hR x).mpr hx)
    firstSeam_representative_reflection
    (isMinimizerAt_reflection_normal_scalar hV hE hmin hR hμ hN hp hae)
    (isMinimizerAt_firstSeam_normal_zero hV hE hmin hR hμ hN hp hae) hsign'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_normal_strong_minimum {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (v : Cover) {x : Torus} (hx : x∈frontier (openRepresentative E))
    (hpos : ∀ᶠ y in 𝓝 x,y∈frontier (openRepresentative E) → 0≤⟪v,N (representative y)⟫)
    (hz : ⟪v,N (representative x)⟫=0) :
    ∀ y∈frontier (openRepresentative E),⟪v,N (representative y)⟫=0 := by
  obtain ⟨ν,H,M,hM,hpM,hν,haM,hb,hs,hj,hu⟩ := Periodic.isMinimizerAt_H1_translation_jacobi hV hE hmin
  have he : ∀ y∈frontier (openRepresentative E),N (representative y)=M (representative y) := by
    intro y hy
    obtain ⟨w,hw⟩ := isMinimizerAt_normal_unique hV hE hmin (representative y)
      (by simpa only [quotientMap_representative] using hy)
    exact (hw μ hμ N hN hp hae).trans (hw ν hν M hM hpM haM).symm
  have hjM := directionalNormalScalar_global_jacobi ν M hM hpM (fun i ↦ (hj i).2)
  have hzM : (directionalNormalScalar M hM hpM v).val (representative x)=0 := by
    rw [directionalNormalScalar_apply,←he x hx]
    exact hz
  have hpM' : ∀ᶠ y in 𝓝 x,y∈frontier (openRepresentative E) →
      0≤(directionalNormalScalar M hM hpM v).val (representative y) := by
    filter_upwards [hpos] with y hy hyB
    rw [directionalNormalScalar_apply,←he y hyB]
    exact hy hyB
  have hzall := isMinimizerAt_Jacobi_strong_minimum hV hE hmin hc hν hM hpM haM hjM
    (directionalNormalScalar M hM hpM v) (hjM v) hx hpM' hzM
  intro y hy
  rw [he y hy]
  simpa only [directionalNormalScalar_apply] using hzall y hy

theorem isMinimizerAt_reflection_strict_normal_sign {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    (hR : E=ᵐ[torusVolume](torusFirstReflection ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    (∀ x∈frontier (openRepresentative E),N (representative x) 0=0) ∨
    (∀ x∈frontier (openRepresentative E),firstSeamFunction (representative x)<0 →
      N (representative x) 0<0) ∨
    (∀ x∈frontier (openRepresentative E),firstSeamFunction (representative x)<0 →
      0<N (representative x) 0) := by
  have hs := continuous_periodic_descent firstSeamFunction_contDiff.continuous firstSeamFunction_periodic
  by_cases hzero : ∀ x∈frontier (openRepresentative E),N (representative x) 0=0
  · exact Or.inl hzero
  · right
    rcases isMinimizerAt_reflection_weak_normal_sign hV hE hmin hc hR hμ hN hp hae with hneg|hpos
    · left
      intro x hx hxs
      refine lt_of_le_of_ne (hneg x hx hxs) ?_
      intro hzx
      have hzall := isMinimizerAt_normal_strong_minimum hV hE hmin hc hμ hN hp hae
        (-(EuclideanSpace.single 0 1)) hx (by
          filter_upwards [(isOpen_lt hs continuous_const).mem_nhds hxs] with y hy hyB
          simpa only [inner_neg_left,EuclideanSpace.inner_single_left,map_one,one_mul,neg_nonneg] using hneg y hyB hy)
        (by simp only [inner_neg_left,EuclideanSpace.inner_single_left,map_one,one_mul,hzx,neg_zero])
      apply hzero
      intro y hy
      simpa only [inner_neg_left,EuclideanSpace.inner_single_left,map_one,one_mul,neg_eq_zero] using hzall y hy
    · right
      intro x hx hxs
      refine lt_of_le_of_ne (hpos x hx hxs) ?_
      intro hzx
      have hzall := isMinimizerAt_normal_strong_minimum hV hE hmin hc hμ hN hp hae
        (EuclideanSpace.single 0 1) hx (by
          filter_upwards [(isOpen_lt hs continuous_const).mem_nhds hxs] with y hy hyB
          simpa only [EuclideanSpace.inner_single_left,map_one,one_mul] using hpos y hyB hy)
        (by simp only [EuclideanSpace.inner_single_left,map_one,one_mul,←hzx])
      apply hzero
      intro y hy
      simpa only [EuclideanSpace.inner_single_left,map_one,one_mul] using hzall y hy

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normal_zero_translation_ae {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {v : Cover} (hz : ∀ᵐ z ∂(μ : Measure NormalBundle),⟪(z.2 : Cover),v⟫=0)
    (t : ℝ) : E=ᵐ[torusVolume] (fun x ↦ x+quotientMap (t • v)) ⁻¹' E := by
  obtain ⟨M,hM,hpolar,hunit⟩ := normalMeasure_polar_unit hμ
  have hzM : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus),⟪M x,v⟫=0 := by
    change ∀ᵐ x ∂Measure.map normalProjection (μ : Measure NormalBundle),⟪M x,v⟫=0
    rw [ae_map_iff normalProjection_continuous.measurable.aemeasurable
      (measurableSet_eq_fun (hM.inner measurable_const) measurable_const)]
    filter_upwards [hpolar,hz] with z hp hz
    change ⟪M (quotientMap z.1),v⟫=0
    rw [hp,hz]
  have hmass (B : Set Torus) : directionalMass (spatialNormalMeasure μ) M (-(t • v)) B=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae hzM] with x hx
    simp only [inner_neg_right,real_inner_smul_right,hx,mul_zero,neg_zero,abs_zero,Pi.zero_apply]
  obtain ⟨r,hr⟩ := (isCompact_univ : IsCompact (univ : Set Torus)).isBounded.subset_ball (0 : Torus)
  have hall : Metric.ball (0 : Torus) r=univ := eq_univ_of_univ_subset hr
  have hi := characteristic_directional_translation_bound hE hμ hM hpolar hunit
    (0 : Torus) (r := r) (s := 1) (by norm_num) (-(t • v))
  rw [hmass,hall,Measure.restrict_univ,quotientMap_neg] at hi
  simp only [sub_neg_eq_add] at hi
  have hint : Integrable (fun x ↦ |characteristic E (x+quotientMap (t • v))-characteristic E x|) torusVolume := by
    apply Integrable.of_bound (((measurable_characteristic hE).comp
      (measurable_id.add_const _)).sub (measurable_characteristic hE)).abs.aestronglyMeasurable 1
    exact Eventually.of_forall fun x ↦ by
      rcases characteristic_dichotomy E (x+quotientMap (t • v)) with h|h <;>
        rcases characteristic_dichotomy E x with h'|h' <;> simp [h,h']
  have he := (integral_eq_zero_iff_of_nonneg (fun x ↦ abs_nonneg _) hint).mp
    (le_antisymm hi (integral_nonneg fun x ↦ abs_nonneg _))
  filter_upwards [he] with x hx
  have heq := sub_eq_zero.mp (abs_eq_zero.mp hx)
  change (x∈E)=(x+quotientMap (t • v)∈E)
  apply propext
  by_cases h : x∈E <;> by_cases h' : x+quotientMap (t • v)∈E <;>
    simp_all [characteristic]

theorem isMinimizerAt_zero_normal_invariant {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (_hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (v : Cover) (hz : ∀ x∈frontier (openRepresentative E),⟪v,N (representative x)⟫=0)
    (t : ℝ) :
    E=ᵐ[torusVolume] (fun x ↦ x+quotientMap (t • v)) ⁻¹' E ∧
    openRepresentative E=(fun x ↦ x+quotientMap (t • v)) ⁻¹' openRepresentative E ∧
    frontier (openRepresentative E)=(fun x ↦ x+quotientMap (t • v)) ⁻¹' frontier (openRepresentative E) := by
  have hμO : IsNormalMeasure (openRepresentative E) μ :=
    hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  have hflux : ∀ᵐ z ∂(μ : Measure NormalBundle),⟪(z.2 : Cover),v⟫=0 := by
    filter_upwards [normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμO,hae] with z hb hn
    have hh := hz (quotientMap z.1) hb
    rw [periodic_representative hp,hn,real_inner_comm] at hh
    exact hh
  have he := normal_zero_translation_ae hE hμ hflux t
  have hO := openRepresentative_congr_ae he
  rw [openRepresentative_translation hE] at hO
  refine ⟨he,hO,?_⟩
  exact (congrArg frontier hO).trans
    ((Homeomorph.addRight (quotientMap (t • v))).preimage_frontier (openRepresentative E)).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalizedCMCCharts_zero_component_differential {B : Set Torus}
    {N : Cover → Cover} {H : ℝ} (hcharts : HasNormalizedCMCCharts B N H)
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) {v : Cover}
    (hz : ∀ x : Cover,quotientMap x∈B → ⟪v,N x⟫=0)
    {a : Cover} (ha : quotientMap a∈B) {w : Cover} (hw : ⟪N a,w⟫=0) :
    ⟪v,fderiv ℝ N a w⟫=0 := by
  obtain ⟨hn,f,hf,hf0,hfgrad,hg,hcov⟩ := hcharts a ha
  let Φ : Plane → Cover := fun y ↦ a+normalGraph (N a) f y
  have hΦ0 : Φ 0=a := by
    simp only [Φ,normalGraph,hf0,zero_smul,add_zero]
    have he : normalPlaneEmbedding (N a) 0=0 := norm_eq_zero.mp (by rw [normalPlaneEmbedding_norm,norm_zero])
    rw [he,add_zero]
  have hΦ : DifferentiableAt ℝ Φ 0 :=
    (normalGraph_hasFDerivAt (n := N a) (hf.differentiable (by simp) 0)).differentiableAt.const_add a
  have hzero : (fun y ↦ ⟪v,N (Φ y)⟫)=ᶠ[𝓝 (0 : Plane)](fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hg] with y hy
    exact hz _ hy.2.1
  have hd := hzero.fderiv_eq (𝕜 := ℝ)
  have hcomp := ((innerSL ℝ v).hasFDerivAt.comp (Φ 0)
    (hN.differentiable (by simp) (Φ 0)).hasFDerivAt).comp 0 hΦ.hasFDerivAt
  change HasFDerivAt (fun y ↦ ⟪v,N (Φ y)⟫) _ 0 at hcomp
  rw [hcomp.fderiv,hΦ0] at hd
  have he := congrArg (fun L : Plane →L[ℝ] ℝ ↦ L (normalPlaneCoordinates (N a) w)) hd
  have hΦd : fderiv ℝ Φ 0 (normalPlaneCoordinates (N a) w)=w := by
    rw [fderiv_const_add]
    rw [normalGraph_fderiv_apply hf,hfgrad,inner_zero_left,zero_smul,add_zero]
    exact normalPlaneEmbedding_coordinates_of_inner_zero hn hw
  simpa only [ContinuousLinearMap.comp_apply,innerSL_apply_apply,hΦd,fderiv_const_apply,zero_apply] using he

theorem isMinimizerAt_zero_component_shape_kernel {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {H : ℝ} (hb : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
    {v : Cover} (hz : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ⟪v,N x⟫=0)
    {a : Cover} (ha : quotientMap a∈frontier (openRepresentative E)) :
    fderiv ℝ N a v=0 := by
  have hcharts := isMinimizerAt_hasNormalizedCMCCharts hV hE hmin hμ hN hp hae hb
  have hd := smooth_unit_normal_derivative (hN.differentiable (by simp) a) (hb a ha).1
  have hDv : ⟪N a,fderiv ℝ N a v⟫=0 := by
    rw [←ContinuousLinearMap.adjoint_inner_left,hd,inner_zero_left]
  have hv : ⟪N a,v⟫=0 := by rw [real_inner_comm,hz a ha]
  have hh := isMinimizerAt_shape_tangent_symmetric hV hE hmin hμ hN hp hae a ha v
    (fderiv ℝ N a v) hv hDv
  rw [normalizedCMCCharts_zero_component_differential hcharts hN hz ha hDv] at hh
  exact inner_self_eq_zero.mp hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_zero_component_shape {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {H : ℝ} (hb : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
    {v : Cover} (hv : ‖v‖=1)
    (hz : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ⟪v,N x⟫=0)
    {a : Cover} (ha : quotientMap a∈frontier (openRepresentative E))
    {w : Cover} (hw : ⟪N a,w⟫=0) :
    fderiv ℝ N a w=H • (w-⟪v,w⟫ • v) := by
  have hd := smooth_unit_normal_derivative (hN.differentiable (by simp) a) (hb a ha).1
  have hD (u : Cover) : ⟪N a,fderiv ℝ N a u⟫=0 := by
    rw [←ContinuousLinearMap.adjoint_inner_left,hd,inner_zero_left]
  have hnv : ⟪N a,v⟫=0 := by simpa only [real_inner_comm] using hz a ha
  have hk := isMinimizerAt_zero_component_shape_kernel hV hE hmin hμ hN hp hae hb hz ha
  have hh := normal_unit_kernel_shape (hb a ha).1.self_of_nhds hv hnv hD
    (isMinimizerAt_shape_tangent_symmetric hV hE hmin hμ hN hp hae a ha) hk hw
  rw [←divergence_eq_coverTrace,(hb a ha).2] at hh
  exact hh

theorem isMinimizerAt_zero_component_curvature {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {H : ℝ} (hb : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
    {v : Cover} (hv : ‖v‖=1)
    (hz : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ⟪v,N x⟫=0)
    {a : Cover} (ha : quotientMap a∈frontier (openRepresentative E)) :
    coverTrace ((fderiv ℝ N a).comp (fderiv ℝ N a))=H^2 := by
  have hd := smooth_unit_normal_derivative (hN.differentiable (by simp) a) (hb a ha).1
  have hD (u : Cover) : ⟪N a,fderiv ℝ N a u⟫=0 := by
    rw [←ContinuousLinearMap.adjoint_inner_left,hd,inner_zero_left]
  have hnv : ⟪N a,v⟫=0 := by simpa only [real_inner_comm] using hz a ha
  have hk := isMinimizerAt_zero_component_shape_kernel hV hE hmin hμ hN hp hae hb hz ha
  have hh := normal_unit_kernel_trace_square (hb a ha).1.self_of_nhds hv hnv hD
    (isMinimizerAt_shape_tangent_symmetric hV hE hmin hμ hN hp hae a ha) hk
  rw [←divergence_eq_coverTrace,(hb a ha).2] at hh
  exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def sibling_axialProjection (v : Cover) : Cover →L[ℝ] Cover :=
  ContinuousLinearMap.id ℝ Cover-(innerSL ℝ v).smulRight v

lemma sibling_axialProjection_apply (v w : Cover) : sibling_axialProjection v w=w-⟪v,w⟫ • v := rfl

lemma axialProjection_fixed {v w : Cover} (hw : ⟪v,w⟫=0) : sibling_axialProjection v w=w := by
  rw [sibling_axialProjection_apply,hw,zero_smul,sub_zero]

lemma graphSlopeNormal_inner_fderiv {n : Cover} (hn : ‖n‖=1)
    {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y u : Plane) :
    ⟪graphSlopeNormal n (gradient f y),fderiv ℝ (normalGraph n f) y u⟫=0 := by
  have he : ⟪normalPlaneEmbedding n (gradient f y),normalPlaneEmbedding n u⟫=⟪gradient f y,u⟫ :=
    (normalPlaneLinearIsometry n).inner_map_map _ _
  have hen : ⟪normalPlaneEmbedding n (gradient f y),n⟫=0 := by
    simpa only [real_inner_comm] using normalPlaneEmbedding_inner hn (gradient f y)
  rw [normalGraph_fderiv_apply hf,graphSlopeNormal_weight hn,real_inner_smul_left,
    inner_sub_left,inner_add_right,inner_add_right,real_inner_smul_right,
    real_inner_smul_right,normalPlaneEmbedding_inner hn,hen,he,
    real_inner_self_eq_norm_sq,hn,one_pow,mul_one,mul_zero,zero_add,add_zero,
    sub_self,mul_zero]

theorem normalizedCMCCharts_axial_local_center {B : Set Torus}
    {N : Cover → Cover} {H : ℝ} (hc : HasNormalizedCMCCharts B N H)
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hH : H≠0) {v : Cover}
    (hs : ∀ a : Cover,quotientMap a∈B → ∀ w : Cover,⟪N a,w⟫=0 →
      fderiv ℝ N a w=H • sibling_axialProjection v w)
    {a : Cover} (ha : quotientMap a∈B) :
    ∀ᶠ w in 𝓝 (0 : Cover),quotientMap (a+w)∈B →
      sibling_axialProjection v (a+w)-H⁻¹ • N (a+w)=sibling_axialProjection v a-H⁻¹ • N a := by
  obtain ⟨hn,f,hf,hf0,hfgrad,hg,hcov⟩ := hc a ha
  let Φ : Plane → Cover := fun y ↦ a+normalGraph (N a) f y
  have hΦ0 : Φ 0=a := by
    simp only [Φ,normalGraph,hf0,zero_smul,add_zero]
    have he : normalPlaneEmbedding (N a) 0=0 := norm_eq_zero.mp (by rw [normalPlaneEmbedding_norm,norm_zero])
    rw [he,add_zero]
  have hΦ : Differentiable ℝ Φ := fun y ↦
    (normalGraph_hasFDerivAt (n := N a) (hf.differentiable (by simp) y)).differentiableAt.const_add a
  let F : Plane → Cover := fun y ↦ sibling_axialProjection v (Φ y)-H⁻¹ • N (Φ y)
  have hF : Differentiable ℝ F :=
    ((sibling_axialProjection v).differentiable.comp hΦ).sub
      (((hN.differentiable (by simp)).comp hΦ).const_smul H⁻¹)
  obtain ⟨r,hr,hgr⟩ := Metric.mem_nhds_iff.mp hg
  have hd : ∀ y∈Metric.ball (0 : Plane) r,fderiv ℝ F y=0 := by
    intro y hy
    have hmem : quotientMap (Φ y)∈B := (hgr hy).2.1
    have hnorm : N (Φ y)=graphSlopeNormal (N a) (gradient f y) := (hgr hy).1
    have ht : ∀ u : Plane,⟪N (Φ y),fderiv ℝ Φ y u⟫=0 := by
      intro u
      rw [hnorm]
      have he : fderiv ℝ Φ y=fderiv ℝ (normalGraph (N a) f) y :=
        fderiv_const_add a
      rw [he]
      exact graphSlopeNormal_inner_fderiv hn hf y u
    have he := (((sibling_axialProjection v).hasFDerivAt.comp y (hΦ y).hasFDerivAt).sub
      (((hN.differentiable (by simp) (Φ y)).hasFDerivAt.comp y
        (hΦ y).hasFDerivAt).const_smul H⁻¹)).fderiv
    change fderiv ℝ F y=_ at he
    rw [he]
    ext u : 1
    simp only [sub_apply,ContinuousLinearMap.comp_apply,smul_apply,zero_apply]
    rw [hs (Φ y) hmem _ (ht u),smul_smul,inv_mul_cancel₀ hH,one_smul,sub_self]
  have hconst (y : Plane) (hy : y∈Metric.ball (0 : Plane) r) : F y=F 0 :=
    (convex_ball (0 : Plane) r).is_const_of_fderivWithin_eq_zero hF.differentiableOn
      (fun z hz ↦ by rw [fderivWithin_of_isOpen Metric.isOpen_ball hz]; exact hd z hz)
      hy (Metric.mem_ball_self hr)
  have hct : Tendsto (normalPlaneCoordinates (N a)) (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
    simpa only [map_zero] using (normalPlaneCoordinates (N a)).continuous.tendsto (0 : Cover)
  filter_upwards [hcov,hct.eventually (Metric.ball_mem_nhds (0 : Plane) hr)] with w hw hy hmem
  have he : Φ (normalPlaneCoordinates (N a) w)=a+w := by
    dsimp only [Φ]
    rw [hw.mp hmem]
  have hh := hconst _ hy
  simpa only [F,he,hΦ0] using hh

theorem isMinimizerAt_zero_component_local_center {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {H : ℝ} (hH : H≠0)
    (hb : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
    {v : Cover} (hv : ‖v‖=1)
    (hz : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ⟪v,N x⟫=0)
    {a : Cover} (ha : quotientMap a∈frontier (openRepresentative E)) :
    ∀ᶠ w in 𝓝 (0 : Cover),quotientMap (a+w)∈frontier (openRepresentative E) →
      sibling_axialProjection v (a+w)-H⁻¹ • N (a+w)=sibling_axialProjection v a-H⁻¹ • N a := by
  exact normalizedCMCCharts_axial_local_center
    (isMinimizerAt_hasNormalizedCMCCharts hV hE hmin hμ hN hp hae hb) hN hH
    (fun a ha w hw ↦ isMinimizerAt_zero_component_shape hV hE hmin hμ hN hp hae hb hv hz ha hw) ha

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialCylinder (v c : Cover) (r : ℝ) : Set Cover :=
  {x | ‖sibling_axialProjection v x-c‖=r}

lemma sibling_axialProjection_inner {v n : Cover} (hnv : ⟪n,v⟫=0) (w : Cover) :
    ⟪n,sibling_axialProjection v w⟫=⟪n,w⟫ := by
  rw [sibling_axialProjection_apply,inner_sub_right,real_inner_smul_right,hnv,mul_zero,sub_zero]

lemma axial_normal_squared_distance_difference {n v : Cover} (hn : ‖n‖=1)
    (hnv : ⟪n,v⟫=0) (g : Plane → ℝ) (c w : Cover) :
    ‖sibling_axialProjection v w-c‖^2-
      ‖sibling_axialProjection v (normalGraph n g (normalPlaneCoordinates n w))-c‖^2=
      (⟪n,w⟫-g (normalPlaneCoordinates n w))*
        (⟪n,w⟫+g (normalPlaneCoordinates n w)-2*⟪n,c⟫) := by
  let q := normalPlaneEmbedding n (normalPlaneCoordinates n w)
  have hq : ⟪n,sibling_axialProjection v q⟫=0 := by
    rw [sibling_axialProjection_inner hnv]
    exact normalPlaneEmbedding_inner hn _
  have hvn : ⟪v,n⟫=0 := by simpa only [real_inner_comm] using hnv
  have hw : w=q+⟪n,w⟫ • n := (normalPlaneCoordinates_reconstruct hn w).symm
  have hg : normalGraph n g (normalPlaneCoordinates n w)=q+g (normalPlaneCoordinates n w) • n := rfl
  rw [hg,map_add,map_smul,axialProjection_fixed hvn]
  conv_lhs => lhs; rw [hw,map_add,map_smul,axialProjection_fixed hvn]
  simp only [norm_sub_sq_real,norm_add_sq_real,real_inner_smul_left,
    real_inner_smul_right,inner_add_left,norm_smul,Real.norm_eq_abs,
    sq_abs,hn,mul_one]
  rw [←real_inner_comm (sibling_axialProjection v q) n,hq]
  ring

lemma sibling_local_graph_cylinder_iff {n v : Cover} (hn : ‖n‖=1) (hnv : ⟪n,v⟫=0)
    {g : Plane → ℝ} (hg : Continuous g) (hg0 : g 0=0) {c : Cover} {r : ℝ}
    (hc : ⟪n,c⟫≠0)
    (hs : ∀ᶠ y in 𝓝 (0 : Plane),normalGraph n g y∈axialCylinder v c r) :
    ∀ᶠ w in 𝓝 (0 : Cover),
      (normalGraph n g (normalPlaneCoordinates n w)=w ↔ w∈axialCylinder v c r) := by
  have hct : Tendsto (normalPlaneCoordinates n) (𝓝 (0 : Cover)) (𝓝 (0 : Plane)) := by
    simpa only [map_zero] using (normalPlaneCoordinates n).continuous.tendsto (0 : Cover)
  have hnon : ∀ᶠ w in 𝓝 (0 : Cover),
      ⟪n,w⟫+g (normalPlaneCoordinates n w)-2*⟪n,c⟫≠0 := by
    have ht : ContinuousAt (fun w : Cover ↦ ⟪n,w⟫+g (normalPlaneCoordinates n w)-2*⟪n,c⟫) 0 := by fun_prop
    apply ht.eventually_ne
    simp only [inner_zero_right,map_zero,hg0,zero_add,zero_sub,neg_ne_zero,mul_ne_zero_iff]
    exact ⟨by norm_num,hc⟩
  filter_upwards [hct.eventually hs,hnon] with w hw hnon
  constructor
  · intro he; rwa [←he]
  · intro hws
    have he : ‖sibling_axialProjection v w-c‖^2-
        ‖sibling_axialProjection v (normalGraph n g (normalPlaneCoordinates n w))-c‖^2=0 := by
      rw [show ‖sibling_axialProjection v w-c‖=r from hws,
        show ‖sibling_axialProjection v (normalGraph n g (normalPlaneCoordinates n w))-c‖=r from hw,sub_self]
    rw [axial_normal_squared_distance_difference hn hnv,mul_eq_zero] at he
    exact (normalGraph_coordinates_eq_iff hn g w).mpr
      ((sub_eq_zero.mp (he.resolve_right hnon)).symm)

theorem isMinimizerAt_zero_component_local_cylinder {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {H : ℝ} (hH : H≠0)
    (hb : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
      (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H)
    {v : Cover} (hv : ‖v‖=1)
    (hz : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ⟪v,N x⟫=0)
    {a : Cover} (ha : quotientMap a∈frontier (openRepresentative E)) :
    ∀ᶠ w in 𝓝 (0 : Cover),
      (quotientMap (a+w)∈frontier (openRepresentative E) ↔
        a+w∈axialCylinder v (sibling_axialProjection v a-H⁻¹ • N a) |H⁻¹|) ∧
      (quotientMap (a+w)∈frontier (openRepresentative E) →
        sibling_axialProjection v (a+w)-H⁻¹ • N (a+w)=sibling_axialProjection v a-H⁻¹ • N a) := by
  have hcharts := isMinimizerAt_hasNormalizedCMCCharts hV hE hmin hμ hN hp hae hb
  obtain ⟨hn,f,hf,hf0,hfgrad,hg,hcov⟩ := hcharts a ha
  have hloc := isMinimizerAt_zero_component_local_center hV hE hmin hμ hN hp hae hH hb hv hz ha
  let c : Cover := -H⁻¹ • N a
  have hcn : ⟪N a,c⟫≠0 := by
    dsimp only [c]
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
    exact neg_ne_zero.mpr (inv_ne_zero hH)
  have hnv : ⟪N a,v⟫=0 := by simpa only [real_inner_comm] using hz a ha
  have hgzero : normalGraph (N a) f 0=0 := by
    simp only [normalGraph,hf0,zero_smul,add_zero]
    exact norm_eq_zero.mp (by rw [normalPlaneEmbedding_norm,norm_zero])
  have hgt : Tendsto (normalGraph (N a) f) (𝓝 (0 : Plane)) (𝓝 (0 : Cover)) := by
    rw [←hgzero]
    exact (((normalPlaneLinearIsometry (N a)).continuous).add (hf.continuous.smul continuous_const)).tendsto 0
  have hcs : ∀ᶠ y in 𝓝 (0 : Plane),normalGraph (N a) f y∈axialCylinder v c |H⁻¹| := by
    filter_upwards [hg,hgt.eventually hloc] with y hy hyloc
    have he := hyloc hy.2.1
    have he' : sibling_axialProjection v (normalGraph (N a) f y)-c=H⁻¹ • N (a+normalGraph (N a) f y) := by
      rw [map_add] at he
      dsimp only [c]
      linear_combination (norm := module) he
    change ‖sibling_axialProjection v (normalGraph (N a) f y)-c‖=|H⁻¹|
    rw [he',norm_smul,Real.norm_eq_abs,(hb _ hy.2.1).1.self_of_nhds,mul_one]
  have hiff := sibling_local_graph_cylinder_iff hn hnv hf.continuous hf0 hcn hcs
  filter_upwards [hcov,hiff,hloc] with w hw hi hl
  refine ⟨?_,hl⟩
  rw [hw,hi]
  change (‖sibling_axialProjection v w-c‖=|H⁻¹| ↔
    ‖sibling_axialProjection v (a+w)-(sibling_axialProjection v a-H⁻¹ • N a)‖=|H⁻¹|)
  rw [map_add]
  have he : sibling_axialProjection v a+sibling_axialProjection v w-(sibling_axialProjection v a-H⁻¹ • N a)=
      sibling_axialProjection v w-c := by dsimp only [c]; module
  rw [he]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

end CubicTorus
end
end
end

end OAI
