import Mathlib
import OAI.Probability.SLELocalization.CommonClocks

namespace OAI


/-! Conformal localization and Past Obstacle estimates. -/

noncomputable section
open Set Filter Topology
open scoped Topology
namespace SLEExactGauge

lemma locallyConnected_sum {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyConnectedSpace X] [LocallyConnectedSpace Y] : LocallyConnectedSpace (X ⊕ Y) := by
  rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
  rintro (x | y) U hU
  · have hp : Sum.inl ⁻¹' U ∈ 𝓝 x := continuous_inl.continuousAt.preimage_mem_nhds hU
    obtain ⟨V,hVU,hVo,hxV,hVc⟩ := locallyConnectedSpace_iff_subsets_isOpen_isConnected.1
      (inferInstance : LocallyConnectedSpace X) x _ hp
    refine ⟨Sum.inl '' V,?_,isOpenMap_inl _ hVo,mem_image_of_mem _ hxV,
      hVc.image _ continuous_inl.continuousOn⟩
    rintro _ ⟨v,hv,rfl⟩
    exact hVU hv
  · have hp : Sum.inr ⁻¹' U ∈ 𝓝 y := continuous_inr.continuousAt.preimage_mem_nhds hU
    obtain ⟨V,hVU,hVo,hyV,hVc⟩ := locallyConnectedSpace_iff_subsets_isOpen_isConnected.1
      (inferInstance : LocallyConnectedSpace Y) y _ hp
    refine ⟨Sum.inr '' V,?_,isOpenMap_inr _ hVo,mem_image_of_mem _ hyV,
      hVc.image _ continuous_inr.continuousOn⟩
    rintro _ ⟨v,hv,rfl⟩
    exact hVU hv

lemma locallyConnected_closed_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    [LocallyConnectedSpace A] [LocallyConnectedSpace B] :
    LocallyConnectedSpace (↑(A ∪ B) : Type _) := by
  have := locallyConnected_sum (X := A) (Y := B)
  let a : A → ↑(A ∪ B) := fun x => ⟨x,Or.inl x.property⟩
  let b : B → ↑(A ∪ B) := fun x => ⟨x,Or.inr x.property⟩
  have hca : Continuous a := continuous_subtype_val.subtype_mk _
  have hcb : Continuous b := continuous_subtype_val.subtype_mk _
  have hcla : IsClosedMap a := by
    intro S hS
    have he : a '' S = Subtype.val ⁻¹' (Subtype.val '' S) := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩; exact ⟨y,hy,rfl⟩
      · rintro ⟨y,hy,he⟩; exact ⟨y,hy,Subtype.ext he⟩
    rw [he]
    exact (hA.isClosedEmbedding_subtypeVal.isClosedMap S hS).preimage continuous_subtype_val
  have hclb : IsClosedMap b := by
    intro S hS
    have he : b '' S = Subtype.val ⁻¹' (Subtype.val '' S) := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩; exact ⟨y,hy,rfl⟩
      · rintro ⟨y,hy,he⟩; exact ⟨y,hy,Subtype.ext he⟩
    rw [he]
    exact (hB.isClosedEmbedding_subtypeVal.isClosedMap S hS).preimage continuous_subtype_val
  have hsurj : Function.Surjective (Sum.elim a b) := by
    intro x
    rcases x.property with ha | hb
    · exact ⟨Sum.inl ⟨x,ha⟩,rfl⟩
    · exact ⟨Sum.inr ⟨x,hb⟩,rfl⟩
  exact ((hcla.sumElim hclb).isQuotientMap (hca.sumElim hcb) hsurj).isCoinducing.locallyConnectedSpace

lemma lower_halfPlane_locallyConnected : LocallyConnectedSpace (↑(halfPlaneᶜ) : Type) := by
  let π : ℂ → ↑(halfPlaneᶜ) := fun z => ⟨⟨z.re,min z.im 0⟩,by
    change ¬ 0 < min z.im 0
    exact not_lt_of_ge (min_le_right _ _)⟩
  have hc : Continuous π := by
    apply Continuous.subtype_mk
    change Continuous (fun z : ℂ => Complex.mk z.re (min z.im 0))
    have hh : Continuous (fun z : ℂ => (z.re:ℂ)+((min z.im 0:ℝ):ℂ)*Complex.I) := by fun_prop
    convert hh using 1
    funext z
    apply Complex.ext <;> simp
  have hr (z : ↑(halfPlaneᶜ)) : π z = z := by
    have hz : z.val.im ≤ 0 := le_of_not_gt z.property
    apply Subtype.ext
    apply Complex.ext <;> simp [π,min_eq_left hz]
  have hq : IsQuotientMap π := by
    refine ⟨.of_isOpen_preimage_iff_isOpen (fun S => ?_),?_⟩
    · constructor
      · intro hS
        have hh := hS.preimage (continuous_subtype_val : Continuous (Subtype.val : ↑(halfPlaneᶜ) → ℂ))
        have he : Subtype.val ⁻¹' (π ⁻¹' S) = S := by ext z; simp only [mem_preimage,hr]
        rwa [he] at hh
      · intro hS
        exact hS.preimage hc
    · intro z
      exact ⟨z,hr z⟩
  exact hq.isCoinducing.locallyConnectedSpace

end SLEExactGauge

end

/-! Conformal localization and Past Trace Continuum estimates. -/

noncomputable section
open Set Filter Topology
open scoped Topology
namespace SLEExactGauge

theorem past_trace_continuum {γ : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hc : ContinuousOn γ (Icc 0 T)) :
    IsCompact (localizationSegment γ 0 T) ∧ IsConnected (localizationSegment γ 0 T) ∧
      LocallyConnectedSpace (localizationSegment γ 0 T) := by
  have : LocallyConnectedSpace (Icc (0:ℝ) T) :=
    (isQuotientMap_projIcc (a := (0:ℝ)) (b := T) (h := hT)).isCoinducing.locallyConnectedSpace
  let F : Icc (0:ℝ) T → localizationSegment γ 0 T :=
    fun t => ⟨γ t, ⟨t,t.property,rfl⟩⟩
  have hFc : Continuous F :=
    (continuousOn_iff_continuous_domRestrict.1 hc).subtype_mk _
  have hFs : Function.Surjective F := by
    rintro ⟨z,t,ht,rfl⟩
    exact ⟨⟨t,ht⟩,rfl⟩
  refine ⟨isCompact_Icc.image_of_continuousOn hc,
    (isConnected_Icc hT).image γ hc,?_⟩
  exact (IsQuotientMap.of_surjective_continuous hFs hFc).isCoinducing.locallyConnectedSpace

theorem past_obstacle_locallyConnected {γ : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hc : ContinuousOn γ (Icc 0 T)) :
    LocallyConnectedSpace (↑(halfPlaneᶜ ∪ localizationSegment γ 0 T) : Type) := by
  have := lower_halfPlane_locallyConnected
  have := (past_trace_continuum hT hc).2.2
  exact locallyConnected_closed_union halfPlane_open.isClosed_compl
    (past_trace_continuum hT hc).1.isClosed

end SLEExactGauge

end

end OAI
