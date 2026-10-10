import Mathlib

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

namespace CannonFiniteFaces

theorem finite_components_of_dense_regions {X : Type*} [TopologicalSpace X]
    [LocallyConnectedSpace X] {V : Set X} (hV : IsOpen V)
    {ι : Type*} [Finite ι] (S : ι → Set X)
    (hS : ∀ i, S i⊆V) (hc : ∀ i, IsPreconnected (S i))
    (hd : Dense (⋃ i, S i)) : Finite (ConnectedComponents V) := by
  classical
  let _ : LocallyConnectedSpace V := hV.locallyConnectedSpace
  let f : V → ConnectedComponents V := ConnectedComponents.mk
  have hf : Continuous f := ConnectedComponents.continuous_coe
  let U : ι → Set V := fun i => Subtype.val ⁻¹' S i
  have hUi (i : ι) : IsPreconnected (U i) := by
    apply IsInducing.subtypeVal.isPreconnected_image.mp
    have he : Subtype.val '' U i=S i := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x,hS i hx⟩,hx,rfl⟩
    rw [he]
    exact hc i
  have hfi (i : ι) : (f '' U i).Finite :=
    ((hUi i).image f hf.continuousOn).subsingleton.finite
  have hfin : (f '' (⋃ i, U i)).Finite := by
    rw [image_iUnion]
    exact finite_iUnion hfi
  have hden : Dense (⋃ i, U i) := by
    have hh := hd.preimage hV.isOpenMap_subtype_val
    simpa only [preimage_iUnion] using hh
  have hdenf : Dense (f '' (⋃ i, U i)) :=
    ConnectedComponents.surjective_coe.denseRange.dense_image hf hden
  have he : f '' (⋃ i, U i)=univ := hfin.isClosed.closure_eq.symm.trans hdenf.closure_eq
  exact finite_univ_iff.mp (he ▸ hfin)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma nonzero_functional_surjective (f : E →L[ℝ] ℝ) (hf : f≠0) :
    Function.Surjective f := by
  obtain ⟨v,hv⟩ : ∃ v, f v≠0 := by
    by_contra hn
    push Not at hn
    apply hf
    ext v
    exact hn v
  intro y
  refine ⟨(y/f v) • v,?_⟩
  simp only [map_smul,smul_eq_mul]
  exact div_mul_cancel₀ y hv

theorem hyperplane_chambers {ι : Type*} [Finite ι]
    (f : ι → E →L[ℝ] ℝ) (c : ι → ℝ) (hf : ∀ i, f i≠0) :
    ∃ S : (ι → Bool) → Set E,
      (∀ s, Convex ℝ (S s)) ∧ Dense (⋃ s, S s) ∧
      (∀ s, S s⊆{x | ∀ i, f i x≠c i}) := by
  classical
  let S : (ι → Bool) → Set E := fun s => ⋂ i,
    if s i=true then {x | c i<f i x} else {x | f i x<c i}
  have hconv (s : ι → Bool) : Convex ℝ (S s) := by
    apply convex_iInter
    intro i
    split_ifs
    · exact (convex_Ioi (c i)).linear_preimage (f i).toLinearMap
    · exact (convex_Iio (c i)).linear_preimage (f i).toLinearMap
  have heq : (⋃ s, S s)={x | ∀ i, f i x≠c i} := by
    ext x
    constructor
    · intro hx i
      obtain ⟨s,hs⟩ := mem_iUnion.mp hx
      have hh := mem_iInter.mp hs i
      split_ifs at hh with h
      · exact ne_of_gt hh
      · exact ne_of_lt hh
    · intro hx
      refine mem_iUnion.mpr ⟨fun i => decide (c i<f i x),?_⟩
      apply mem_iInter.mpr
      intro i
      dsimp
      split_ifs with hi
      · exact of_decide_eq_true hi
      · have hh : ¬c i<f i x := by simpa using hi
        exact lt_of_le_of_ne (le_of_not_gt hh) (hx i)
  have hopen (i : ι) : IsOpen {x | f i x≠c i} :=
    isOpen_compl_singleton.preimage (f i).continuous
  have hdense (i : ι) : Dense {x | f i x≠c i} :=
    (dense_compl_singleton (c i)).preimage
      ((f i).isOpenMap (nonzero_functional_surjective (f i) (hf i)))
  have hden : Dense {x | ∀ i, f i x≠c i} := by
    have hh := dense_iInter_of_isOpen hopen hdense
    simpa only [mem_iInter,ofPred_forall] using hh
  refine ⟨S,hconv,heq ▸ hden,?_⟩
  intro s
  rw [←heq]
  exact subset_iUnion S s

theorem finite_components_hyperplane_support {K : Set E} (hK : IsClosed K)
    {ι : Type*} [Finite ι] (f : ι → E →L[ℝ] ℝ) (c : ι → ℝ)
    (hf : ∀ i, f i≠0) (hs : K⊆⋃ i, {x | f i x=c i}) :
    Finite (ConnectedComponents (Kᶜ : Set E)) := by
  obtain ⟨S,hconv,hden,havoid⟩ := hyperplane_chambers f c hf
  apply finite_components_of_dense_regions hK.isOpen_compl S _
    (fun s => (hconv s).isPreconnected) hden
  intro s x hx hxK
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hs hxK)
  exact havoid s hx i hi

abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem segment_supporting_line (a b : Plane) :
    ∃ f : Plane →L[ℝ] ℝ, f≠0 ∧ segment ℝ a b⊆{x | f x=f a} := by
  classical
  let x₀ : Plane →L[ℝ] ℝ := EuclideanSpace.proj 0
  let x₁ : Plane →L[ℝ] ℝ := EuclideanSpace.proj 1
  by_cases hd : b 0=a 0
  · refine ⟨x₀,?_,?_⟩
    · intro h
      have hh := congrArg (fun f : Plane →L[ℝ] ℝ => f (EuclideanSpace.single 0 1)) h
      norm_num [x₀] at hh
    · have hcv : Convex ℝ {x | x₀ x=x₀ a} :=
        (convex_singleton (x₀ a)).linear_preimage x₀.toLinearMap
      exact hcv.segment_subset rfl hd
  · let f := x₁-((b 1-a 1)/(b 0-a 0)) • x₀
    refine ⟨f,?_,?_⟩
    · intro h
      have hh := congrArg (fun f : Plane →L[ℝ] ℝ => f (EuclideanSpace.single 1 1)) h
      norm_num [f,x₀,x₁,PiLp.single_apply] at hh
    · have hab : f b=f a := by
        change b 1-((b 1-a 1)/(b 0-a 0))*b 0=a 1-((b 1-a 1)/(b 0-a 0))*a 0
        have hn : b 0-a 0≠0 := sub_ne_zero.mpr hd
        field_simp [hn]
        ring
      have hcv : Convex ℝ {x | f x=f a} :=
        (convex_singleton (f a)).linear_preimage f.toLinearMap
      exact hcv.segment_subset rfl hab

theorem finite_components_segment_support {K : Set Plane} (hK : IsClosed K)
    (P : Finset (Plane×Plane)) (hs : K⊆⋃ p∈P, segment ℝ p.1 p.2) :
    Finite (ConnectedComponents (Kᶜ : Set Plane)) := by
  classical
  choose f hf hseg using fun p : P => segment_supporting_line p.val.1 p.val.2
  apply finite_components_hyperplane_support hK f (fun p => f p p.val.1) hf
  intro x hx
  obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp (hs hx)
  exact mem_iUnion.mpr ⟨⟨p,hp⟩,hseg ⟨p,hp⟩ hxp⟩

theorem finite_components_chart_support {X : Type*} [TopologicalSpace X]
    [T2Space X] [PreconnectedSpace X] [LocallyConnectedSpace X]
    (e : Plane → X) (he : IsOpenEmbedding e) (p : X) (heR : range e={p}ᶜ)
    {K : Set X} (hK : IsClosed K) (P : Finset (Plane×Plane))
    (hs : K⊆e '' (⋃ q∈P, segment ℝ q.1 q.2)) :
    Finite (ConnectedComponents (Kᶜ : Set X)) := by
  classical
  choose f hf hseg using fun q : P => segment_supporting_line q.val.1 q.val.2
  obtain ⟨S,hconv,hden,havoid⟩ := hyperplane_chambers f (fun q => f q q.val.1) hf
  have hsub (s : P → Bool) : e '' S s⊆Kᶜ := by
    rintro _ ⟨x,hx,rfl⟩ hxK
    obtain ⟨y,hy,hexy⟩ := hs hxK
    have hey : y=x := he.injective hexy
    subst y
    obtain ⟨q,hq,hxq⟩ := mem_iUnion₂.mp hy
    exact havoid s hx ⟨q,hq⟩ (hseg ⟨q,hq⟩ hxq)
  have hde : DenseRange e := by
    change Dense (range e)
    rw [heR,dense_compl_singleton_iff_not_open]
    intro hopen
    have hall : ({p} : Set X)=univ :=
      (show IsClopen ({p} : Set X) from ⟨isClosed_singleton,hopen⟩).eq_univ
        (singleton_nonempty p)
    have hep : e 0=p := mem_singleton_iff.mp (hall.symm ▸ mem_univ (e 0))
    have hn : e 0∈({p}ᶜ : Set X) := heR ▸ mem_range_self 0
    exact hn (mem_singleton_iff.mpr hep)
  apply finite_components_of_dense_regions hK.isOpen_compl (fun s => e '' S s)
    hsub (fun s => (hconv s).isPreconnected.image e he.continuous.continuousOn)
  rw [←image_iUnion]
  exact hde.dense_image he.continuous hden

end CannonFiniteFaces

end
end
end
end
end
end
end
end
end

end OAI
