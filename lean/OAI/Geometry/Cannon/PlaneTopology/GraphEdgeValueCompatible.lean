import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.Arc

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval

variable {ι : Type*} [Finite ι]

omit [Finite ι] in
lemma graph_edge_value_compatible (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j)) (z : ℂ → ℂ)
    {i j : ι} {s t : I} (hh : F i s=F j t) :
    Path.segment (z (F i 0)) (z (F i 1)) s =
      Path.segment (z (F j 0)) (z (F j 1)) t := by
  by_cases hij : i=j
  · subst j
    exact congrArg (Path.segment (z (F i 0)) (z (F i 1))) ((F i).injective hh)
  · obtain ⟨hs,ht⟩ := (hF hij).1 s t hh
    rcases hs with rfl|rfl <;> rcases ht with rfl|rfl
    · exact (Path.source _).trans ((congrArg z hh).trans (Path.source _).symm)
    · exact (Path.source _).trans ((congrArg z hh).trans (Path.target _).symm)
    · exact (Path.target _).trans ((congrArg z hh).trans (Path.source _).symm)
    · exact (Path.target _).trans ((congrArg z hh).trans (Path.target _).symm)

theorem compact_quotient_descent {A B C : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace C] [CompactSpace A] [T2Space B]
    (q : A → B) (hq : Function.Surjective q) (hqc : Continuous q)
    (b : A → C) (hb : Continuous b) (he : ∀ x y,q x=q y → b x=b y) :
    ∃ g : ContinuousMap B C,∀ x,g (q x)=b x := by
  let g : B → C := fun x=>b (Function.surjInv hq x)
  have hgb (a : A) : g (q a)=b a := he _ _ (Function.surjInv_eq hq (q a))
  have hquot : IsQuotientMap q := IsQuotientMap.of_surjective_continuous hq hqc
  refine ⟨⟨g,hquot.continuous_iff.mpr ?_⟩,hgb⟩
  have heq : g ∘ q=b := funext hgb
  rw [heq]
  exact hb

theorem realize_graph (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j)) (z : ℂ → ℂ) :
    ∃ g : C((⋃ i,range (F i) : Set ℂ),ℂ),
      ∀ i t,g ⟨F i t,mem_iUnion.mpr ⟨i,mem_range_self t⟩⟩=
        Path.segment (z (F i 0)) (z (F i 1)) t := by
  classical
  let S : Set ℂ := ⋃ i,range (F i)
  let q : (Σ _ : ι,I) → S := fun p=>⟨F p.1 p.2,mem_iUnion.mpr ⟨p.1,mem_range_self p.2⟩⟩
  have hq : Function.Surjective q := by
    rintro ⟨x,hx⟩
    obtain ⟨i,t,ht⟩:=mem_iUnion.mp hx
    exact ⟨⟨i,t⟩,Subtype.ext ht⟩
  have hqc : Continuous q := by
    apply Continuous.subtype_mk
    exact continuous_sigma_iff.mpr (fun i=>(F i).continuous)
  let b : (Σ _ : ι,I) → ℂ := fun p=>Path.segment (z (F p.1 0)) (z (F p.1 1)) p.2
  have hb : Continuous b := by
    apply continuous_sigma_iff.mpr
    intro i
    exact (Path.segment (z (F i 0)) (z (F i 1))).continuous
  have hbq : ∀ p r,q p=q r → b p=b r := by
    rintro ⟨i,s⟩ ⟨j,t⟩ he
    have hh : F i s=F j t := congrArg Subtype.val he
    change Path.segment (z (F i 0)) (z (F i 1)) s =
      Path.segment (z (F j 0)) (z (F j 1)) t
    exact graph_edge_value_compatible F hF z hh
  obtain ⟨g,hg⟩:=compact_quotient_descent q hq hqc b hb hbq
  exact ⟨g,fun i t=>hg ⟨i,t⟩⟩

theorem extend_graph (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j)) (z : ℂ → ℂ) :
    ∃ g : C(ℂ,ℂ),∀ i t,g (F i t)=Path.segment (z (F i 0)) (z (F i 1)) t := by
  obtain ⟨f,hf⟩:=realize_graph F hF z
  have hK : IsClosed (⋃ i,range (F i) : Set ℂ) :=
    isClosed_iUnion_of_finite (fun i=>(F i).compact_range.isClosed)
  let fr : C((⋃ i,range (F i) : Set ℂ),ℝ) := ⟨fun x=>(f x).re,Complex.continuous_re.comp f.continuous⟩
  let fi : C((⋃ i,range (F i) : Set ℂ),ℝ) := ⟨fun x=>(f x).im,Complex.continuous_im.comp f.continuous⟩
  obtain ⟨gr,hgr⟩:=fr.exists_extension' hK.isClosedEmbedding_subtypeVal
  obtain ⟨gi,hgi⟩:=fi.exists_extension' hK.isClosedEmbedding_subtypeVal
  refine ⟨⟨fun x=>⟨gr x,gi x⟩,by
    exact Complex.equivRealProdCLM.symm.continuous.comp (gr.continuous.prodMk gi.continuous)⟩,?_⟩
  intro i t
  have hr := congrFun hgr ⟨F i t,mem_iUnion.mpr ⟨i,mem_range_self t⟩⟩
  have hi := congrFun hgi ⟨F i t,mem_iUnion.mpr ⟨i,mem_range_self t⟩⟩
  apply Complex.ext
  · exact hr.trans (congrArg Complex.re (hf i t))
  · exact hi.trans (congrArg Complex.im (hf i t))
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
