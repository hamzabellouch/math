import Mathlib

namespace OAI

section
section
section
noncomputable section
namespace CannonFiniteCarrier
open Set Topology Relation

lemma closed_cover_reflTransGen {Y ι : Type*} [TopologicalSpace Y] [Finite ι]
    (K : ι → Set Y) (hK : ∀ i,IsClosed (K i)) (S : Set Y)
    (hS : IsPreconnected S) (hcover : S⊆⋃i,K i)
    (i j : ι) (hi : (S∩K i).Nonempty) (hj : (S∩K j).Nonempty) :
    ReflTransGen (fun a b=> (S∩K a∩K b).Nonempty) i j := by
  classical
  by_contra hij
  let R := fun a b=> (S∩K a∩K b).Nonempty
  let T : Set ι := {k | ReflTransGen R i k}
  let U : Set Y := ⋃ k∈T,K k
  let V : Set Y := ⋃ k∈Tᶜ,K k
  have hsplit : (⋃ k,K k)=U∪V := iSup_split K (·∈T)
  have hcU : IsClosed U := isClosed_iUnion_of_finite fun k=>isClosed_iUnion_of_finite fun _=>hK k
  have hcV : IsClosed V := isClosed_iUnion_of_finite fun k=>isClosed_iUnion_of_finite fun _=>hK k
  have hiT : i∈T := ReflTransGen.refl
  obtain ⟨a,haS,hai⟩:=hi
  obtain ⟨b,hbS,hbj⟩:=hj
  have haU : (S∩U).Nonempty := ⟨a,haS,mem_iUnion₂_of_mem hiT hai⟩
  have hbV : (S∩V).Nonempty := ⟨b,hbS,mem_iUnion₂_of_mem hij hbj⟩
  obtain ⟨x,hxS,hxU,hxV⟩:=isPreconnected_closed_iff.mp hS U V hcU hcV
    (hcover.trans hsplit.le) haU hbV
  obtain ⟨k,hk,hxk⟩:=mem_iUnion₂.mp hxU
  obtain ⟨l,hl,hxl⟩:=mem_iUnion₂.mp hxV
  exact hl (hk.tail ⟨x,⟨hxS,hxk⟩,hxl⟩)

theorem connected_carrier {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Finite ι] (A : ι → Set X) (K : ι → Set Y)
    (hA : ∀ i,IsPreconnected (A i)) (hK : ∀ i,IsClosed (K i))
    (S : Set Y) (hS : IsPreconnected S) (hcover : S⊆⋃i,K i)
    (hmeet : ∀ i j,(S∩K i∩K j).Nonempty → (A i∩A j).Nonempty) :
    IsPreconnected (⋃ (i : {i : ι // (S∩K i).Nonempty}),A i.val) := by
  classical
  apply IsPreconnected.iUnion_of_reflTransGen (s:=fun i : {i : ι // (S∩K i).Nonempty}=>A i.val) (fun i=>hA i.val)
  intro i j
  have hreach := closed_cover_reflTransGen (fun i : {i : ι // (S∩K i).Nonempty}=>K i.val)
    (fun i=>hK i.val) S hS (by
      intro y hy
      obtain ⟨k,hk⟩:=mem_iUnion.mp (hcover hy)
      exact mem_iUnion.mpr ⟨⟨k,⟨y,hy,hk⟩⟩,hk⟩) i j i.property j.property
  exact ReflTransGen.mono (r:=fun a b : {i : ι // (S∩K i).Nonempty}=>(S∩K a.val∩K b.val).Nonempty)
    (fun a b hab=>hmeet a.val b.val hab) i j hreach

lemma preimage_subset_carrier {X Y ι : Type*} (A : ι → Set X) (K : ι → Set Y)
    (f : X → Y) (hcover : ∀ x,∃ i,x∈A i) (hf : ∀ i,MapsTo f (A i) (K i)) (S : Set Y) :
    f ⁻¹' S⊆⋃(i : {i : ι // (S∩K i).Nonempty}),A i.val := by
  intro x hx
  obtain ⟨i,hi⟩:=hcover x
  exact mem_iUnion.mpr ⟨⟨i,⟨f x,hx,hf i hi⟩⟩,hi⟩

lemma path_in_open_enlargement {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] {A U : Set X} (hA : IsPreconnected A)
    (hU : IsOpen U) (hAU : A⊆U) {x y : X} (hx : x∈A) (hy : y∈A) :
    ∃ γ : Path x y,∀ t,γ t∈U := by
  have hsub := hA.subset_connectedComponentIn hx hAU
  have hc : IsConnected (connectedComponentIn U x) :=
    isConnected_connectedComponentIn_iff.mpr (hAU hx)
  have hp := hU.connectedComponentIn.isConnected_iff_isPathConnected.mp hc
  have hj := hp.joinedIn x (hsub hx) y (hsub hy)
  exact ⟨hj.somePath,fun t=>connectedComponentIn_subset U x (hj.somePath_mem t)⟩
end CannonFiniteCarrier

end
end
end
end

end OAI
