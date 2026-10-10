import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Finset.Basic

namespace OAI

/-! Homeomorphisms supported in pairwise disjoint sets can be assembled
without disturbing their prescribed restrictions. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

lemma _root_.OAI.Homeomorph.mapsTo_of_fixes_compl
    {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) {D : Set X}
    (hf : ∀ x ∉ D, f x=x) : MapsTo f D D := by
  intro x hx
  by_contra hfx
  have he : f (f x)=f x := hf (f x) hfx
  have hx' : f x=x := f.injective he
  exact hfx (hx'.symm ▸ hx)

lemma finite_supported_homeomorphs
    {X I : Type*} [TopologicalSpace X] (s : Finset I)
    (D : I → Set X) (F : I → X ≃ₜ X)
    (hd : (s : Set I).Pairwise (fun i j => Disjoint (D i) (D j)))
    (hsupport : ∀ i ∈ s, ∀ x ∉ D i, F i x=x) :
    ∃ H : X ≃ₜ X,
      (∀ x ∉ ⋃ i ∈ s, D i, H x=x) ∧
      ∀ i ∈ s, ∀ x ∈ D i, H x=F i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨Homeomorph.refl X,fun _ _ => rfl,by simp⟩
  | @insert i s his ih =>
    have hd' : (s : Set I).Pairwise (fun i j => Disjoint (D i) (D j)) :=
      hd.mono (by intro j hj; exact Finset.mem_insert_of_mem hj)
    obtain ⟨H,hHout,hH⟩ := ih hd' (fun j hj => hsupport j (Finset.mem_insert_of_mem hj))
    refine ⟨H.trans (F i),?_,?_⟩
    · intro x hx
      have hxi : x ∉ D i := fun h => hx (mem_iUnion₂.mpr ⟨i,Finset.mem_insert_self _ _,h⟩)
      have hxs : x ∉ ⋃ j ∈ s, D j := by
        intro h
        obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp h
        exact hx (mem_iUnion₂.mpr ⟨j,Finset.mem_insert_of_mem hj,hxj⟩)
      change F i (H x)=x
      rw [hHout x hxs,hsupport i (Finset.mem_insert_self _ _) x hxi]
    · intro j hj x hx
      rcases Finset.mem_insert.mp hj with he | hjs
      · subst j
        have hxs : x ∉ ⋃ j ∈ s, D j := by
          intro h
          obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp h
          exact Set.disjoint_left.mp (hd (Finset.mem_insert_self _ _)
            (Finset.mem_insert_of_mem hj) (fun he => his (he.symm ▸ hj))) hx hxj
        change F i (H x)=F i x
        rw [hHout x hxs]
      · have hHx : H x ∈ D j := by
          rw [hH j hjs x hx]
          exact _root_.OAI.Homeomorph.mapsTo_of_fixes_compl (F j)
            (hsupport j (Finset.mem_insert_of_mem hjs)) hx
        have hHxi : H x ∉ D i := by
          intro hi
          exact Set.disjoint_left.mp (hd (Finset.mem_insert_of_mem hjs)
            (Finset.mem_insert_self _ _) (fun he => his (he ▸ hjs))) hHx hi
        change F i (H x)=F j x
        rw [hsupport i (Finset.mem_insert_self _ _) (H x) hHxi,hH j hjs x hx]

end CircleDomainRigidity

end

end OAI
