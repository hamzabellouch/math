import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.FinitePrimitiveResolution

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteCutResolution

theorem finite_cut_resolution {a : ℕ} {κ : Type*} [Finite κ] (R : κ → polygonAlgebra a) :
    ∃ S : Finset (Fin 4 × CutRing), ∀ i,
      ResolvedBy (fun p : S => halfPlane a p.val.1 p.val.2) (R i).val := by
  classical
  let _ := Fintype.ofFinite κ
  have hgen : {U : Set (GenericSquare a) | ∃ j z, U=halfPlane a j z}=
      Set.range (fun p : Fin 4 × CutRing => halfPlane a p.1 p.2) := by
    ext U
    constructor
    · rintro ⟨j,z,rfl⟩; exact ⟨(j,z),rfl⟩
    · rintro ⟨⟨j,z⟩,rfl⟩; exact ⟨j,z,rfl⟩
  have h (i : κ) : ∃ S : Finset (Fin 4 × CutRing),
      ResolvedBy (fun p : S => halfPlane a p.val.1 p.val.2) (R i).val := by
    apply finite_resolving_subfamily (fun p : Fin 4 × CutRing => halfPlane a p.1 p.2)
    have hp := (R i).property
    change (R i).val ∈ BooleanSubalgebra.closure _ at hp
    rwa [hgen] at hp
  choose S hS using h
  refine ⟨Finset.univ.biUnion S,fun i x y hh => ?_⟩
  apply hS i x y
  intro p
  exact hh ⟨p.val,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,p.property⟩⟩

theorem finite_cut_resolution_extend {a : ℕ} {κ η : Type*} [Finite κ] [Finite η]
    (R : κ → polygonAlgebra a) (j : η → Fin 4) (c : η → CutRing) :
    ∃ S : Finset (Fin 4 × CutRing),
      (∀ i, ResolvedBy (fun p : S => halfPlane a p.val.1 p.val.2) (R i).val) ∧
      ∀ e, (j e,c e) ∈ S := by
  classical
  let _ := Fintype.ofFinite η
  obtain ⟨S,hS⟩ := finite_cut_resolution R
  refine ⟨S ∪ Finset.univ.image (fun e => (j e,c e)),?_,?_⟩
  · intro i x y hh
    exact hS i x y (fun p => hh ⟨p.val,Finset.mem_union_left _ p.property⟩)
  · intro e
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e,Finset.mem_univ e,rfl⟩)

end FiniteCutResolution

end SimpleAmenable
end
end

end OAI
