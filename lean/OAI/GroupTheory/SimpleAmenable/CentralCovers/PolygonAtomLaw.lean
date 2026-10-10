import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.StarAtomLaw

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonAtomLaw
variable {a m : ℕ} {Ω : Type*}

@[simp] theorem PolygonLabelling.tableHom_single_mask [Fintype Ω] (v : PolygonLabelling a Ω)
    (ω : Ω) : v.tableHom.comp (sectorMask {ω}) = conditionalAlternatingHom (m := m) (v.fiber ω) := by
  classical
  ext s : 1
  change v.tableHom (sectorMask {ω} s) = conditionalAlternatingHom (v.fiber ω) s
  have he : sectorMask {ω} s = Pi.mulSingle ω s := by
    ext ν
    by_cases hh : ν=ω <;> simp [sectorMask,hh]
  rw [he,v.tableHom_single]

noncomputable def polygonPartitionLabelling (U : Ω → polygonAlgebra a)
    (hcover : ∀ p : GenericSquare a, ∃ i, p ∈ (U i).val)
    (hdisjoint : Pairwise fun i j => Disjoint (U i).val (U j).val) : PolygonLabelling a Ω where
  label p := (hcover p).choose
  fiber_mem i := by
    have he : {p | (hcover p).choose = i} = (U i).val := by
      ext p
      constructor
      · intro hp
        change (hcover p).choose = i at hp
        simpa only [hp] using (hcover p).choose_spec
      · intro hp
        by_contra hh
        exact Set.disjoint_left.mp (hdisjoint hh) (hcover p).choose_spec hp
    rw [he]
    exact (U i).property

theorem polygonPartitionLabelling_fiber (U : Ω → polygonAlgebra a)
    (hcover : ∀ p : GenericSquare a, ∃ i, p ∈ (U i).val)
    (hdisjoint : Pairwise fun i j => Disjoint (U i).val (U j).val) (i : Ω) :
    (polygonPartitionLabelling U hcover hdisjoint).fiber i = U i := by
  apply Subtype.ext
  ext p
  change (hcover p).choose = i ↔ p ∈ (U i).val
  constructor
  · intro hp; simpa only [hp] using (hcover p).choose_spec
  · intro hp
    by_contra hh
    exact Set.disjoint_left.mp (hdisjoint hh) (hcover p).choose_spec hp

theorem polygonPartitionLabelling_surjective (U : Ω → polygonAlgebra a)
    (hcover : ∀ p : GenericSquare a, ∃ i, p ∈ (U i).val)
    (hdisjoint : Pairwise fun i j => Disjoint (U i).val (U j).val)
    (hne : ∀ i, (U i).val.Nonempty) :
    Function.Surjective (polygonPartitionLabelling U hcover hdisjoint).label := by
  intro i
  obtain ⟨p,hp⟩ := hne i
  refine ⟨p,?_⟩
  change p ∈ ((polygonPartitionLabelling U hcover hdisjoint).fiber i).val
  rwa [polygonPartitionLabelling_fiber]

theorem centralOn_polygon_atoms {H : Type*} [Group H] [Fintype Ω]
    (q : H →* polygonAlternatingGroup a m) (U : Ω → polygonAlgebra a)
    (hcover : ∀ p : GenericSquare a, ∃ i, p ∈ (U i).val)
    (hdisjoint : Pairwise fun i j => Disjoint (U i).val (U j).val)
    (hne : ∀ i, (U i).val.Nonempty)
    (f : Ω → UniversalExtension (alternatingGroup (Fin m)) →* H)
    (hcomm : Pairwise fun i j => ∀ s t, Commute (f i s) (f j t))
    (hproj : ∀ i, q.comp (f i) = (conditionalAlternatingHom (U i)).comp
      (universalProjection (alternatingGroup (Fin m)))) :
    CentralOn q (⨆ i, (f i).range) := by
  let v := polygonPartitionLabelling U hcover hdisjoint
  apply centralOn_of_star_atoms q v.tableHom
    (v.tableHom_injective (polygonPartitionLabelling_surjective U hcover hdisjoint hne)) f hcomm
  intro i
  rw [PolygonLabelling.tableHom_single_mask]
  change q.comp (f i) = (conditionalAlternatingHom
    ((polygonPartitionLabelling U hcover hdisjoint).fiber i)).comp _
  rw [polygonPartitionLabelling_fiber]
  exact hproj i

end PolygonAtomLaw

end SimpleAmenable
end
end

end OAI
