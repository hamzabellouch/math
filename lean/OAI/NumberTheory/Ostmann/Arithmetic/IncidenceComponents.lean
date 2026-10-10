import OAI.NumberTheory.Ostmann.Arithmetic.IncidenceHaar

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.IncidenceHaar

variable {V E G : Type*} [Fintype V] [Fintype E] [DecidableEq V] [CommGroup G]

abbrev Component (source target : E → V) :=
  Quotient (Relation.EqvGen.setoid (edgeRelation source target))

instance componentFintype (source target : E → V) : Fintype (Component source target) :=
  Fintype.ofFinite _
instance componentDecidableEq (source target : E → V) : DecidableEq (Component source target) :=
  Classical.decEq _

def componentLabel (source target : E → V) (v : V) : Component source target :=
  Quotient.mk _ v

def componentRoot (source target : E → V) (c : Component source target) : V := c.out

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem componentRoot_label (source target : E → V) (c : Component source target) :
    componentLabel source target (componentRoot source target c) = c := Quotient.out_eq c

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem componentPath (source target : E → V) (v : V) :
    Relation.EqvGen (edgeRelation source target) v
      (componentRoot source target (componentLabel source target v)) :=
  Quotient.exact (Quotient.out_eq (componentLabel source target v)).symm

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem componentLabel_edge (source target : E → V) (e : E) :
    componentLabel source target (source e) = componentLabel source target (target e) :=
  Quotient.sound (Relation.EqvGen.rel _ _ ⟨e,rfl,rfl⟩)

def balanced (source target : E → V) : Subgroup (V → G) where
  carrier := {x | ∀ c : Component source target, fiberProduct (componentLabel source target) c x = 1}
  one_mem' := by intro c; exact map_one _
  mul_mem' hx hy := by intro c; rw [map_mul,hx c,hy c,mul_one]
  inv_mem' hx := by intro c; rw [map_inv,hx c,inv_one]

theorem boundary_range_eq_balanced (source target : E → V) :
    (boundary (G:=G) source target).range = balanced source target := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact fun c => fiberProduct_boundary source target (componentLabel source target)
      (componentLabel_edge source target) c y
  · intro hx
    exact mem_range_of_component_products source target (componentLabel source target)
      (componentRoot source target) (componentRoot_label source target)
      (componentPath source target) x hx

def boundaryToBalanced (source target : E → V) : (E → G) →* balanced (G:=G) source target :=
  (boundary (G:=G) source target).codRestrict (balanced (G:=G) source target) (fun x => by
    rw [← boundary_range_eq_balanced]
    exact ⟨x,rfl⟩)

theorem boundaryToBalanced_surjective (source target : E → V) :
    Function.Surjective (boundaryToBalanced (G:=G) source target) := by
  intro x
  have hx : x.val ∈ (boundary source target).range := by
    rw [boundary_range_eq_balanced]
    exact x.property
  obtain ⟨y,hy⟩ := hx
  exact ⟨y,Subtype.ext hy⟩

instance balancedFintype [Fintype G] (source target : E → V) :
    Fintype (balanced (G:=G) source target) := Fintype.ofFinite _

theorem boundary_uniform [Fintype G] [DecidableEq E] (source target : E → V)
    (F : balanced (G:=G) source target → ℂ) :
    ResidueHaar.average (fun x => F (boundaryToBalanced source target x)) =
      ResidueHaar.average F :=
  GroupHaarImage.average_surjective _ (boundaryToBalanced_surjective source target) F

end Ostmann.Arithmetic.IncidenceHaar

end

end OAI
