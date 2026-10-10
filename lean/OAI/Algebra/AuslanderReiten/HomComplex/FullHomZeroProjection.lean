import OAI.Algebra.AuslanderReiten.HomComplex.FullHomZeroRepresentative

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
namespace ArExplicit
universe u v w
variable {C : Type w} [Category.{v} C] [Preadditive C]
variable {K L M : CochainComplex C ℤ}

theorem fullHomPostcomp_ofHom (f : K ⟶ L) (g : L ⟶ M) :
    fullHomPostcomp g 0 (CohomologyClass.mk (Cocycle.ofHom f)) =
      CohomologyClass.mk (Cocycle.ofHom (f ≫ g)) := by
  rw [← fullHomPostcomp_identity f, fullHomPostcomp_comp, fullHomPostcomp_identity]

variable (k : Type u) [CommRing k] [Linear k C]

include k in
theorem fullHomZero_projection_inverse (f : K ⟶ L) (g : L ⟶ K)
    (e : (HomotopyCategory.quotient C _).obj L ≅ (HomotopyCategory.quotient C _).obj K)
    (he : (HomotopyCategory.quotient C _).map g = e.hom)
    (h : fullHomPostcomp g 0 (CohomologyClass.mk (Cocycle.ofHom f)) =
      CohomologyClass.mk (Cocycle.ofHom (𝟙 K))) :
    (HomotopyCategory.quotient C _).map f = e.inv := by
  rw [fullHomPostcomp_ofHom] at h
  have hh := (fullHomZero_class_eq_iff k (f ≫ g) (𝟙 K)).mp h
  rw [CategoryTheory.Functor.map_comp, he, CategoryTheory.Functor.map_id] at hh
  apply (cancel_mono e.hom).1
  exact hh.trans e.inv_hom_id.symm

end ArExplicit

end

end OAI
