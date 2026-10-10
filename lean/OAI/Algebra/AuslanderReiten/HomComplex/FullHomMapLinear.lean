import OAI.Algebra.AuslanderReiten.HomComplex.FullHomMap
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomProductLinear
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomComposition

namespace OAI

noncomputable section
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit
variable {k : Type*} [CommRing k]
variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [Linear k C] [Linear k D]
variable (Φ : C ⥤ D) [Φ.Additive] [Φ.Linear k]
variable (K L : CochainComplex C ℤ) (n : ℤ)

theorem mapFullHom_smul (a : k) (x : CohomologyClass K L n) :
    mapFullHom Φ K L n (a • x) = a • mapFullHom Φ K L n x := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  rw [← CompleteComparison.fullHom_mk_smul, mapFullHom_mk, mapFullHom_mk,
    ← CompleteComparison.fullHom_mk_smul]
  congr 1
  apply Subtype.ext
  apply Cochain.ext
  intro p q hpq
  exact Φ.map_smul a (x.val.v p q hpq)

def mapFullHomLinear : CohomologyClass K L n →ₗ[k]
    CohomologyClass ((Φ.mapHomologicalComplex _).obj K)
      ((Φ.mapHomologicalComplex _).obj L) n where
  __ := mapFullHom Φ K L n
  map_smul' := mapFullHom_smul Φ K L n

theorem mapFullHom_identity :
    mapFullHom Φ K K 0 (CohomologyClass.mk (Cocycle.ofHom (𝟙 K))) =
      CohomologyClass.mk (Cocycle.ofHom (𝟙 ((Φ.mapHomologicalComplex _).obj K))) := by
  rw [mapFullHom_mk]
  congr 1
  apply Subtype.ext
  change (Cochain.ofHom (𝟙 K)).map Φ =
    Cochain.ofHom (𝟙 ((Φ.mapHomologicalComplex _).obj K))
  rw [Cochain.map_ofHom, CategoryTheory.Functor.map_id]

variable {K L n}
theorem fullHomPostcomp_smul (f : K ⟶ L) (n : ℤ) (a : k)
    (x : CohomologyClass K K n) :
    fullHomPostcomp f n (a • x) = a • fullHomPostcomp f n x := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  rw [← CompleteComparison.fullHom_mk_smul, fullHomPostcomp_mk, fullHomPostcomp_mk,
    ← CompleteComparison.fullHom_mk_smul]
  congr 1
  apply Subtype.ext
  exact Cochain.smul_comp a x.val (Cochain.ofHom f) (add_zero n)

theorem fullHomPrecomp_smul (f : K ⟶ L) (n : ℤ) (a : k)
    (x : CohomologyClass L L n) :
    fullHomPrecomp f n (a • x) = a • fullHomPrecomp f n x := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  rw [← CompleteComparison.fullHom_mk_smul, fullHomPrecomp_mk, fullHomPrecomp_mk,
    ← CompleteComparison.fullHom_mk_smul]
  congr 1
  apply Subtype.ext
  exact Cochain.comp_smul (Cochain.ofHom f) a x.val (zero_add n)

theorem fullHomPostcomp_identity (f : K ⟶ L) :
    fullHomPostcomp f 0 (CohomologyClass.mk (Cocycle.ofHom (𝟙 K))) =
      CohomologyClass.mk (Cocycle.ofHom f) := by
  rw [fullHomPostcomp_mk]
  congr 1
  apply Subtype.ext
  exact Cochain.id_comp _

theorem fullHomPrecomp_identity (f : K ⟶ L) :
    fullHomPrecomp f 0 (CohomologyClass.mk (Cocycle.ofHom (𝟙 L))) =
      CohomologyClass.mk (Cocycle.ofHom f) := by
  rw [fullHomPrecomp_mk]
  congr 1
  apply Subtype.ext
  exact Cochain.comp_id _

end ArExplicit

end

end OAI
