import OAI.Algebra.AuslanderReiten.HomComplex.FullHomMap
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomComposition

namespace OAI

noncomputable section
open CategoryTheory CochainComplex CochainComplex.HomComplex
namespace ArExplicit
variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
variable {Φ Ψ : C ⥤ D} [Φ.Additive] [Ψ.Additive]
variable {K L : CochainComplex C ℤ} {n : ℤ}

theorem mapFullHom_naturality (η : Φ ⟶ Ψ) (x : CohomologyClass K L n) :
    fullHomPostcomp ((η.mapHomologicalComplex _).app L) n (mapFullHom Φ K L n x) =
      fullHomPrecomp ((η.mapHomologicalComplex _).app K) n (mapFullHom Ψ K L n x) := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  rw [mapFullHom_mk, mapFullHom_mk, fullHomPostcomp_mk, fullHomPrecomp_mk]
  congr 1
  apply Cocycle.ext
  apply Cochain.ext
  intro i j hij
  change ((x.val.map Φ).comp (Cochain.ofHom ((η.mapHomologicalComplex _).app L))
      (add_zero n)).v i j hij =
    ((Cochain.ofHom ((η.mapHomologicalComplex _).app K)).comp (x.val.map Ψ)
      (zero_add n)).v i j hij
  rw [Cochain.comp_v _ _ (add_zero n) i j j hij (add_zero j),
    Cochain.comp_v _ _ (zero_add n) i i j (add_zero i) hij]
  simp only [Cochain.map_v, Cochain.ofHom_v, NatTrans.mapHomologicalComplex_app_f]
  exact η.naturality (x.val.v i j hij)

variable {F G H I : CochainComplex C ℤ}

theorem fullHomPostcomp_comp (f : F ⟶ G) (g : G ⟶ H) (x : CohomologyClass I F n) :
    fullHomPostcomp g n (fullHomPostcomp f n x) = fullHomPostcomp (f ≫ g) n x := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  simp only [fullHomPostcomp_mk]
  congr 1
  apply Cocycle.ext
  apply Cochain.ext
  intro i j hij
  change ((x.val.comp (Cochain.ofHom f) (add_zero n)).comp (Cochain.ofHom g)
      (add_zero n)).v i j hij = (x.val.comp (Cochain.ofHom (f ≫ g)) (add_zero n)).v i j hij
  rw [Cochain.comp_v _ _ (add_zero n) i j j hij (add_zero j),
    Cochain.comp_v _ _ (add_zero n) i j j hij (add_zero j),
    Cochain.comp_v _ _ (add_zero n) i j j hij (add_zero j)]
  simp only [Cochain.ofHom_v, HomologicalComplex.comp_f, Category.assoc]

theorem fullHomPostcomp_precomp (f : F ⟶ G) (g : H ⟶ I) (x : CohomologyClass G H n) :
    fullHomPostcomp g n (fullHomPrecomp f n x) =
      fullHomPrecomp f n (fullHomPostcomp g n x) := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  simp only [fullHomPostcomp_mk, fullHomPrecomp_mk]
  congr 1
  apply Cocycle.ext
  apply Cochain.ext
  intro i j hij
  change (((Cochain.ofHom f).comp x.val (zero_add n)).comp (Cochain.ofHom g)
      (add_zero n)).v i j hij =
    ((Cochain.ofHom f).comp (x.val.comp (Cochain.ofHom g) (add_zero n))
      (zero_add n)).v i j hij
  rw [Cochain.comp_v _ _ (add_zero n) i j j hij (add_zero j),
    Cochain.comp_v _ _ (zero_add n) i i j (add_zero i) hij,
    Cochain.comp_v _ _ (zero_add n) i i j (add_zero i) hij,
    Cochain.comp_v _ _ (add_zero n) i j j hij (add_zero j)]
  simp only [Cochain.ofHom_v, Category.assoc]

theorem fullHomPrecomp_comp (f : F ⟶ G) (g : G ⟶ H) (x : CohomologyClass H I n) :
    fullHomPrecomp f n (fullHomPrecomp g n x) = fullHomPrecomp (f ≫ g) n x := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  simp only [fullHomPrecomp_mk]
  congr 1
  apply Cocycle.ext
  apply Cochain.ext
  intro i j hij
  change ((Cochain.ofHom f).comp ((Cochain.ofHom g).comp x.val (zero_add n))
      (zero_add n)).v i j hij = ((Cochain.ofHom (f ≫ g)).comp x.val (zero_add n)).v i j hij
  rw [Cochain.comp_v _ _ (zero_add n) i i j (add_zero i) hij,
    Cochain.comp_v _ _ (zero_add n) i i j (add_zero i) hij,
    Cochain.comp_v _ _ (zero_add n) i i j (add_zero i) hij]
  simp only [Cochain.ofHom_v, HomologicalComplex.comp_f, Category.assoc]

end ArExplicit

end

end OAI
