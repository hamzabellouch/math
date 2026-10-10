import OAI.Algebra.Finitistic.Localization.DerivedTruncationCohomology

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.DerivedTruncation
open DerivedCategory
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable (n : ℤ)

lemma single_homology_injective {A B : C}
    (f g : (singleFunctor C n).obj A ⟶ (singleFunctor C n).obj B)
    (h : (homologyFunctor C n).map f = (homologyFunctor C n).map g) : f = g := by
  obtain ⟨a,rfl⟩ := (singleFunctor C n).map_surjective f
  obtain ⟨b,rfl⟩ := (singleFunctor C n).map_surjective g
  congr 1
  let e := singleFunctorCompHomologyFunctorIso C n
  apply (cancel_epi (e.app A).hom).mp
  have ha : (homologyFunctor C n).map ((singleFunctor C n).map a) ≫ (e.app B).hom =
      (e.app A).hom ≫ a := e.hom.naturality a
  have hb : (homologyFunctor C n).map ((singleFunctor C n).map b) ≫ (e.app B).hom =
      (e.app A).hom ≫ b := e.hom.naturality b
  rw [← ha,← hb,h]

lemma homology_injective {X Y : DerivedCategory C}
    [X.IsGE n] [X.IsLE n] [Y.IsGE n] [Y.IsLE n]
    (f g : X ⟶ Y) (h : (homologyFunctor C n).map f = (homologyFunctor C n).map g) : f = g := by
  apply (cancel_epi (singleIso X n).inv).mp
  apply (cancel_mono (singleIso Y n).hom).mp
  apply single_homology_injective n
  simp only [Functor.map_comp,h]

variable (X : DerivedCategory C) [X.IsGE n] [X.IsLE n]

def cohomologyAutomorphism : (homologyFunctor C n).obj X ≅ (homologyFunctor C n).obj X :=
  (homologyFunctor C n).mapIso (singleIso X n) ≪≫
    (singleFunctorCompHomologyFunctorIso C n).app ((homologyFunctor C n).obj X)

/-- Normalize a single-degree identification to induce the identity on its actual cohomology. -/
def canonicalIso : X ≅ (singleFunctor C n).obj ((homologyFunctor C n).obj X) :=
  singleIso X n ≪≫ (singleFunctor C n).mapIso (cohomologyAutomorphism n X).symm

lemma canonicalIso_homology :
    (homologyFunctor C n).map (canonicalIso n X).hom ≫
      ((singleFunctorCompHomologyFunctorIso C n).app ((homologyFunctor C n).obj X)).hom = 𝟙 _ := by
  let e := singleFunctorCompHomologyFunctorIso C n
  have hn : (homologyFunctor C n).map ((singleFunctor C n).map (cohomologyAutomorphism n X).inv) ≫
      ((singleFunctorCompHomologyFunctorIso C n).app ((homologyFunctor C n).obj X)).hom =
    ((singleFunctorCompHomologyFunctorIso C n).app ((homologyFunctor C n).obj X)).hom ≫
      (cohomologyAutomorphism n X).inv := e.hom.naturality _
  dsimp only [canonicalIso,Iso.trans_hom,Functor.mapIso_hom,Iso.symm_hom]
  rw [Functor.map_comp,Category.assoc,hn]
  rw [← Category.assoc]
  change (cohomologyAutomorphism n X).hom ≫ (cohomologyAutomorphism n X).inv = 𝟙 _
  exact Iso.hom_inv_id _

variable {X} {Y : DerivedCategory C} [Y.IsGE n] [Y.IsLE n]

/-- The normalized single-degree identification commutes with every derived morphism. -/
theorem canonicalIso_naturality (f : X ⟶ Y) :
    f ≫ (canonicalIso n Y).hom =
      (canonicalIso n X).hom ≫ (singleFunctor C n).map ((homologyFunctor C n).map f) := by
  apply homology_injective n
  apply (cancel_mono
    ((singleFunctorCompHomologyFunctorIso C n).app ((homologyFunctor C n).obj Y)).hom).mp
  simp only [Functor.map_comp,Category.assoc,canonicalIso_homology,Category.comp_id]
  have hn : (homologyFunctor C n).map ((singleFunctor C n).map ((homologyFunctor C n).map f)) ≫
      ((singleFunctorCompHomologyFunctorIso C n).app ((homologyFunctor C n).obj Y)).hom =
    ((singleFunctorCompHomologyFunctorIso C n).app ((homologyFunctor C n).obj X)).hom ≫
      (homologyFunctor C n).map f :=
    (singleFunctorCompHomologyFunctorIso C n).hom.naturality _
  rw [hn,← Category.assoc,canonicalIso_homology,Category.id_comp]
end LittleFinitistic.DerivedTruncation

end

end OAI
