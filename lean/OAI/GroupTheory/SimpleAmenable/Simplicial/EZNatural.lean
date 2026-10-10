import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.EilenbergZilber
import OAI.GroupTheory.SimpleAmenable.Homology.AssemblyMap

namespace OAI

open CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace EilenbergZilber

open DiagonalResolution ModelAssembly
variable {X Y : Dᵒᵖ ⥤ Type} (φ : X ⟶ Y)
noncomputable def diagonalMap : SSet.chainComplex (diag ⋙ X) Z ⟶ SSet.chainComplex (diag ⋙ Y) Z :=
  (alternatingFaceMapComplex A).map
    (Functor.whiskerRight (Functor.whiskerLeft diag φ) (sigmaConst.obj Z))
noncomputable def twoMap : twoComplex X ⟶ twoComplex Y :=
  (alternatingFaceMapComplex (ChainComplex A ℕ)).map
    (Functor.whiskerRight
      (Functor.curry.map (Functor.whiskerLeft
        (CategoryTheory.prodOpEquiv SimplexCategory (D:=SimplexCategory)).inverse
        (Functor.whiskerRight φ (sigmaConst.obj Z)))) (alternatingFaceMapComplex A))
noncomputable def twoIsoN (X : Dᵒᵖ ⥤ Type) :
    TotalFunctor.map₂ (assembly X) BiResolution.complex ≅ twoComplex X := by
  let F := assembly X
  let FC := F.mapHomologicalComplex c
  refine (CategoryTheory.eqToIso (congrArg (fun G => G.obj
    (BiResolution.chains ⋙ alternatingFaceMapComplex (D ⥤ A)))
      (map_alternatingFaceMapComplex FC))) ≪≫ ?_
  refine (alternatingFaceMapComplex (ChainComplex A ℕ)).mapIso
    (Functor.isoWhiskerLeft BiResolution.chains
      (CategoryTheory.eqToIso (map_alternatingFaceMapComplex F))) ≪≫ ?_
  exact (alternatingFaceMapComplex (ChainComplex A ℕ)).mapIso
    (Functor.isoWhiskerRight (bisimplicialIso X) (alternatingFaceMapComplex A))
noncomputable def equivN (X : Dᵒᵖ ⥤ Type) :
    HomotopyEquiv (SSet.chainComplex (diag ⋙ X) Z) ((twoComplex X).total c) :=
  (HomotopyEquiv.ofIso (diagonalIso X).symm).trans
    ((assembledEquiv X).trans (HomotopyEquiv.ofIso
      (TotalFunctor.iso (assembly X) BiResolution.complex ≪≫ total.mapIso (twoIsoN X) c)))
lemma diagonalIso_f (n : ℕ) : (diagonalIso X).hom.f n = forward X (SimplexCategory.mk n,SimplexCategory.mk n) := by
  simp only [diagonalIso, Iso.trans_hom, HomologicalComplex.comp_f]
  dsimp only [CategoryTheory.eqToIso]
  erw [HomologicalComplex.eqToHom_f]
  erw [eqToHom_refl, Category.id_comp]
  rfl
lemma twoIso_f (p q : ℕ) : ((twoIsoN X).hom.f p).f q = forward X (SimplexCategory.mk p,SimplexCategory.mk q) := by
  simp only [twoIsoN, Iso.trans_hom, HomologicalComplex.comp_f]
  dsimp only [CategoryTheory.eqToIso]
  erw [HomologicalComplex.eqToHom_f, HomologicalComplex.eqToHom_f]
  erw [eqToHom_refl, Category.id_comp]
  erw [Iso.trans_hom, HomologicalComplex.comp_f,
    Functor.mapIso_hom, alternatingFaceMapComplex_map_f, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app]
  dsimp only [CategoryTheory.eqToIso]
  erw [eqToHom_app, HomologicalComplex.eqToHom_f, eqToHom_refl, Category.id_comp]
  rfl
@[reassoc] lemma diagonal_natural :
    ((assemblyMap φ).mapHomologicalComplex c).app DiagonalResolution.complex ≫
      (diagonalIso Y).hom = (diagonalIso X).hom ≫ diagonalMap φ := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (assemblyMap φ).app (free (SimplexCategory.mk n,SimplexCategory.mk n)) ≫
    (diagonalIso Y).hom.f n = (diagonalIso X).hom.f n ≫ _
  rw [diagonalIso_f,diagonalIso_f]
  exact map_forward φ _
@[reassoc] lemma two_natural :
    TotalFunctor.nat₂ (assemblyMap φ) BiResolution.complex ≫ (twoIsoN Y).hom =
      (twoIsoN X).hom ≫ twoMap φ := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply HomologicalComplex.Hom.ext
  funext q
  change (assemblyMap φ).app (free (SimplexCategory.mk p,SimplexCategory.mk q)) ≫
    ((twoIsoN Y).hom.f p).f q = ((twoIsoN X).hom.f p).f q ≫ _
  rw [twoIso_f,twoIso_f]
  exact map_forward φ _
@[reassoc] lemma equiv_natural :
    diagonalMap φ ≫ (equivN Y).hom = (equivN X).hom ≫ total.map (twoMap φ) c := by
  change diagonalMap φ ≫ (diagonalIso Y).inv ≫ (assembledEquiv Y).hom ≫
    (TotalFunctor.iso (assembly Y) BiResolution.complex).hom ≫ (total.mapIso (twoIsoN Y) c).hom =
      ((diagonalIso X).inv ≫ (assembledEquiv X).hom ≫
      (TotalFunctor.iso (assembly X) BiResolution.complex).hom ≫ (total.mapIso (twoIsoN X) c).hom) ≫ _
  apply (cancel_epi (diagonalIso X).hom).mp
  simp only [←Category.assoc]
  rw [←diagonal_natural]
  simp only [Category.assoc,Iso.hom_inv_id_assoc]
  have hn := ((assemblyMap φ).mapHomologicalComplex c).naturality modelEquiv.hom
  have hn' : ((assemblyMap φ).mapHomologicalComplex c).app DiagonalResolution.complex ≫
      (assembledEquiv Y).hom = (assembledEquiv X).hom ≫
      ((assemblyMap φ).mapHomologicalComplex c).app BiResolution.total := hn.symm
  rw [←Category.assoc,hn']
  simp only [Category.assoc]
  have ht := TotalFunctor.iso_natural (assemblyMap φ) BiResolution.complex
  change ((assemblyMap φ).mapHomologicalComplex c).app BiResolution.total ≫
    (TotalFunctor.iso (assembly Y) BiResolution.complex).hom = _ at ht
  erw [reassoc_of% ht]
  have htwo : total.map (TotalFunctor.nat₂ (assemblyMap φ) BiResolution.complex) c ≫
      total.map (twoIsoN Y).hom c = total.map (twoIsoN X).hom c ≫ total.map (twoMap φ) c := by
    rw [←total.map_comp,←total.map_comp,two_natural]
  exact congrArg (fun k => (assembledEquiv X).hom ≫
    (TotalFunctor.iso (assembly X) BiResolution.complex).hom ≫ k) htwo
noncomputable def homologyIsoN (X : Dᵒᵖ ⥤ Type) (n : ℕ) :
    SSet.homology (diag ⋙ X) Z n ≅ (((twoComplex X).total c).homology n) :=
  (equivN X).toHomologyIso n
@[reassoc] lemma homology_natural (n : ℕ) :
    homologyMap (diagonalMap φ) n ≫ (homologyIsoN Y n).hom =
      (homologyIsoN X n).hom ≫ homologyMap (total.map (twoMap φ) c) n := by
  change homologyMap (diagonalMap φ) n ≫ homologyMap (equivN Y).hom n =
    homologyMap (equivN X).hom n ≫ homologyMap (total.map (twoMap φ) c) n
  rw [←homologyMap_comp,←homologyMap_comp,equiv_natural]
end EilenbergZilber

end OAI
