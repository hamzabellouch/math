import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.BiProjective

namespace OAI

section

section

open CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace EilenbergZilber

open DiagonalResolution ModelAssembly
abbrev c := ComplexShape.down ℕ

def diag : SimplexCategoryᵒᵖ ⥤ Dᵒᵖ := (Functor.diag SimplexCategory).op

def bisimplicial {C : Type*} [Category C] (F : Dᵒᵖ ⥤ C) :
    SimplicialObject (SimplicialObject C) :=
  Functor.curry.obj ((CategoryTheory.prodOpEquiv SimplexCategory (D := SimplexCategory)).inverse ⋙ F)

variable (X : Dᵒᵖ ⥤ Type)
noncomputable def diagonalIso :
    (((assembly X).mapHomologicalComplex c).obj DiagonalResolution.complex) ≅
      SSet.chainComplex (diag ⋙ X) Z := by
  refine (CategoryTheory.eqToIso (congrArg (fun F => F.obj DiagonalResolution.chains)
    (map_alternatingFaceMapComplex (assembly X)))) ≪≫ ?_
  change AlternatingFaceMapComplex.obj (diag ⋙ models ⋙ assembly X) ≅
    AlternatingFaceMapComplex.obj (diag ⋙ X ⋙ sigmaConst.obj Z)
  exact (alternatingFaceMapComplex A).mapIso
    (Functor.isoWhiskerLeft diag (freeNatIso X))

noncomputable def rowIso (p : SimplexCategoryᵒᵖ) :
    ((BiResolution.chains.obj p) ⋙ assembly X) ≅
      (bisimplicial (X ⋙ sigmaConst.obj Z)).obj p := by
  refine NatIso.ofComponents (fun q => freeIso X (p.unop,q.unop)) ?_
  intro q q' f
  change (assembly X).map (pre (a:=(p.unop,q'.unop)) (b:=(p.unop,q.unop))
      (𝟙 p.unop,f.unop)) ≫ forward X (p.unop,q'.unop) =
    forward X (p.unop,q.unop) ≫
      (sigmaConst.obj Z).map (X.map (show (p.unop,q'.unop) ⟶ (p.unop,q.unop) from
        (𝟙 p.unop,f.unop)).op)
  exact pre_forward X (a:=(p.unop,q'.unop)) (b:=(p.unop,q.unop)) (𝟙 p.unop,f.unop)

noncomputable def bisimplicialIso :
    BiResolution.chains ⋙ (Functor.whiskeringRight _ _ _).obj (assembly X) ≅
      bisimplicial (X ⋙ sigmaConst.obj Z) := by
  refine NatIso.ofComponents (rowIso X) ?_
  intro p p' f
  apply NatTrans.ext
  funext q
  change (assembly X).map (pre (a:=(p'.unop,q.unop)) (b:=(p.unop,q.unop))
      (f.unop,𝟙 q.unop)) ≫ forward X (p'.unop,q.unop) =
    forward X (p.unop,q.unop) ≫
      (sigmaConst.obj Z).map (X.map (show (p'.unop,q.unop) ⟶ (p.unop,q.unop) from
        (f.unop,𝟙 q.unop)).op)
  exact pre_forward X (a:=(p'.unop,q.unop)) (b:=(p.unop,q.unop)) (f.unop,𝟙 q.unop)

noncomputable def twoComplex : HomologicalComplex₂ A c c :=
  AlternatingFaceMapComplex.obj (bisimplicial (X ⋙ sigmaConst.obj Z) ⋙ alternatingFaceMapComplex A)

noncomputable def twoIso : TotalFunctor.map₂ (assembly X) BiResolution.complex ≅ twoComplex X := by
  let F := assembly X
  let FC := F.mapHomologicalComplex c
  refine (CategoryTheory.eqToIso (congrArg (fun G => G.obj
    (BiResolution.chains ⋙ alternatingFaceMapComplex (D ⥤ A)))
      (map_alternatingFaceMapComplex FC))) ≪≫ ?_
  change AlternatingFaceMapComplex.obj
    (BiResolution.chains ⋙ alternatingFaceMapComplex (D ⥤ A) ⋙ FC) ≅ _
  rw [map_alternatingFaceMapComplex F]
  exact (alternatingFaceMapComplex (ChainComplex A ℕ)).mapIso
    (Functor.isoWhiskerRight (bisimplicialIso X) (alternatingFaceMapComplex A))

noncomputable def equiv : HomotopyEquiv (SSet.chainComplex (diag ⋙ X) Z) ((twoComplex X).total c) :=
  (HomotopyEquiv.ofIso (diagonalIso X).symm).trans
    ((assembledEquiv X).trans (HomotopyEquiv.ofIso
      (TotalFunctor.iso (assembly X) BiResolution.complex ≪≫ total.mapIso (twoIso X) c)))

noncomputable def homologyIso (n : ℕ) :
    SSet.homology (diag ⋙ X) Z n ≅ (((twoComplex X).total c).homology n) :=
  (equiv X).toHomologyIso n

end EilenbergZilber

end

end

end OAI
