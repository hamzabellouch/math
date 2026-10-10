import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.FirstBarDegreeTwoFinite
import OAI.GroupTheory.SimpleAmenable.Configurations.FiberBinary
import OAI.GroupTheory.SimpleAmenable.Homology.FiniteCokernelExtension

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram
open FreeChains ComponentStable

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable def binaryMap : nerve (Diagram C (Fin 3)) ⟶ nerve C⊗nerve C :=
  nerveMap (eval 2) ≫ (PiSSet.nervePiIso (fun _:Fin 2=>C)).hom ≫
    (PiSSet.binaryIso (fun _:Fin 2=>nerve C)).hom
omit [SymmetricCategory C] in
lemma binaryMap_fst : binaryMap (C:=C) ≫ CartesianMonoidalCategory.fst _ _=
    nerveMap (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom) ≫ nerveMap oneEval := rfl
omit [SymmetricCategory C] in
lemma binaryMap_snd : binaryMap (C:=C) ≫ CartesianMonoidalCategory.snd _ _=
    nerveMap (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom) ≫ nerveMap oneEval := rfl
omit [SymmetricCategory C] in
lemma binaryMap_mult : binaryMap (C:=C) ≫ multiplication=nerveMap (eval 2 ⋙ tensorPair) := rfl
omit [SymmetricCategory C] in
@[reassoc] lemma binaryMap_middle (q:ℕ) :
    SSet.homologyMap (binaryMap (C:=C)) Z q ≫ SSet.homologyMap multiplication Z q =
      SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (1:Fin 3)).toOrderHom)) Z q ≫
        SSet.homologyMap (nerveMap oneEval) Z q := by
  rw [←SSet.homologyMap_comp,binaryMap_mult,←SSet.homologyMap_comp]
  exact (NerveHomotopy.ofNatTrans binaryCutIso.hom).congr_homologyMap Z q
private lemma defect_rearrange {M:Type} [AddCommGroup M] (x y z:M) : x-y+z=z+x-y := by abel
omit [SymmetricCategory C] in
lemma d21_binaryD (q:ℕ) : (homologyRow (C:=C) q).d 2 1 ≫ (StableBarOne.oneIso q).hom ≫ toStable q =
    SSet.homologyMap (binaryMap (C:=C)) Z q ≫ binaryD q := by
  let faceMap (index : Fin 3) :
      (nerve (Diagram C (Fin 3))).homology Z q ⟶ (nerve (Diagram C (Fin 2))).homology Z q :=
    SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ index).toOrderHom)) Z q
  rw [SimplicialFirstFinite.d21]
  change (faceMap 0 - faceMap 1 + faceMap 2) ≫
    SSet.homologyMap (nerveMap oneEval) Z q ≫ toStable q =
    SSet.homologyMap (binaryMap (C:=C)) Z q ≫ binaryD q
  simp only [Preadditive.add_comp,Preadditive.sub_comp,binaryD,Preadditive.comp_add,
    Preadditive.comp_sub]
  rw [binaryMap_middle_assoc,
    ←SSet.homologyMap_comp_assoc (f:=binaryMap) (g:=CartesianMonoidalCategory.fst _ _),binaryMap_fst,
    SSet.homologyMap_comp_assoc,←SSet.homologyMap_comp_assoc (f:=binaryMap) (g:=CartesianMonoidalCategory.snd _ _),
    binaryMap_snd,SSet.homologyMap_comp_assoc]
  exact defect_rearrange
    (M := (nerve (Diagram C (Fin 3))).homology Z q ⟶ object (C:=C) q) _ _ _
end IntervalBar.Diagram

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentStable IntervalBar.Diagram

attribute [local instance 1200] Rep.hV2 Submodule.module Submodule.Quotient.module
lemma stableH2_finite_of_bar (a:ℕ)
    [Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z 1:A)]
    [Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z 2:A)]
    [Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z 3:A)] :
    Module.Finite ℤ (object (C:=PolygonObject a) 2:A) := by
  have fullH1Finite := fullH1_finite_of_bar a 32 (by omega)
  have mixedImageFinite := mixedImage_finite a
  have firstRowTwoFinite := first_row_two_finite (C:=PolygonObject a)
  apply ChainComplex.finite_of_boundary_annihilation (homologyRow (C:=PolygonObject a) 2)
    (StableBarOne.row_d10 2 (by decide)) ((StableBarOne.oneIso 2).hom ≫ toStable 2) (mixedImage a)
  rw [←Category.assoc,d21_binaryD]
  change (SSet.homologyMap (binaryMap (C:=PolygonObject a)) Z 2 ≫ binaryD 2) ≫
    ModuleCat.ofHom (mixedImage a).mkQ = 0
  rw [Category.assoc,binaryD_quotient_zero,comp_zero]
lemma fullH2_finite_of_bar (a m:ℕ) (hm:34 ≤ m)
    [Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z 1:A)]
    [Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z 2:A)]
    [Module.Finite ℤ ((bar (C:=PolygonObject a)).homology Z 3:A)] :
    Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 2) :=
  (finite_fullH2_iff_stable a m hm).mpr (stableH2_finite_of_bar a)
end SimpleAmenable.PolygonTracks

end

end OAI
