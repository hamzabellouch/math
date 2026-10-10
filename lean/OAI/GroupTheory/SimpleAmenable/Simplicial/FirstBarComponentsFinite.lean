import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.AbelianHomologyFinite

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace IntervalBar.Diagram
open FreeChains SimplicialDiagonal

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable abbrev homologyRow (q:ℕ) : ChainComplex A ℕ :=
  AlternatingFaceMapComplex.obj (simplicial (C:=C) ⋙ nerveFunctor ⋙ SSet.homologyFunctor Z q)
omit [SymmetricCategory C] in
lemma first_row_finite (q:ℕ)
    [Module.Finite ℤ ((bar (C:=C)).homology Z (1+q) : A)]
    (hf:∀p r,p+r=q+2 → 3≤p → Module.Finite ℤ ((homologyRow (C:=C) r).homology p)) :
    Module.Finite ℤ ((homologyRow (C:=C) q).homology 1) := by
  let X := simplicial (C:=C) ⋙ nerveFunctor
  let K := EilenbergZilber.twoComplex (uncurry X)
  have : Module.Finite ℤ ((K.total c).homology (1+q)) := by
    let e : ((bar (C:=C)).homology Z (1+q) : A) ≅ (K.total c).homology (1+q) :=
      EilenbergZilber.homologyIsoN (uncurry X) (1+q)
    exact Module.Finite.equiv e.toLinearEquiv
  have : Module.Finite ℤ ((TotalFiniteness.row K q).homology 1) := by
    apply TotalFiniteness.finite_first K q
    intro p r hpr hp
    have : Module.Finite ℤ ((AlternatingFaceMapComplex.obj (X ⋙ SSet.homologyFunctor DiagonalResolution.Z r)).homology p) := hf p r hpr hp
    exact Module.Finite.equiv (homologyRowHomologyIso X p r).symm.toLinearEquiv
  exact Module.Finite.equiv (homologyRowHomologyIso X 1 q).toLinearEquiv
lemma component_homology_finite (n:ℕ)
    [Module.Finite ℤ ((bar (C:=C)).homology Z 1 : A)] :
    Module.Finite ℤ ((nerve (SingleObj (Skeleton C))).homology Z n : A) := by
  have : Module.Finite ℤ ((homologyRow (C:=C) 0).homology 1) :=
    first_row_finite 0 (by intro p r hpr hp; omega)
  have : Module.Finite ℤ ((nerve (SingleObj (Skeleton C))).homology Z 1 : A) := by
    let e : (homologyRow (C:=C) 0).homology 1 ≅ (nerve (SingleObj (Skeleton C))).homology Z 1 :=
      (homologyFunctor A c 1).mapIso (componentRowChainIso (C:=C) ≪≫ (complexIso _).symm)
    exact Module.Finite.equiv e.toLinearEquiv
  exact TranslationNerve.homology_finite_of_one _ n
lemma first_row_one_finite
    [Module.Finite ℤ ((bar (C:=C)).homology Z 1 : A)]
    [Module.Finite ℤ ((bar (C:=C)).homology Z 2 : A)] :
    Module.Finite ℤ ((homologyRow (C:=C) 1).homology 1) := by
  apply first_row_finite 1
  intro p r hpr hp
  have hr:r=0:=by omega
  subst r
  have:=component_homology_finite (C:=C) p
  let e : ((nerve (SingleObj (Skeleton C))).homology Z p : A) ≅ (homologyRow (C:=C) 0).homology p :=
    (homologyFunctor A c p).mapIso ((complexIso _) ≪≫ (componentRowChainIso (C:=C)).symm)
  exact Module.Finite.equiv e.toLinearEquiv
end IntervalBar.Diagram

end

end OAI
