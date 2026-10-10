import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.E2Descend
import OAI.GroupTheory.SimpleAmenable.Simplicial.LowerBarComposition
import OAI.GroupTheory.SimpleAmenable.Simplicial.StringBarNaturality
import OAI.GroupTheory.SimpleAmenable.Homology.TrajectoryDifferential

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Opposite AlgebraicTopology HomologicalComplex
namespace SimplicialDiagonal

noncomputable def rowsIso (X : I ⥤ SSet) : EilenbergZilber.bisimplicial (uncurry X) ≅ X :=
  NatIso.ofComponents (rowIso X) (by
    intro n m f
    ext k x
    simp [rowIso,EilenbergZilber.bisimplicial,uncurry,Functor.uncurry])
noncomputable def homologyRowIso (X : I ⥤ SSet) (q : ℕ) :
    TotalFiniteness.row (EilenbergZilber.twoComplex (uncurry X)) q ≅
      AlternatingFaceMapComplex.obj (X ⋙ SSet.homologyFunctor DiagonalResolution.Z q) :=
  BarHomology.rowIso (uncurry X) q ≪≫ (alternatingFaceMapComplex FreeChains.A).mapIso
    (Functor.isoWhiskerRight (rowsIso X) (SSet.homologyFunctor DiagonalResolution.Z q))
noncomputable def homologyRowHomologyIso (X : I ⥤ SSet) (p q : ℕ) :
    (TotalFiniteness.row (EilenbergZilber.twoComplex (uncurry X)) q).homology p ≅
      (AlternatingFaceMapComplex.obj (X ⋙ SSet.homologyFunctor DiagonalResolution.Z q)).homology p :=
  (homologyFunctor FreeChains.A FreeChains.c p).mapIso (homologyRowIso X q)
lemma rows_connected (X : I ⥤ SSet) (hX : ∀ n,SSet.IsConnected (X.obj n)) (p : I) :
    SSet.IsConnected ((EilenbergZilber.bisimplicial (uncurry X)).obj p) := by
  have := hX p
  exact BarFinitePower.connected_of_iso _ (rowIso X p)
end SimplicialDiagonal
namespace BarHomology
open FreeChains

lemma zeroRow_finite (X : DiagonalResolution.Dᵒᵖ ⥤ Type)
    (hc : ∀ p, SSet.IsConnected ((EilenbergZilber.bisimplicial X).obj p)) (p : ℕ) :
    Module.Finite ℤ ((TotalFiniteness.row (EilenbergZilber.twoComplex X) 0).homology p) := by
  let K := AlternatingFaceMapComplex.obj ((Functor.const SimplexCategoryᵒᵖ).obj Z)
  have : Module.Finite ℤ (K.X p) := by
    change Module.Finite ℤ (ModuleCat.of ℤ ℤ)
    infer_instance
  have : Module.Finite ℤ (K.homology p) := finite_homology K p
  let e : K.homology p ≅ (TotalFiniteness.row (EilenbergZilber.twoComplex X) 0).homology p :=
    (homologyFunctor A c p).mapIso (zeroRowIso X hc).symm
  exact Module.Finite.equiv e.toLinearEquiv
end BarHomology
namespace RestrictedNerve
open IntervalBar.Diagram
variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
lemma stringBarRows_connected (p : SimplexCategoryᵒᵖ) : SSet.IsConnected ((stringBarRows W).obj p) :=
  bar₃_connected
lemma finite_bar₃_of_string (n : ℕ)
    [Module.Finite ℤ (SSet.homology (C:=FreeChains.A) (SimplicialDiagonal.diagonal.obj (stringBarRows W)) DiagonalResolution.Z n)] :
    Module.Finite ℤ ((bar₃ (C:=C)).homology DiagonalResolution.Z n : FreeChains.A) :=
  Module.Finite.equiv (asIso (SSet.homologyMap (stringBarAugmentation W) DiagonalResolution.Z n)).toLinearEquiv
end RestrictedNerve
namespace SimpleAmenable.PolygonObject.LabelledStage
open Labelled IntervalBar.Diagram FreeChains

attribute [local instance 1200] Rep.hV2 Representation.instModuleAsModule TensorProduct.instModule
noncomputable def trajectoryE2Iso (a p q : ℕ) (hq : 0<q) (hq5 : q≤5) :
    (TotalFiniteness.row (EilenbergZilber.twoComplex
      (SimplicialDiagonal.uncurry (RestrictedNerve.stringBarRows (positionalProperty a)))) q).homology p ≅
      groupHomology (trajectoryRep a q) p :=
by
  refine SimplicialDiagonal.homologyRowHomologyIso
    (RestrictedNerve.stringBarRows (positionalProperty a)) p q ≪≫ ?_
  exact (homologyFunctor A c p).mapIso (trajectoryChainIso a q hq hq5)
lemma trajectoryE2_finite (a p q : ℕ) (ha : 0<a) (hq : 0<q) (hq5 : q≤5)
    [Module.Finite ℤ (Stage.K q)] :
    Module.Finite ℤ ((TotalFiniteness.row (EilenbergZilber.twoComplex
      (SimplicialDiagonal.uncurry (RestrictedNerve.stringBarRows (positionalProperty a)))) q).homology p) := by
  have he : trajectoryRep a q = SquareStep.coefficientRep a (Stage.K q) := by
    unfold trajectoryRep
    congr 1
    exact Subsingleton.elim _ _
  have : Module.Finite ℤ (groupHomology (trajectoryRep a q) p) := by
    rw [he]
    exact SquareStep.coefficient_homology_finite ha (Stage.K q) p
  exact Module.Finite.equiv (trajectoryE2Iso a p q hq hq5).symm.toLinearEquiv
lemma polygon_bar₃_finite_of_symmetric (a : ℕ) (ha : 0<a)
    (hK : ∀ q, 0<q → q≤5 → Module.Finite ℤ (Stage.K q)) (n : ℕ) (hn : n≤5) :
    Module.Finite ℤ ((bar₃ (C:=PolygonObject a)).homology Z n : A) := by
  let X := SimplicialDiagonal.uncurry (RestrictedNerve.stringBarRows (positionalProperty a))
  have hc : ∀ p, SSet.IsConnected ((EilenbergZilber.bisimplicial X).obj p) :=
    SimplicialDiagonal.rows_connected _ (RestrictedNerve.stringBarRows_connected _)
  have : Module.Finite ℤ (SSet.homology (C:=A) (EilenbergZilber.diag ⋙ X) Z n) := by
    apply EilenbergZilber.finite_diagonal X n
    intro p q hpq
    by_cases hq : q=0
    · subst q
      exact BarHomology.zeroRow_finite X hc p
    · have := hK q (by omega) (by omega)
      exact trajectoryE2_finite a p q ha (by omega) (by omega)
  have : Module.Finite ℤ (SSet.homology (C:=A)
      (SimplicialDiagonal.diagonal.obj (RestrictedNerve.stringBarRows (positionalProperty a)))
      DiagonalResolution.Z n) := ‹Module.Finite ℤ (SSet.homology (C:=A) (EilenbergZilber.diag ⋙ X) Z n)›
  exact RestrictedNerve.finite_bar₃_of_string (positionalProperty a) n
end SimpleAmenable.PolygonObject.LabelledStage

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace SimplicialDiagonal
open FreeChains

variable (X:I ⥤ SSet)
lemma finite_reverse_step (q:ℕ)
    (hc:∀p,(X.obj p).IsConnected)
    (hz:IsZero ((X.obj (op ⦋0⦌)).homology Z q))
    [IsIso (SSet.homologyMap (segalTwo X) Z q)]
    (hrows:∀p i,i<q → Module.Finite ℤ ((X.obj (op ⦋p⦌)).homology Z i : A))
    [Module.Finite ℤ ((diagonal.obj X).homology Z (1+q) : A)] :
    Module.Finite ℤ ((X.obj (op ⦋1⦌)).homology Z q : A) := by
  have := hc (op ⦋1⦌)
  have := outer_kernel_finite X q (hrows 1)
  let K := EilenbergZilber.twoComplex (uncurry X)
  have : Module.Finite ℤ ((K.total c).homology (1+q)) := by
    let e : ((diagonal.obj X).homology Z (1+q) : A) ≅ (K.total c).homology (1+q) :=
      EilenbergZilber.homologyIsoN (uncurry X) (1+q)
    exact Module.Finite.equiv e.toLinearEquiv
  have : Module.Finite ℤ ((TotalFiniteness.row K q).homology 1) := by
    apply TotalFiniteness.finite_first K q
    intro p r hpr hp
    have : Module.Finite ℤ ((SSet.homologyFunctor Z r).obj (X.obj (op ⦋p⦌)) : A) := hrows p r (by omega)
    have : Module.Finite ℤ (SSet.homology ((EilenbergZilber.bisimplicial (uncurry X)).obj (op ⦋p⦌)) Z r : A) :=
      Module.Finite.equiv ((SSet.homologyFunctor Z r).mapIso (rowIso X (op ⦋p⦌))).symm.toLinearEquiv
    exact BarHomology.E2_finite (uncurry X) p r
  have : Module.Finite ℤ ((AlternatingFaceMapComplex.obj (X⋙SSet.homologyFunctor Z q)).homology 1) :=
    Module.Finite.equiv (homologyRowHomologyIso X 1 q).toLinearEquiv
  exact SimplicialFirstFinite.finite_one (X⋙SSet.homologyFunctor Z q) hz
lemma finite_reverse (r:ℕ)
    (hc:∀p,(X.obj p).IsConnected)
    (hz:∀q,0<q → IsZero ((X.obj (op ⦋0⦌)).homology Z q))
    (hs:∀q,0<q → IsIso (SSet.homologyMap (segalTwo X) Z q))
    (hrows:∀q,(∀i,i≤q → Module.Finite ℤ ((X.obj (op ⦋1⦌)).homology Z i : A)) →
      ∀p,Module.Finite ℤ ((X.obj (op ⦋p⦌)).homology Z q : A))
    (hf:∀n,n≤r+1 → Module.Finite ℤ ((diagonal.obj X).homology Z n : A)) :
    ∀q,q≤r → Module.Finite ℤ ((X.obj (op ⦋1⦌)).homology Z q : A) := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq
    by_cases hq0:q=0
    · subst q
      have := hc (op ⦋1⦌)
      exact BarFinitePower.homology_zero_finite _
    · have := hs q (by omega)
      have := hf (1+q) (by omega)
      apply finite_reverse_step X q hc (hz q (by omega))
      intro p i hi
      exact hrows i (by intro j hj; exact ih j (by omega) (by omega)) p
end SimplicialDiagonal

end

end OAI
