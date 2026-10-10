import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.FirstBarDegreeTwoFinite

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite HomologicalComplex
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable def lowOneHomologyIso :
    ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).homology 1 ≅
      (homologyRow (C:=C) 1).homology 2 := by
  let K := (RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c
  let L := homologyRow (C:=C) 1
  let e : K.sc' 2 1 0 ≅ L.sc' 3 2 1 :=
    ShortComplex.isoMk (gradedIso 2) (gradedIso 1) (gradedIso 0)
      (differential2 (C:=C)).symm (differential1 (C:=C)).symm
  exact (ShortComplex.homologyFunctor A).mapIso
    (K.isoSc' 2 1 0 (c.prev_eq' rfl) (c.next_eq' rfl) ≪≫ e ≪≫
      (L.isoSc' 3 2 1 (c.prev_eq' rfl) (c.next_eq' rfl)).symm)
lemma row_one_two_finite
    [Module.Finite ℤ (ComponentStable.object (C:=C) 1:A)]
    (hf:∀i,i≤1 → Module.Finite ℤ ((nerve (SingleObj (Skeleton C))).homology Z i:A)) :
    Module.Finite ℤ ((homologyRow (C:=C) 1).homology 2) := by
  have : Module.Finite ℤ (colimit (homologyDiagram (C:=C) 1):A) := inferInstanceAs
    (Module.Finite ℤ (ComponentStable.object (C:=C) 1:A))
  have := RegularCoefficient.total_finite (homologyDiagram (C:=C) 1) 1 (by
    intro i hi
    have := hf i hi
    exact Module.Finite.equiv (CommMonoidOpposite.homologyIso (Skeleton C) i).symm.toLinearEquiv)
  exact Module.Finite.equiv (lowOneHomologyIso (C:=C)).toLinearEquiv
end MarkedH1
namespace IntervalBar.Diagram
open FreeChains ComponentTranslation SimplicialDiagonal

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma bar_low_finite
    [Module.Finite ℤ (ComponentStable.object (C:=C) 1:A)]
    [Module.Finite ℤ (ComponentStable.object (C:=C) 2:A)]
    (hf:∀i,Module.Finite ℤ ((nerve (SingleObj (Skeleton C))).homology Z i:A))
    (n:ℕ) (hn:n≤3) : Module.Finite ℤ ((bar (C:=C)).homology Z n:A) := by
  let X:=simplicial (C:=C) ⋙ nerveFunctor
  apply EilenbergZilber.finite_diagonal (uncurry X) n
  intro p q hpq
  have hr : Module.Finite ℤ ((homologyRow (C:=C) q).homology p) := by
    by_cases hq:q=0
    · subst q
      have := hf p
      let e : ((nerve (SingleObj (Skeleton C))).homology Z p:A) ≅ (homologyRow (C:=C) 0).homology p :=
        (homologyFunctor A c p).mapIso ((complexIso _) ≪≫ (componentRowChainIso (C:=C)).symm)
      exact Module.Finite.equiv e.toLinearEquiv
    · by_cases hp:p=0
      · subst p
        have : Subsingleton ((homologyRow (C:=C) q).X 0) := ModuleCat.isZero_iff_subsingleton.mp
          (nerve.positive_zero (fun U V:IntervalBar.Diagram C (Fin 1)=>⟨zeroHom C U V⟩) q hq)
        have : Module.Finite ℤ ((homologyRow (C:=C) q).X 0) := inferInstance
        exact BarHomology.finite_homology _ _
      · have hq2:q≤2:=by omega
        interval_cases q
        · contradiction
        · rcases (show p=1 ∨ p=2 by omega) with rfl|rfl
          · exact StableBarOne.row_one_finite 1 (by decide)
          · exact MarkedH1.row_one_two_finite (fun i _=>hf i)
        · have hp1:p=1:=by omega
          subst p
          exact StableBarOne.row_one_finite 2 (by decide)
  have : Module.Finite ℤ ((AlgebraicTopology.AlternatingFaceMapComplex.obj (X ⋙ SSet.homologyFunctor DiagonalResolution.Z q)).homology p) := hr
  exact Module.Finite.equiv (homologyRowHomologyIso X p q).symm.toLinearEquiv
end IntervalBar.Diagram

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimplicialDiagonal
open FreeChains

variable (X:I ⥤ SSet)
lemma finite_forward (r:ℕ)
    (hc:∀p,(X.obj p).IsConnected)
    (hz:∀q,0<q → IsZero ((X.obj (op ⦋0⦌)).homology Z q))
    (hf:∀p q,q≤r → Module.Finite ℤ ((X.obj (op ⦋p⦌)).homology Z q : A)) :
    ∀n,n≤r+1 → Module.Finite ℤ ((diagonal.obj X).homology Z n:A) := by
  intro n hn
  apply EilenbergZilber.finite_diagonal (uncurry X) n
  intro p q hpq
  by_cases hq:q=0
  · subst q
    exact BarHomology.zeroRow_finite _ (rows_connected X hc) p
  · have : Module.Finite ℤ (SSet.homology ((EilenbergZilber.bisimplicial (uncurry X)).obj (op ⦋p⦌)) Z q:A) := by
      by_cases hp:p=0
      · subst p
        have hz' := (hz q (by omega)).of_iso ((SSet.homologyFunctor Z q).mapIso (rowIso X (op ⦋0⦌)))
        have : Subsingleton (SSet.homology ((EilenbergZilber.bisimplicial (uncurry X)).obj (op ⦋0⦌)) Z q:A) :=
          ModuleCat.isZero_iff_subsingleton.mp hz'
        infer_instance
      · have : Module.Finite ℤ ((SSet.homologyFunctor Z q).obj (X.obj (op ⦋p⦌)) : A) := hf p q (by omega)
        exact Module.Finite.equiv ((SSet.homologyFunctor Z q).mapIso (rowIso X (op ⦋p⦌))).symm.toLinearEquiv
    exact BarHomology.E2_finite _ p q
end SimplicialDiagonal
namespace IntervalBar.Diagram
open FreeChains BarFinitePower SimplicialDiagonal

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma bar₂_finite_forward (r:ℕ)
    (hf:∀n,n≤r → Module.Finite ℤ ((bar (C:=C)).homology Z n : A)) :
    ∀q,q≤r+1 → Module.Finite ℤ ((bar₂ (C:=C)).homology Z q : A) := by
  apply finite_forward (rows₂ (C:=C)) r (fun _=>bar_connected _) zero_bar_acyclic
  intro p q hq
  apply singleRow_finite
  exact fun i hi=>hf i (by omega)
lemma bar₃_finite_forward (r:ℕ)
    (hf:∀n,n≤r → Module.Finite ℤ ((bar₂ (C:=C)).homology Z n : A)) :
    ∀q,q≤r+1 → Module.Finite ℤ ((bar₃ (C:=C)).homology Z q : A) := by
  apply finite_forward (rows₃ (C:=C)) r (fun _=>bar₂_connected)
    (fun q hq=>by
      change IsZero (SSet.homology (C:=A) (bar₂ (C:=Diagram C (Fin 1))) Z q)
      exact bar₂_acyclic (fun _ _=>inferInstance) q hq)
  intro p q hq
  apply doubleRow_finite
  exact fun i hi=>hf i (by omega)
lemma triple_finite_of_bar
    (hf:∀n,n≤3 → Module.Finite ℤ ((bar (C:=C)).homology Z n : A)) :
    ∀q,q≤5 → Module.Finite ℤ ((bar₃ (C:=C)).homology Z q : A) :=
  bar₃_finite_forward 4 (bar₂_finite_forward 3 hf)
end IntervalBar.Diagram

end

end OAI
