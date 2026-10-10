import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.BarContractible
import OAI.GroupTheory.SimpleAmenable.Simplicial.FiniteSetMonoidal

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace IntervalBar.Diagram

open FreeChains
lemma bar₃_acyclic {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
    [∀x y:C,Subsingleton (x ⟶ y)] (hh:∀x y:C,Nonempty (x ⟶ y))
    (n:ℕ) (hn:0<n) : Limits.IsZero (SSet.homology (C:=A) (bar₃ (C:=C)) Z n) := by
  apply SimplicialDiagonal.connectivity (rows₃ (C:=C)) n
  · intro p; exact bar₂_connected
  · intro q hq
    exact bar₂_acyclic (fun x y => ⟨homOfAll hh 0 x y⟩) q hq
  · intro p q hq _
    exact bar₂_acyclic (fun x y => ⟨homOfAll hh p x y⟩) q hq
  · exact hn
  · omega
end IntervalBar.Diagram
namespace SimpleAmenable.PolygonObject.FiniteSetGroupoid
abbrev Terminal := Discrete PUnit
instance terminalSymmetric : SymmetricCategory Terminal where
  braiding X Y := eqToIso (Subsingleton.elim _ _)
  braiding_naturality_left := by intros; exact Subsingleton.elim _ _
  braiding_naturality_right := by intros; exact Subsingleton.elim _ _
  hexagon_forward := by intros; exact Subsingleton.elim _ _
  hexagon_reverse := by intros; exact Subsingleton.elim _ _
  symmetry := by intros; exact Subsingleton.elim _ _
noncomputable def terminal {C:Type} [Category.{0} C] : C ⥤ Terminal :=
  (Functor.const C).obj ⟨PUnit.unit⟩
noncomputable instance terminalMonoidal {C:Type} [Category.{0} C] [MonoidalCategory C] :
    (terminal (C:=C)).Monoidal := Functor.CoreMonoidal.toMonoidal {
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left := by intros; exact Subsingleton.elim _ _
  μIso_hom_natural_right := by intros; exact Subsingleton.elim _ _
  associativity := by intros; exact Subsingleton.elim _ _
  left_unitality := by intros; exact Subsingleton.elim _ _
  right_unitality := by intros; exact Subsingleton.elim _ _ }
noncomputable instance terminalBraided {C:Type} [Category.{0} C] [MonoidalCategory C] [BraidedCategory C] :
    (terminal (C:=C)).Braided where
  braided _ _ := Subsingleton.elim _ _
noncomputable def emptyFunctor : Terminal ⥤ FiniteSetGroupoid :=
  (Functor.const _).obj empty
noncomputable instance emptyFunctorMonoidal : emptyFunctor.Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso _ _ := Iso.refl _
    μIso_hom_natural_left := by intros; apply Equiv.ext; intro x; exact Fin.elim0 x
    μIso_hom_natural_right := by intros; apply Equiv.ext; intro x; exact Fin.elim0 x
    associativity := by intros; apply Equiv.ext; intro x; exact Fin.elim0 x
    left_unitality := by intros; apply Equiv.ext; intro x; exact Fin.elim0 x
    right_unitality := by intros; apply Equiv.ext; intro x; exact Fin.elim0 x }
noncomputable instance : emptyFunctor.Braided where
  braided _ _ := by apply Equiv.ext; intro x; exact Fin.elim0 x
end SimpleAmenable.PolygonObject.FiniteSetGroupoid

end

end

end OAI
