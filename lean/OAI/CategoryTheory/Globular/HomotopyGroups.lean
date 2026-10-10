import OAI.CategoryTheory.Globular.ElementaryExpansion

namespace OAI

namespace Grothendieck.GlobularTheory.Model
open CategoryTheory

noncomputable instance homotopyGroupGroup.{v} {C : GlobularTheory.{v}} (X : C.Model)
    (hC : C.IsCoherator) (x : X.underlying.Cell 0) (n : ℕ) :
    Group (X.HomotopyGroup hC x n) :=
  show Group (End (⟨X.baseCell hC x n⟩ : CellGroupoid X hC n)) from inferInstance

noncomputable def homotopyMapHom.{v} {C : GlobularTheory.{v}} {X Y : C.Model}
    (f : X ⟶ Y) (hC : C.IsCoherator) (x : X.underlying.Cell 0) (n : ℕ) :
    X.HomotopyGroup hC x n →* Y.HomotopyGroup hC ((underlyingMap f).app 0 x) n where
  toFun := homotopyMap f hC x n
  map_one' := by
    apply congrArg (Quot.mk _)
    apply Subtype.ext
    exact (map_unitCell f hC n (X.baseCell hC x n)).trans
      (congrArg (Y.unitCell hC n) (map_baseCell f hC x n))
  map_mul' a b := by
    induction a using Quot.inductionOn with | h a =>
    induction b using Quot.inductionOn with | h b =>
    apply congrArg (Quot.mk _)
    apply Subtype.ext
    exact map_compCell f hC n b.1 a.1 _

noncomputable def homotopyGroupIsoOfWeakEquivalence.{v} {C : GlobularTheory.{v}}
    {X Y : C.Model} (f : X ⟶ Y) (hC : C.IsCoherator) (hf : WeakEquivalence hC f)
    (x : X.underlying.Cell 0) (n : ℕ) :
    X.HomotopyGroup hC x n ≃* Y.HomotopyGroup hC ((underlyingMap f).app 0 x) n :=
  MulEquiv.ofBijective (homotopyMapHom f hC x n) (hf.2 x n)

end Grothendieck.GlobularTheory.Model

end OAI
