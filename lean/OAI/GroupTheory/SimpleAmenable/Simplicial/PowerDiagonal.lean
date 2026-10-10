import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.StageEvaluationEquiv
import OAI.GroupTheory.SimpleAmenable.Simplicial.StageMonoidal
import OAI.GroupTheory.SimpleAmenable.Simplicial.TripleComposition

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Simplicial Opposite
namespace BarFinitePower
open SimplicialDiagonal

variable (κ : Type) {X Y : SimplexCategoryᵒᵖ ⥤ SSet}
noncomputable def liftRows (f : κ → (X ⟶ Y)) : X ⟶ Y ⋙ power κ where
  app p := lift κ (fun k => (f k).app p)
  naturality p q g := by
    apply NatTrans.ext; funext r
    apply ConcreteCategory.hom_ext; intro x; funext k
    exact congrArg (fun f => (f.app r) x) ((f k).naturality g)
lemma liftDiagonal (f : κ → (X ⟶ Y)) :
    lift κ (fun k => diagonal.map (f k)) = diagonal.map (liftRows κ f) := rfl
lemma homologyLiftDiagonal_isIso (f : κ → (X ⟶ Y))
    (h : ∀p n, IsIso (SSet.homologyMap (lift κ (fun k => (f k).app p)) DiagonalResolution.Z n)) (n:ℕ) :
    IsIso (SSet.homologyMap (lift κ (fun k => diagonal.map (f k))) DiagonalResolution.Z n) := by
  rw [liftDiagonal]
  apply homologyMap_isIso
  exact h
end BarFinitePower

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace BarFinitePower
open IntervalBar IntervalBar.Diagram SimplicialDiagonal

variable {C : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C] (κ : Type)
noncomputable def triplePowerComparison : bar₃ (C:=κ → C) ⟶ (power κ).obj (bar₃ (C:=C)) :=
  lift κ (fun k => bar₃Map (project κ k))
lemma tripleDegree_homology_isIso (l m p k:ℕ) :
    IsIso (SSet.homologyMap (lift κ (fun j => nerveMap
      (map (I:=Fin (l+1)) (map (I:=Fin (m+1)) (map (I:=Fin (p+1)) (project (C:=C) κ j))))))
      DiagonalResolution.Z k) := by
  have : (Functor.pi' (fun j => map (I:=Fin (l+1)) (map (I:=Fin (m+1)) (map (I:=Fin (p+1)) (project (C:=C) κ j))))).IsEquivalence :=
    inferInstanceAs (tripleProject (C:=C) κ l m p).IsEquivalence
  exact lift_nerve_homology_isIso κ (fun j => map (I:=Fin (l+1))
      (map (I:=Fin (m+1)) (map (I:=Fin (p+1)) (project (C:=C) κ j)))) k
lemma tripleBarOne_homology_isIso (m p k:ℕ) :
    IsIso (SSet.homologyMap (lift κ (fun j => barMap
      (map (I:=Fin (m+1)) (map (I:=Fin (p+1)) (project (C:=C) κ j))))) DiagonalResolution.Z k) := by
  apply homologyLiftDiagonal_isIso κ (fun j =>
    Functor.whiskerRight (simplicialMap (map (I:=Fin (m+1))
      (map (I:=Fin (p+1)) (project (C:=C) κ j)))) nerveFunctor)
  intro l q
  exact tripleDegree_homology_isIso κ l.unop.len m p q
lemma tripleBarTwo_homology_isIso (p k:ℕ) :
    IsIso (SSet.homologyMap (lift κ (fun j => bar₂Map
      (map (I:=Fin (p+1)) (project (C:=C) κ j)))) DiagonalResolution.Z k) := by
  apply homologyLiftDiagonal_isIso κ (fun j => rows₂Map (map (I:=Fin (p+1)) (project (C:=C) κ j)))
  intro m q
  exact tripleBarOne_homology_isIso κ m.unop.len p q

lemma triplePowerComparison_homology_isIso (n:ℕ) :
    IsIso (SSet.homologyMap (triplePowerComparison (C:=C) κ) DiagonalResolution.Z n) := by
  apply homologyLiftDiagonal_isIso κ (fun k => rows₃Map (project (C:=C) κ k))
  intro p q
  exact tripleBarTwo_homology_isIso κ p.unop.len q
end BarFinitePower
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar.Diagram BarFinitePower

variable {a n : ℕ} (S : Stage a n)
noncomputable def finiteProductComparison : bar₃ (C:=S.Obj) ⟶
    (power (Fin S.partition.size × Fin S.support.card)).obj (bar₃ (C:=FiniteSetGroupoid)) :=
  bar₃Map UniformObject.evaluation ≫ triplePowerComparison _
lemma finiteProductComparison_homology_isIso (k:ℕ) :
    IsIso (SSet.homologyMap S.finiteProductComparison DiagonalResolution.Z k) := by
  have := evaluationIsEquivalence S.partition S.L S.L_reduced S.L_injective
  rw [finiteProductComparison,SSet.homologyMap_comp]
  have := bar₃Map_homology_isIso (UniformObject.evaluation (P:=S.partition) (L:=S.L)) k
  have := triplePowerComparison_homology_isIso (C:=FiniteSetGroupoid) (Fin S.partition.size × Fin S.support.card) k
  infer_instance
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
