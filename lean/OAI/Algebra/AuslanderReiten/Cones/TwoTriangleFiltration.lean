import OAI.Algebra.AuslanderReiten.Homology.TriangleGradedSequence
import OAI.Algebra.AuslanderReiten.Cones.TwoConeFiltration

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated

namespace ArExplicit

universe u w
variable (k : Type u) [Field k]
variable {C : Type w} [Category.{u} C] [Preadditive C] [Linear k C]
variable [Limits.HasZeroObject C] [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
variable {B D E K W : C} (X : C)
variable (f : B ⟶ K) (g : K ⟶ D) (δ : D ⟶ B⟦(1 : ℤ)⟧)
variable (i : K ⟶ W) (p : W ⟶ E) (ε : E ⟶ K⟦(1 : ℤ)⟧)
variable (h₁ : Triangle.mk f g δ ∈ distTriang C)
variable (h₂ : Triangle.mk i p ε ∈ distTriang C)

def twoTriangleHomFiltration :
    TwoConeFiltration (k := k) (fun n => X ⟶ B⟦n⟧) (fun n => X ⟶ D⟦n⟧)
      (fun n => X ⟶ E⟦n⟧) (fun n => X ⟶ K⟦n⟧) (fun n => X ⟶ W⟦n⟧) where
  row := TriangleGradedSequence.connecting k (Triangle.mk f g δ) X
  column n := (TriangleGradedSequence.second k (Triangle.mk f g δ) X (n + 1)).comp
    (TriangleGradedSequence.connecting k (Triangle.mk i p ε) X n)
  bottom := TriangleGradedSequence.first k (Triangle.mk f g δ) X
  middle := TriangleGradedSequence.second k (Triangle.mk f g δ) X
  attach := TriangleGradedSequence.connecting k (Triangle.mk i p ε) X
  inclusion := TriangleGradedSequence.first k (Triangle.mk i p ε) X
  projection := TriangleGradedSequence.second k (Triangle.mk i p ε) X
  row_bottom := TriangleGradedSequence.exact_next k _ X h₁
  bottom_middle := TriangleGradedSequence.exact_middle k _ X h₁
  middle_row := TriangleGradedSequence.exact_top k _ X h₁
  attach_inclusion := TriangleGradedSequence.exact_next k _ X h₂
  inclusion_projection := TriangleGradedSequence.exact_middle k _ X h₂
  projection_attach := TriangleGradedSequence.exact_top k _ X h₂
  adjacent _ := rfl

end ArExplicit

end

end OAI
