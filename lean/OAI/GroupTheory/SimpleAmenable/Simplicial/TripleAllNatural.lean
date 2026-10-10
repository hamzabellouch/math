import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.StringEvaluation

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
lemma tripleDiagramResolutionHomologyIso_inner_natural (q r:ℕ) {p s:ℕ}
    (u:Fin (p+1)→oFin (s+1)) (j:ℕ) :
    SSet.homologyMap (SimplicialDiagonal.nerveDiagonal.map (tripleInnerReindex W q r u))
      DiagonalResolution.Z j ≫ (tripleDiagramResolutionHomologyIso W p q r j).hom =
      (tripleDiagramResolutionHomologyIso W s q r j).hom ≫
        SSet.homologyMap (nerveMap (Diagram.map (Diagram.map (Diagram.reindex u))))
          DiagonalResolution.Z j := by
  rw [←tripleResolutionAugmentation_homology W p q r j,
    ←tripleResolutionAugmentation_homology W s q r j]
  have h := congrArg (fun f => SSet.homologyMap f DiagonalResolution.Z j)
    (tripleResolutionAugmentation_inner_natural W q r u)
  simpa only [SSet.homologyMap_comp] using h

noncomputable def tripleSimultaneousReindex {p s:ℕ} (u:Fin (p+1)→oFin (s+1)) :
    tripleDiagramHorizontal W s s s ⟶ tripleDiagramHorizontal W p p p :=
  tripleInnerReindex W s s u ≫ tripleMiddleReindex W p s u ≫ tripleOuterReindex W p p u
lemma tripleResolutionAugmentation_diagonal_natural {p s:ℕ}
    (u:Fin (p+1)→oFin (s+1)) :
    SimplicialDiagonal.nerveDiagonal.map (tripleSimultaneousReindex W u) ≫
      tripleResolutionAugmentation W p p p =
      tripleResolutionAugmentation W s s s ≫
        nerveMap (Diagram.map (Diagram.map (Diagram.reindex u))) ≫
        nerveMap (Diagram.map (Diagram.reindex u)) ≫ nerveMap (Diagram.reindex u) := by
  unfold tripleSimultaneousReindex
  simp only [Functor.map_comp,Category.assoc]
  rw [tripleResolutionAugmentation_outer_natural]
  rw [←Category.assoc (SimplicialDiagonal.nerveDiagonal.map (tripleMiddleReindex W p s u)),
    tripleResolutionAugmentation_middle_natural]
  simp only [Category.assoc]
  rw [←Category.assoc (SimplicialDiagonal.nerveDiagonal.map (tripleInnerReindex W s s u)),
    tripleResolutionAugmentation_inner_natural]
  simp only [Category.assoc]
end RestrictedNerve

end

end

end OAI
