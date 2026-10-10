import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.RestrictedTripleMaps

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve
open IntervalBar IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
noncomputable abbrev property₂ (p q:ℕ) := diagramProperty (diagramProperty W (Fin (p+1))) (Fin (q+1))
noncomputable abbrev property₃ (p q r:ℕ) := diagramProperty (property₂ W p q) (Fin (r+1))
noncomputable abbrev pos₂ (p q:ℕ) := PosDiagrams (diagramProperty W (Fin (p+1))) (Fin (q+1))
noncomputable abbrev pos₃ (p q r:ℕ) := PosDiagrams (property₂ W p q) (Fin (r+1))
noncomputable def tripleTranspose (p q r n:ℕ) :
    Diagram (Diagram (Diagram (Strings W n) (Fin (p+1))) (Fin (q+1))) (Fin (r+1)) ⥤
      Strings (property₃ W p q r) n :=
  Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1)) (transposeDiagram (I:=Fin (p+1)) W n)) ⋙
    Diagram.map (I:=Fin (r+1)) (transposeDiagram (I:=Fin (q+1)) (diagramProperty W (Fin (p+1))) n) ⋙
      transposeDiagram (I:=Fin (r+1)) (property₂ W p q) n
noncomputable instance tripleTransposeEquivalence (p q r n:ℕ) :
    (tripleTranspose W p q r n).IsEquivalence := by unfold tripleTranspose; infer_instance

noncomputable def triplePosInclusion (p q r:ℕ) : pos₃ W p q r ⥤
    Diagram (Diagram (Diagram C (Fin (p+1))) (Fin (q+1))) (Fin (r+1)) :=
  posDiagramInclusion (property₂ W p q) (Fin (r+1)) ⋙
    Diagram.map (I:=Fin (r+1)) (posDiagramInclusion (diagramProperty W (Fin (p+1))) (Fin (q+1))) ⋙
      Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1)) (posDiagramInclusion W (Fin (p+1))))
noncomputable instance triplePosInclusionEquivalence (p q r:ℕ) :
    (triplePosInclusion W p q r).IsEquivalence := by unfold triplePosInclusion; infer_instance
noncomputable def tripleDiagramHorizontal (p q r:ℕ) : SimplicialObject Cat.{0,0} where
  obj n := Cat.of (Diagram (Diagram (Diagram (Strings W n.unop.len) (Fin (p+1))) (Fin (q+1))) (Fin (r+1)))
  map f := (Diagram.map (I:=Fin (r+1)) (Diagram.map (I:=Fin (q+1)) (Diagram.map (I:=Fin (p+1))
    (reindex W f.unop.toOrderHom.toFunctor)))).toCatHom
  map_id n := by apply Cat.ext; exact map₃_strings_reindex_id W n.unop.len p q r
  map_comp f g := by apply Cat.ext; exact map₃_strings_reindex_comp W p q r g.unop.toOrderHom.toFunctor f.unop.toOrderHom.toFunctor

noncomputable def triplePosHomologyIso (p q r j:ℕ) :
    (nerve (pos₃ W p q r)).homology DiagonalResolution.Z j ≅
      (nerve (Diagram (Diagram (Diagram C (Fin (p+1))) (Fin (q+1))) (Fin (r+1)))).homology DiagonalResolution.Z j :=
  NerveHomotopy.homologyIso (triplePosInclusion W p q r).asEquivalence DiagonalResolution.Z j

noncomputable def tripleTransposeHomologyIso (p q r n j:ℕ) :
    (nerve (Diagram (Diagram (Diagram (Strings W n) (Fin (p+1))) (Fin (q+1))) (Fin (r+1)))).homology DiagonalResolution.Z j ≅
      (nerve (Strings (property₃ W p q r) n)).homology DiagonalResolution.Z j :=
  NerveHomotopy.homologyIso (tripleTranspose W p q r n).asEquivalence DiagonalResolution.Z j

noncomputable def tripleRestrictedHomologyIso (p q r j:ℕ) :
    (SimplicialDiagonal.nerveDiagonal.obj (horizontal (property₃ W p q r))).homology DiagonalResolution.Z j ≅
      (nerve (Diagram (Diagram (Diagram C (Fin (p+1))) (Fin (q+1))) (Fin (r+1)))).homology DiagonalResolution.Z j :=
  homologyIso (property₃ W p q r) j ≪≫ triplePosHomologyIso W p q r j
end RestrictedNerve

end

end

end OAI
