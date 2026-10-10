import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.TripleReindex

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar.Diagram BarFinitePower UniformObject

variable {a n : ℕ} {S T : Stage a n} (h : S≤T)
variable (b : Fin S.partition.size × Fin S.support.card)
    (c : Fin T.partition.size × Fin T.support.card)
    (hp : S.partition.color (T.partition.point c.1)=b.1)
    (hl : S.L b.2=T.L c.2)
include hp hl

lemma refinement_coordinate_homology (j:ℕ) :
    SSet.homologyMap (bar₃Map (evaluation (P:=S.partition) (L:=S.L) ⋙ project _ b))
        DiagonalResolution.Z j =
    SSet.homologyMap (bar₃Map (inclusion h ⋙ evaluation (P:=T.partition) (L:=T.L) ⋙ project _ c))
        DiagonalResolution.Z j :=
  bar₃Map_eq_of_monoidalNatTrans (refineEvaluationIso h b c hp hl).hom j
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
