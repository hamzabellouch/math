import Mathlib
import OAI.Combinatorics.KMedian.Projection.ProductTable
import OAI.Combinatorics.KMedian.Projection.SeedSound

namespace OAI

section Inline_PCPSeedTables
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Binary Binary.Automatic Amplifier ProjectionTable
open scoped Classical

noncomputable def neutralTable : ProjectionTable Bool Bool :=
  build (BiProjection.neutral Bool Bool Bool Bool) (Fintype.equivFin Bool) (Ordered.fixed Bool) (Ordered.fixed Bool)
noncomputable def portOrder : Ordered ProjectionSeed.Port := (Ordered.fixed (RegularProgram.Port×Bool)).prod (Ordered.fixed Bool)
noncomputable def goodTable (t : CSPTable Label) : ProjectionTable ProjectionSeed.LeftLabel ProjectionSeed.RightLabel :=
  product (regularTable t) neutralTable
lemma poly_goodTable : Poly goodTable := by
  exact (poly_product (A:=Label×Label) (B:=Label) (A':=Bool) (B':=Bool)).comp
    (Poly.pair (poly_regularTable (A:=Label)) (Automatic.Poly.const neutralTable))
noncomputable def badRoot := Fintype.equivFin ((ProjectionSeed.Degree×Bool)×Bool)
noncomputable def badNodes := (Ordered.fixed Bool).prod (Ordered.fixed Bool)
noncomputable def badTable : ProjectionTable ProjectionSeed.LeftLabel ProjectionSeed.RightLabel :=
  build ProjectionSeed.bad badRoot badNodes portOrder
noncomputable def seedTable (t : CSPTable Label) : ProjectionTable ProjectionSeed.LeftLabel ProjectionSeed.RightLabel :=
  if allLegal t then goodTable t else badTable
lemma poly_seedTable : Poly seedTable := Poly.ite (poly_allLegal (A:=Label)) poly_goodTable (Automatic.Poly.const badTable)
variable (t : CSPTable Label) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
noncomputable def goodRoot := ((rootEquiv t h).prodCongr (Fintype.equivFin Bool)).trans finProdFinEquiv
noncomputable def goodNodes := (nodeOrder t h).prod (Ordered.fixed Bool)
lemma goodTable_build : goodTable t=build (good t h) (goodRoot t h) (goodNodes t h) portOrder := by
  unfold goodTable
  rw [regularTable_build t h]
  exact product_build (projection t h) (BiProjection.neutral Bool Bool Bool Bool)
    (rootEquiv t h) (Fintype.equivFin Bool) (nodeOrder t h) (Ordered.fixed Bool)
    (Ordered.fixed (RegularProgram.Port×Bool)) (Ordered.fixed Bool)
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedTables

end OAI
