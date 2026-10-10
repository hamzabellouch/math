import OAI.Probability.SATComputability.HierarchyExpectation
import OAI.Probability.SATComputability.HierarchyBounds
import OAI.Probability.SATComputability.WeightedExpressions

namespace OAI

namespace FixedClauseThreshold.Computability

open Nat.Partrec Encodable Denumerable FiniteArithmetic
open RapidForcing.EffectiveArithmetic
local instance hierarchyTableRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable
local instance hierarchyTableCodeEq : DecidableEq Code := Encodable.decidableEqOfEncodable Code
local instance hierarchyTableListBEq : BEq (List Code) := instBEqOfDecidableEq

abbrev ExpressionTable := List (List Code × Code)

noncomputable def tableLookup (tab : ExpressionTable) (cs : List Code) : Code :=
  (tab.lookup cs).getD .zero

@[fun_prop] theorem tableLookup_computable :
    Computable (fun p : ExpressionTable × List Code => tableLookup p.1 p.2) := by
  unfold tableLookup
  exact (Primrec.option_getD.comp
    ((Primrec.listLookup (α := List Code) (β := Code)).comp Primrec.snd Primrec.fst)
    (Primrec.const Code.zero)).to_comp

theorem tableLookup_map (states : List (List Code)) (f : List Code → Code)
    {cs : List Code} (hcs : cs ∈ states) :
    tableLookup (states.map (fun ds => (ds, f ds))) cs = f cs := by
  unfold tableLookup
  rw [List.lookup_graph f hcs]
  rfl

noncomputable def layerExpression (m : ℚ) (tab : ExpressionTable) (cs : List Code) : Code :=
  .comp (rationalExpression m⁻¹)
    (logMixtureExpression ((chooseChildren cs).map (fun b =>
      (b.1, Code.comp (rationalExpression m) (tableLookup tab b.2)))))

@[fun_prop] theorem layerExpression_computable :
    Computable (fun p : ℚ × ExpressionTable × List Code => layerExpression p.1 p.2.1 p.2.2) := by
  have hl : Computable (fun p : ℚ × ExpressionTable × List Code =>
      (chooseChildren p.2.2).map (fun b =>
        (b.1, Code.comp (rationalExpression p.1) (tableLookup p.2.1 b.2)))) := by
    apply computable_list_map (chooseChildren_computable.comp (by fun_prop))
    unfold Computable₂
    fun_prop
  unfold layerExpression
  fun_prop

noncomputable def tableLayer (states : List (List Code)) (m : ℚ) (tab : ExpressionTable) :
    ExpressionTable := states.map (fun cs => (cs, layerExpression m tab cs))

@[fun_prop] theorem tableLayer_computable :
    Computable (fun p : List (List Code) × ℚ × ExpressionTable => tableLayer p.1 p.2.1 p.2.2) := by
  unfold tableLayer
  apply computable_list_map Computable.fst
  unfold Computable₂
  fun_prop

noncomputable def hierarchyTable (states : List (List Code)) (ms : List ℚ)
    (initial : ExpressionTable) : ExpressionTable :=
  ms.foldr (fun m tab => tableLayer states m tab) initial

@[fun_prop] theorem hierarchyTable_computable :
    Computable (fun p : List (List Code) × List ℚ × ExpressionTable =>
      hierarchyTable p.1 p.2.1 p.2.2) := by
  unfold hierarchyTable
  exact computable_list_foldr
    (f := fun p : List (List Code) × List ℚ × ExpressionTable => p.2.1)
    (g := fun p => p.2.2) (h := fun p q => tableLayer p.1 q.1 q.2)
    (by fun_prop) (by fun_prop) (by unfold Computable₂; fun_prop)

noncomputable def listLogMean : List ℚ → (List Code → ℝ) → List Code → ℝ
  | [], g, cs => g cs
  | m::ms, g, cs => Real.log (branchSum (chooseChildren cs)
      (fun ds => Real.exp ((m : ℝ)*listLogMean ms g ds))) / (m : ℝ)

theorem layerExpression_value (m : ℚ) (tab : ExpressionTable) (cs : List Code) :
    expressionValue (layerExpression m tab cs) =
      Real.log (branchSum (chooseChildren cs)
        (fun ds => Real.exp ((m : ℝ)*expressionValue (tableLookup tab ds)))) / (m : ℝ) := by
  have hw : ∀ b ∈ (chooseChildren cs).map (fun b =>
      (b.1, Code.comp (rationalExpression m) (tableLookup tab b.2))), 0 ≤ b.1 := by
    intro b hb
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
    exact chooseChildren_nonneg cs d hd
  have hs : (((chooseChildren cs).map (fun b =>
      (b.1, Code.comp (rationalExpression m) (tableLookup tab b.2)))).map Prod.fst).sum = 1 := by
    simpa only [List.map_map, Function.comp_def] using chooseChildren_sum cs
  simp only [layerExpression, expressionValue, rationalExpression_value, Rat.cast_inv,
    logMixtureExpression_value _ hw hs, List.map_map, Function.comp_def, branchSum]
  ring

theorem chooseChildren_in_states {B L : ℕ} {cs : List Code}
    (hcs : cs ∈ hierarchyStates B L) :
    ∀ b ∈ chooseChildren cs, b.2 ∈ hierarchyStates B L := by
  obtain ⟨hL, hB⟩ := (mem_hierarchyStates B L cs).mp hcs
  intro b hb
  apply (mem_hierarchyStates B L b.2).mpr
  refine ⟨(chooseChildren_length cs b hb).trans hL, ?_⟩
  have hall : ∀ c ∈ cs, Encodable.encode c ≤ B := hB
  clear hL hcs hB
  induction cs generalizing b with
  | nil =>
    have he : b = (1, []) := by simpa only [chooseChildren, List.foldr_nil, List.mem_singleton] using hb
    simp [he]
  | cons c cs ih =>
    obtain ⟨x, hx, hymap⟩ := List.mem_flatMap.mp hb
    obtain ⟨y, hymem, rfl⟩ := List.mem_map.mp hymap
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact (normalizedBranches_code_le c x hx).trans (hall c (by simp))
    · exact ih y hymem (fun z hz => hall z (List.mem_cons_of_mem c hz)) d hd

theorem hierarchyTable_value (B L : ℕ) (ms : List ℚ) (initial : ExpressionTable)
    (g : List Code → ℝ)
    (hinit : ∀ cs ∈ hierarchyStates B L, expressionValue (tableLookup initial cs) = g cs)
    (cs : List Code) (hcs : cs ∈ hierarchyStates B L) :
    expressionValue (tableLookup (hierarchyTable (hierarchyStates B L) ms initial) cs) =
      listLogMean ms g cs := by
  induction ms generalizing cs with
  | nil => exact hinit cs hcs
  | cons m ms ih =>
    change expressionValue (tableLookup
      (tableLayer (hierarchyStates B L) m (hierarchyTable (hierarchyStates B L) ms initial)) cs) = _
    rw [tableLayer, tableLookup_map _ _ hcs,
      layerExpression_value, listLogMean]
    congr 2
    unfold branchSum
    congr 1
    apply List.map_congr_left
    intro b hb
    change (b.1 : ℝ) * Real.exp ((m : ℝ) * expressionValue
      (tableLookup (hierarchyTable (hierarchyStates B L) ms initial) b.2)) =
        (b.1 : ℝ) * Real.exp ((m : ℝ) * listLogMean ms g b.2)
    rw [ih b.2 (chooseChildren_in_states hcs b hb)]

end FixedClauseThreshold.Computability

end OAI
