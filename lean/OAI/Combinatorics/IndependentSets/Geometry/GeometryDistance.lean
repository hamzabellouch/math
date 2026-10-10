import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.IntegerEdgeTest
import OAI.Combinatorics.IndependentSets.Geometry.GeometryInitialize
import OAI.Combinatorics.IndependentSets.Machines.ExprDrop

namespace OAI

namespace LargeIndependentSets.GeometryNames
open IndependentSetsCut.CounterMachine UniformLC ShortestPaths
open IndependentSetsGames.Foundations.Complexity Turing
open scoped Classical BigOperators ENNReal
noncomputable section

variable (L R : Type) [Fintype L] [Fintype R] (n D : ℕ) [NeZero D]

def distances (t : Table L R) := (input L R n D t).output

noncomputable def distanceComputer : TM2ComputableInPolyTime Table.bits FloydCarry.State.bits (distances L R n D) :=
  MachineSequential.composeBits (f:=input L R n D) (g:=@FloydCarry.Input.output D)
    (initializer L R n D) (FloydCarry.certificate D)
lemma distanceComputer_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet (distanceComputer L R n D).tm :=
  MachineFiniteAlphabet.composeBits _ _ (initializer_finiteAlphabet L R n D) (FloydCarry.certificate_finiteAlphabet D)

omit [NeZero D] in
lemma enat_eighth (c : ℕ∞) : 8*c≤(D:ℕ∞) ↔ c≤((D/8:ℕ):ℕ∞) := by
  induction c using ENat.recTopCoe with
  | top => simp
  | coe c =>
    have hh : (8:ℕ∞)*(c:ℕ∞)=((8*c:ℕ):ℕ∞) := by norm_cast
    rw [hh,ENat.natCast_le_natCast,ENat.natCast_le_natCast]
    omega

lemma distance_threshold (t : Table L R) (i j : Fin (size L R n D t)) :
    ((distances L R n D t).core.matrix.get i j).val≤D/8 ↔
      pathDistance (layeredSystem t.lc n).linkLength
        (names L R n D t.nu t.nv i) (names L R n D t.nu t.nv j)≤ENNReal.ofReal (1/8) := by
  change (((Capped.Matrix.ofInteger D (integerMatrix L R n D t)).allPairs).get i j).val≤D/8 ↔ _
  rw [Capped.Matrix.threshold_exact D _ i j (Nat.div_le_self _ _)]
  rw [← cover_allPairs_exact (layeredSystem t.lc n) (names L R n D t.nu t.nv)
    (names_surjective L R n D t.nu t.nv t.hu t.hv) i j,integer_edge_test]
  exact (enat_eighth D _).symm

abbrev prefixCount (t : Table L R) := 3+size L R n D t*size L R n D t

def payloadOffsetExpr : Expr :=
  .sum (.add (.const 3) (.mul StoredFloyd.sizeExpr StoredFloyd.sizeExpr))
    (.add (Expr.word (.arg 0)) (.const 1))

def fromTable (e : Expr) : Expr := Expr.dropInput payloadOffsetExpr e

lemma distances_suffix (t : Table L R) :
    (distances L R n D t).bits =
      UnaryTables.words (distances L R n D t).value (prefixCount L R n D t) ++ t.bits := by
  have hc : (distances L R n D t).count=prefixCount L R n D t+(3+3*t.ne) := by
    simp [distances,FloydCarry.Input.output,FloydCarry.State.count,StoredFloyd.Input.output,input,prefixCount]
  rw [FloydCarry.State.bits,hc,UnaryTables.words_add]
  congr 1
  apply UnaryTables.words_congr
  intro w hw
  have hprefix : (distances L R n D t).core.n=size L R n D t := rfl
  simp only [FloydCarry.State.value,hprefix]
  have hn : ¬prefixCount L R n D t+w<2+size L R n D t*size L R n D t := by unfold prefixCount; omega
  have he : prefixCount L R n D t+w≠2+size L R n D t*size L R n D t := by unfold prefixCount; omega
  rw [ite_eq_right hn,ite_eq_right he]
  have hs : prefixCount L R n D t+w-(3+size L R n D t*size L R n D t)=w := by unfold prefixCount; omega
  rw [hs]
  exact payload_get L R n D t w hw

lemma payloadOffsetExpr_eval (t : Table L R) (a : ℕ → ℕ) :
    payloadOffsetExpr.eval (distances L R n D t).bits a=
      (UnaryTables.words (distances L R n D t).value (prefixCount L R n D t)).length := by
  simp only [payloadOffsetExpr,Expr.eval,FloydCarry.sizeExpr_eval,UnaryTables.words_length,UnaryTables.offset]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Expr.word_eval,Expr.eval]
  rw [FloydCarry.State.bits,UnaryTables.wordValue_words]
  · rfl
  · change w < 3+(size L R n D t)*(size L R n D t)+(input L R n D t).payload.length
    exact lt_of_lt_of_le (Finset.mem_range.mp hw) (Nat.le_add_right _ _)

lemma fromTable_eval (e : Expr) (t : Table L R) (a : ℕ → ℕ) :
    (fromTable e).eval (distances L R n D t).bits a=e.eval t.bits a := by
  rw [fromTable,Expr.dropInput_eval,payloadOffsetExpr_eval,distances_suffix,List.drop_left]

lemma cellExpr_eval (t : Table L R) (i j : Expr) (a : ℕ → ℕ)
    (x y : Fin (size L R n D t))
    (hi : i.eval (distances L R n D t).bits a=x.val)
    (hj : j.eval (distances L R n D t).bits a=y.val) :
    (StoredFloyd.cellExpr i j).eval (distances L R n D t).bits a=
      ((distances L R n D t).core.matrix.get x y).val := by
  rw [StoredFloyd.cellExpr_eval,hi,hj,FloydCarry.sizeExpr_eval]
  exact FloydCarry.read_cell (distances L R n D t) x y

def closeExpr (i j : Expr) : Expr := Expr.le (StoredFloyd.cellExpr i j) (.const (D/8))

lemma closeExpr_nonzero (t : Table L R) (i j : Expr) (a : ℕ → ℕ)
    (x y : Fin (size L R n D t))
    (hi : i.eval (distances L R n D t).bits a=x.val)
    (hj : j.eval (distances L R n D t).bits a=y.val) :
    (closeExpr D i j).eval (distances L R n D t).bits a≠0 ↔
      pathDistance (layeredSystem t.lc n).linkLength (names L R n D t.nu t.nv x)
        (names L R n D t.nu t.nv y)≤ENNReal.ofReal (1/8) := by
  rw [closeExpr,Expr.le_eval,cellExpr_eval L R n D t i j a x y hi hj,Expr.eval]
  rw [← distance_threshold L R n D t x y]
  split_ifs <;> simp_all

end
end LargeIndependentSets.GeometryNames

end OAI
