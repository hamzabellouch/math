import Mathlib
import OAI.Combinatorics.IndependentSets.Geometry.GeometryLink
import OAI.Combinatorics.IndependentSets.Reduction.FloydLoop

namespace OAI

namespace IndependentSetsCut.CounterMachine.UnaryTables
lemma words_cons (f : ℕ → ℕ) (n : ℕ) :
    words f (n+1)=IndependentSetsGames.Foundations.Complexity.encodeWord (f 0) ++ words (fun w => f (w+1)) n := by
  simp [words,List.range_succ_eq_map,List.map_map,IndependentSetsGames.Foundations.Complexity.encodeWord,Function.comp_def]
end IndependentSetsCut.CounterMachine.UnaryTables

namespace LargeIndependentSets.GeometryNames
open IndependentSetsCut.CounterMachine UniformLC ShortestPaths
open IndependentSetsGames.Foundations.Complexity Turing
open scoped Classical BigOperators ENNReal
noncomputable section

variable (L R : Type) [Fintype L] [Fintype R] (n D : ℕ) [NeZero D]

def integerMatrix (t : Table L R) : ShortestPaths.Matrix (size L R n D t) :=
  Vector.ofFn (fun i => Vector.ofFn (fun j =>
    linkCost (layeredSystem t.lc n) (names L R n D t.nu t.nv i) (names L R n D t.nu t.nv j)))

def input (t : Table L R) : FloydCarry.Input D :=
  ⟨⟨size L R n D t,Capped.Matrix.ofInteger D (integerMatrix L R n D t)⟩,
    (List.range (3+3*t.ne)).map t.value⟩

lemma payload_length (t : Table L R) : (input L R n D t).payload.length=3+3*t.ne := by simp [input]
lemma payload_get (t : Table L R) (w : ℕ) (hw : w<3+3*t.ne) :
    (input L R n D t).payload[w]?.getD 0=t.value w := by simp [input,hw]

abbrev inputCount (t : Table L R) := 4+(size L R n D t)*(size L R n D t)+(3+3*t.ne)
def inputValue (t : Table L R) (w : ℕ) : ℕ :=
  if w=0 then size L R n D t else (input L R n D t).initial.value (w-1)

lemma input_bits (t : Table L R) :
    FloydCarry.Input.bits (input L R n D t)=UnaryTables.words (inputValue L R n D t) (inputCount L R n D t) := by
  have hc : inputCount L R n D t=(input L R n D t).initial.count+1 := by
    simp [inputCount,FloydCarry.State.count,FloydCarry.Input.initial,StoredFloyd.Input.initial,input]; omega
  rw [hc,UnaryTables.words_cons]
  simp only [inputValue,↓reduceIte,Nat.add_eq_zero_iff,one_ne_zero,and_false,Nat.add_sub_cancel]
  rfl

def inputCountExpr : Expr := .add (.add (.const 4) (.mul (sizeExpr L R n D) (sizeExpr L R n D)))
  (.add (.const 3) (.mul (.const 3) neExpr))

def inputValueExpr : Expr :=
  Expr.cond (Expr.lt (.arg 0) (.const 2)) (sizeExpr L R n D)
    (Expr.cond (Expr.equal (.arg 0) (.const 2)) (.const 0)
      (Expr.cond (Expr.lt (.arg 0) (.add (.const 3) (.mul (sizeExpr L R n D) (sizeExpr L R n D))))
        (costExpr L R n D (Expr.quotient (.sub (.arg 0) (.const 3)) (sizeExpr L R n D))
          (Expr.remainder (.sub (.arg 0) (.const 3)) (sizeExpr L R n D)))
        (Expr.cond (Expr.equal (.arg 0) (.add (.const 3) (.mul (sizeExpr L R n D) (sizeExpr L R n D))))
          (.add (.const 3) (.mul (.const 3) neExpr))
          (Expr.word (.sub (.arg 0) (.add (.const 4) (.mul (sizeExpr L R n D) (sizeExpr L R n D))))))))

@[simp] lemma inputCountExpr_eval (t : Table L R) (a : ℕ → ℕ) :
    (inputCountExpr L R n D).eval t.bits a=inputCount L R n D t := by
  simp [inputCountExpr,Expr.eval,inputCount]

lemma inputValueExpr_eval (t : Table L R) (w : ℕ) (hw : w < inputCount L R n D t) :
    (inputValueExpr L R n D).eval t.bits (fun _ => w)=inputValue L R n D t w := by
  let N := size L R n D t
  have hN : 0<N := size_pos L R n D t
  have hc : (input L R n D t).initial.core.n=N := rfl
  have hk : (input L R n D t).initial.core.k=0 := rfl
  have hp : (input L R n D t).initial.payload=(input L R n D t).payload := rfl
  have indicator (P : Prop) [Decidable P] : (if P then (1:ℕ) else 0)≠0 ↔ P := by
    split_ifs <;> simp_all
  simp only [inputValueExpr,Expr.cond_eval,Expr.lt_eval,Expr.equal_eval,Expr.eval,sizeExpr_eval,neExpr_eval,indicator]
  have hsize : N=size L R n D t := rfl
  simp only [← hsize]
  by_cases hsmall : w<2
  · have hw' : w=0 ∨ w=1 := by omega
    rcases hw' with rfl | rfl <;>
      simp [inputValue,FloydCarry.State.value,StoredFloyd.State.value,hc,N]
  · simp only [hsmall,ite_false,ne_eq,not_true_eq_false]
    by_cases hw2 : w=2
    · subst w
      simp [inputValue,FloydCarry.State.value,StoredFloyd.State.value,hc,hk,N,show (1:ℕ)<2+N*N by omega]
    · have hw3 : 3≤w := by omega
      simp only [hw2,ite_false,not_true_eq_false]
      by_cases hmat : w<3+N*N
      · have hi : (w-3)/N<N := (Nat.div_lt_iff_lt_mul hN).mpr (by omega)
        have hj : (w-3)%N<N := Nat.mod_lt _ hN
        let i : Fin N := ⟨(w-3)/N,hi⟩
        let j : Fin N := ⟨(w-3)%N,hj⟩
        have hei : (Expr.quotient (.sub (.arg 0) (.const 3)) (sizeExpr L R n D)).eval t.bits (fun _ => w)=i.val := by
          simp [Expr.quotient_eval,Expr.eval,i,N]
        have hej : (Expr.remainder (.sub (.arg 0) (.const 3)) (sizeExpr L R n D)).eval t.bits (fun _ => w)=j.val := by
          simp [Expr.remainder_eval,Expr.eval,j,N]
        simp only [hmat,ite_true]
        rw [costExpr_eval L R n D t _ _ _ i j hei hej]
        simp [inputValue,FloydCarry.State.value,show w≠0 by omega,
          show w-1<2+N*N by omega,StoredFloyd.State.value,show w-1≠0 by omega,
          show w-1≠1 by omega,show w-1-2=w-3 by omega,
          input,FloydCarry.Input.initial,StoredFloyd.Input.initial,StoredFloyd.entry,hi,hj,
          Capped.Matrix.ofInteger,Capped.Matrix.get,integerMatrix,ShortestPaths.Matrix.get,i,j,N]
      · simp only [hmat,ite_false]
        by_cases hend : w=3+N*N
        · simp only [hend,ite_true]
          simp [inputValue,FloydCarry.State.value,hc,hp,payload_length,N]
        · simp only [hend,ite_false,Expr.word_eval,Expr.eval,sizeExpr_eval]
          have hoff : w-(4+N*N)<3+3*t.ne := by change w < 4+N*N+(3+3*t.ne) at hw; omega
          rw [Table.bits,UnaryTables.wordValue_words _ _ _ hoff]
          simp [inputValue,FloydCarry.State.value,hc,hp,show w≠0 by omega,
            show ¬w-1<2+N*N by omega,show w-1≠2+N*N by omega,
            show w-1-(3+N*N)=w-(4+N*N) by omega,payload_get L R n D t _ hoff,N]

lemma input_spec (t : Table L R) :
    UnaryTables.words (fun w => (inputValueExpr L R n D).eval t.bits (fun _ => w))
      ((inputCountExpr L R n D).eval t.bits (fun _ => 0))=FloydCarry.Input.bits (input L R n D t) := by
  rw [inputCountExpr_eval,input_bits]
  exact UnaryTables.words_congr (inputValueExpr_eval L R n D t)

noncomputable def initializer : TM2ComputableInPolyTime Table.bits FloydCarry.Input.bits (input L R n D) :=
  UnaryTables.encodedComputer _ _ _ (inputCountExpr L R n D) (inputValueExpr L R n D) (input_spec L R n D)
lemma initializer_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet (initializer L R n D).tm :=
  UnaryTables.encodedComputer_finiteAlphabet _ _ _ _ _ _

end
end LargeIndependentSets.GeometryNames

end OAI
