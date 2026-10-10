import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.BoundedIteration
import OAI.Combinatorics.IndependentSets.Reduction.StoredFloyd

namespace OAI

namespace LargeIndependentSets.StoredFloyd
open ShortestPaths
open IndependentSetsCut.CounterMachine
open IndependentSetsGames.Foundations.Complexity
open Turing

structure Input (B : ℕ) where
  n : ℕ
  matrix : Capped.Matrix B n

def Input.initial {B : ℕ} (a : Input B) : State B := ⟨a.n,0,a.matrix⟩
def Input.bits {B : ℕ} (a : Input B) : List Bool :=
  BoundedIteration.counted Input.n State.bits Input.initial a

def Input.output {B : ℕ} (a : Input B) : State B := ⟨a.n,a.n,a.matrix.allPairs⟩

lemma run_append {B n : ℕ} (a : Capped.Matrix B n) (xs ys : List (Fin n)) :
    a.run (xs++ys) = (a.run xs).run ys := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => exact ih (a.pivot x)

lemma iterate_initial {B : ℕ} (a : Input B) (i : ℕ) (hi : i≤a.n) :
    State.step^[i] a.initial = ⟨a.n,i,a.matrix.run ((List.finRange a.n).take i)⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hn : i<a.n := hi
    rw [Function.iterate_succ_apply',ih hn.le]
    have hl : i<(List.finRange a.n).length := by simpa using hn
    rw [List.take_succ_eq_append_getElem hl]
    simp only [List.getElem_finRange,run_append,Capped.Matrix.run]
    simp only [State.step,dite_eq_left hn]
    congr 2

lemma iterate_output {B : ℕ} (a : Input B) : State.step^[a.n] a.initial = a.output := by
  rw [iterate_initial a a.n le_rfl]
  simp only [Input.output,Capped.Matrix.allPairs]
  rw [List.take_of_length_le (by simp)]

lemma entry_le {B n : ℕ} (a : Capped.Matrix B n) (i j : ℕ) : entry a i j≤B+1 := by
  unfold entry
  split
  · split
    · exact (a.get _ _).bound
    · omega
  · omega

lemma value_le {B : ℕ} (s : State B) (i : ℕ) : s.value i ≤ s.n+s.k+B+1 := by
  unfold State.value
  split
  · omega
  · split
    · omega
    · have := entry_le s.matrix ((i-2)/s.n) ((i-2)%s.n); omega

lemma bits_length_le {B : ℕ} (s : State B) :
    s.bits.length ≤ (2+s.n*s.n)*(s.n+s.k+B+2) := by
  rw [State.bits,UnaryTables.words_length]
  unfold UnaryTables.offset
  calc
    _ ≤ ∑ _ ∈ Finset.range (2+s.n*s.n), (s.n+s.k+B+2) := by
      apply Finset.sum_le_sum
      intro i _hi
      have := value_le s i
      omega
    _ = _ := by simp

noncomputable def lengthPolynomial (B : ℕ) : Polynomial ℕ :=
  (2+Polynomial.X*Polynomial.X)*(2*Polynomial.X+Polynomial.C (B+2))

lemma lengthPolynomial_eval (B N : ℕ) : (lengthPolynomial B).eval N = (2+N*N)*(2*N+B+2) := by
  simp [lengthPolynomial,Nat.add_assoc]

lemma intermediate_bound {B : ℕ} (a : Input B) (i : ℕ) (hi : i≤a.n) :
    (State.step^[i] a.initial).bits.length ≤ (lengthPolynomial B).eval a.bits.length := by
  rw [iterate_initial a i hi,lengthPolynomial_eval]
  have hn : a.n≤a.bits.length := BoundedIteration.count_le Input.n State.bits Input.initial a
  have hk : i≤a.bits.length := hi.trans hn
  apply (bits_length_le _).trans
  dsimp only
  gcongr; omega

noncomputable def rawCertificate (B : ℕ) :
    TM2ComputableInPolyTime Input.bits State.bits
      (fun a : Input B => State.step^[a.n] a.initial) :=
  BoundedIteration.certificate State.bits State.step Input.initial Input.n (body B)
    (lengthPolynomial B) intermediate_bound

noncomputable def certificate (B : ℕ) :
    TM2ComputableInPolyTime Input.bits State.bits (@Input.output B) where
  tm := (rawCertificate B).tm
  inputAlphabet := (rawCertificate B).inputAlphabet
  outputAlphabet := (rawCertificate B).outputAlphabet
  time := (rawCertificate B).time
  outputsFun a := by
    simpa only [iterate_output] using (rawCertificate B).outputsFun a

lemma certificate_finiteAlphabet (B : ℕ) (k : (certificate B).tm.K) :
    Finite ((certificate B).tm.Γ k) :=
  BoundedIteration.certificate_finiteAlphabet State.bits State.step Input.initial Input.n
    (body B) (lengthPolynomial B) intermediate_bound (body_finiteAlphabet B) k

lemma output_threshold (B : ℕ) {n : ℕ} (a : ShortestPaths.Matrix n) (i j : Fin n)
    (t : ℕ) (ht : t≤B) :
    ((Input.output (⟨n,Capped.Matrix.ofInteger B a⟩ : Input B)).matrix.get i j).val≤t ↔
      a.allPairs.get i j ≤ (t : ℕ∞) := Capped.Matrix.threshold_exact B a i j ht
end LargeIndependentSets.StoredFloyd
namespace LargeIndependentSets.FloydCarry
open IndependentSetsCut.CounterMachine
open ShortestPaths
open Turing
open scoped BigOperators
open IndependentSetsGames.Foundations.Complexity

structure State (B : ℕ) where
  core : StoredFloyd.State B
  payload : List ℕ

def State.value {B : ℕ} (s : State B) (w : ℕ) : ℕ :=
  if w<2+s.core.n*s.core.n then s.core.value w
  else if w=2+s.core.n*s.core.n then s.payload.length
  else s.payload[w-(3+s.core.n*s.core.n)]?.getD 0

def State.count {B : ℕ} (s : State B) := 3+s.core.n*s.core.n+s.payload.length
def State.bits {B : ℕ} (s : State B) := UnaryTables.words s.value s.count

def State.step {B : ℕ} (s : State B) : State B := ⟨s.core.step,s.payload⟩

lemma read_core {B : ℕ} (s : State B) (w : ℕ) (hw : w<2+s.core.n*s.core.n) :
    Expr.wordValue s.bits w=s.core.value w := by
  rw [State.bits,UnaryTables.wordValue_words _ _ _ (by unfold State.count; omega)]
  simp [State.value,hw]
@[simp] lemma read_n {B : ℕ} (s : State B) : Expr.wordValue s.bits 0=s.core.n := by
  rw [read_core _ _ (by omega)]; simp [StoredFloyd.State.value]
@[simp] lemma read_k {B : ℕ} (s : State B) : Expr.wordValue s.bits 1=s.core.k := by
  rw [read_core _ _ (by omega)]; simp [StoredFloyd.State.value]
@[simp] lemma read_count {B : ℕ} (s : State B) :
    Expr.wordValue s.bits (2+s.core.n*s.core.n)=s.payload.length := by
  rw [State.bits,UnaryTables.wordValue_words _ _ _ (by unfold State.count; omega)]
  simp [State.value]
lemma read_payload {B : ℕ} (s : State B) (w : ℕ) (hw : w<s.payload.length) :
    Expr.wordValue s.bits (3+s.core.n*s.core.n+w)=s.payload[w] := by
  rw [State.bits,UnaryTables.wordValue_words _ _ _ (by unfold State.count; omega)]
  simp [State.value,show ¬3+s.core.n*s.core.n+w<2+s.core.n*s.core.n by omega,
    show 3+s.core.n*s.core.n+w ≠ 2+s.core.n*s.core.n by omega,
    show 3+s.core.n*s.core.n+w-(3+s.core.n*s.core.n)=w by omega,hw]

lemma read_cell {B : ℕ} (s : State B) (i j : Fin s.core.n) :
    Expr.wordValue s.bits (2+i.val*s.core.n+j.val)=(s.core.matrix.get i j).val := by
  have hlt : i.val*s.core.n+j.val<s.core.n*s.core.n := by
    calc
      _ < (i.val+1)*s.core.n := by nlinarith [j.isLt]
      _ ≤ _ := Nat.mul_le_mul_right _ i.isLt
  rw [read_core _ _ (by omega)]
  rw [← StoredFloyd.read_cell s.core i j,StoredFloyd.State.bits,
    UnaryTables.wordValue_words _ _ _ (by omega)]

@[simp] lemma sizeExpr_eval {B : ℕ} (s : State B) (a : ℕ → ℕ) :
    StoredFloyd.sizeExpr.eval s.bits a=s.core.n := by simp [StoredFloyd.sizeExpr,Expr.eval]
@[simp] lemma pivotExpr_eval {B : ℕ} (s : State B) (a : ℕ → ℕ) :
    StoredFloyd.pivotExpr.eval s.bits a=s.core.k := by simp [StoredFloyd.pivotExpr,Expr.eval]
@[simp] lemma coreCount_eval {B : ℕ} (s : State B) (a : ℕ → ℕ) :
    StoredFloyd.countExpr.eval s.bits a=2+s.core.n*s.core.n := by simp [StoredFloyd.countExpr,Expr.eval]

def payloadCountExpr : Expr := Expr.word StoredFloyd.countExpr

def countExpr : Expr := .add (.add StoredFloyd.countExpr (.const 1)) payloadCountExpr

def valueExpr (B : ℕ) : Expr :=
  Expr.cond (Expr.lt (.arg 0) StoredFloyd.countExpr) (StoredFloyd.valueExpr B) (Expr.word (.arg 0))

lemma coreValue_eval {B : ℕ} (s : State B) (w : ℕ) (hw : w<2+s.core.n*s.core.n) :
    (StoredFloyd.valueExpr B).eval s.bits (fun _ => w)=s.core.step.value w := by
  by_cases hw0 : w=0
  · subst w; simp [StoredFloyd.valueExpr,Expr.eval,StoredFloyd.State.value,StoredFloyd.State.step]
  by_cases hw1 : w=1
  · subst w; simp [StoredFloyd.valueExpr,Expr.eval,StoredFloyd.State.value,StoredFloyd.State.step]
  have hw2 : 2 ≤ w := by omega
  have ht : w-2<s.core.n*s.core.n := by omega
  have hn : 0<s.core.n := by nlinarith
  have hi : (w-2)/s.core.n<s.core.n := (Nat.div_lt_iff_lt_mul hn).mpr ht
  have hj : (w-2)%s.core.n<s.core.n := Nat.mod_lt _ hn
  let i : Fin s.core.n := ⟨(w-2)/s.core.n,hi⟩
  let j : Fin s.core.n := ⟨(w-2)%s.core.n,hj⟩
  have hr : StoredFloyd.rowExpr.eval s.bits (fun _ => w)=i.val := by simp [StoredFloyd.rowExpr,Expr.eval,i]
  have hc : StoredFloyd.colExpr.eval s.bits (fun _ => w)=j.val := by simp [StoredFloyd.colExpr,Expr.eval,j]
  simp only [StoredFloyd.valueExpr,Expr.cond_eval,Expr.equal_eval,Expr.eval,hw0,hw1,ite_false,
    ne_eq,not_true_eq_false,
    sizeExpr_eval,pivotExpr_eval,Expr.lt_eval,StoredFloyd.minExpr_eval,StoredFloyd.cellExpr_eval,hr,hc]
  by_cases hk : s.core.k<s.core.n
  · let k : Fin s.core.n := ⟨s.core.k,hk⟩
    simp only [hk,ite_true,Nat.one_ne_zero,not_false_eq_true]
    rw [read_cell s i j,show s.core.k=k.val from rfl,read_cell s i k,read_cell s k j]
    simp [StoredFloyd.State.value,StoredFloyd.State.step,hw0,hw1,hk,
      StoredFloyd.entry,hi,hj,Capped.Matrix.pivot,Capped.Matrix.get,pivot,Capped.min_val,Capped.add_val,i,j,k]
  · simp only [hk,ite_false,not_true_eq_false,read_cell]
    simp [StoredFloyd.State.value,StoredFloyd.State.step,hw0,hw1,hk,StoredFloyd.entry,hi,hj,i,j]

@[simp] lemma payloadCount_eval {B : ℕ} (s : State B) (a : ℕ → ℕ) :
    payloadCountExpr.eval s.bits a=s.payload.length := by simp [payloadCountExpr,Expr.word_eval]
@[simp] lemma countExpr_eval {B : ℕ} (s : State B) (a : ℕ → ℕ) :
    countExpr.eval s.bits a=s.count := by simp [countExpr,Expr.eval,State.count]; omega

lemma valueExpr_eval {B : ℕ} (s : State B) (w : ℕ) (hw : w<s.count) :
    (valueExpr B).eval s.bits (fun _ => w)=s.step.value w := by
  simp only [valueExpr,Expr.cond_eval,Expr.lt_eval,Expr.eval,coreCount_eval]
  by_cases hc : w<2+s.core.n*s.core.n
  · simp [hc,coreValue_eval s w hc,State.value,State.step,StoredFloyd.State.step]
  · simp only [hc,ite_false,ne_eq,not_true_eq_false,Expr.word_eval,Expr.eval]
    rw [State.bits,UnaryTables.wordValue_words _ _ _ hw]
    simp only [State.value,State.step,StoredFloyd.State.step,hc,ite_false]
    rfl

lemma body_spec {B : ℕ} (s : State B) :
    UnaryTables.words (fun w => (valueExpr B).eval s.bits (fun _ => w))
      (countExpr.eval s.bits (fun _ => 0))=s.step.bits := by
  rw [countExpr_eval]
  exact UnaryTables.words_congr (valueExpr_eval s)

noncomputable def body (B : ℕ) : TM2ComputableInPolyTime State.bits State.bits (@State.step B) :=
  UnaryTables.encodedComputer _ _ _ countExpr (valueExpr B) body_spec
lemma body_finiteAlphabet (B : ℕ) : MachineFiniteAlphabet.FiniteAlphabet (body B).tm :=
  UnaryTables.encodedComputer_finiteAlphabet _ _ _ _ _ _

structure Input (B : ℕ) where
  core : StoredFloyd.Input B
  payload : List ℕ

def Input.initial {B : ℕ} (a : Input B) : State B := ⟨a.core.initial,a.payload⟩
def Input.count {B : ℕ} (a : Input B) := a.core.n
def Input.bits {B : ℕ} (a : Input B) : List Bool :=
  BoundedIteration.counted Input.count State.bits Input.initial a

def Input.output {B : ℕ} (a : Input B) : State B := ⟨a.core.output,a.payload⟩

lemma iterate_pair {B : ℕ} (s : State B) (i : ℕ) :
    State.step^[i] s=⟨StoredFloyd.State.step^[i] s.core,s.payload⟩ := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']; rfl

lemma iterate_output {B : ℕ} (a : Input B) : State.step^[a.count] a.initial=a.output := by
  rw [iterate_pair]
  dsimp only [Input.initial,Input.count,Input.output]
  rw [StoredFloyd.iterate_output]

lemma wordValue_le_length (s : List Bool) (w : ℕ) : Expr.wordValue s w ≤ s.length := by
  unfold Expr.wordValue
  calc
    _ ≤ ∑ _ ∈ Finset.range s.length, (1:ℕ) := by
      apply Finset.sum_le_sum
      intro i _hi
      unfold Expr.bitValue
      split <;> split <;> simp
    _ = _ := by simp

lemma initial_length_le {B : ℕ} (a : Input B) : a.initial.bits.length≤a.bits.length := by
  simp [Input.bits,BoundedIteration.counted]

lemma payload_length_le {B : ℕ} (a : Input B) : a.payload.length≤a.bits.length := by
  change a.initial.payload.length ≤ a.bits.length
  rw [← read_count a.initial]
  exact (wordValue_le_length _ _).trans (initial_length_le a)

lemma payload_value_le {B : ℕ} (a : Input B) (w : ℕ) :
    a.payload[w]?.getD 0≤a.bits.length := by
  by_cases hw : w<a.payload.length
  · rw [List.getElem?_eq_getElem hw,Option.getD_some]
    change a.initial.payload[w] ≤ a.bits.length
    rw [← read_payload a.initial w hw]
    exact (wordValue_le_length _ _).trans (initial_length_le a)
  · simp [List.getElem?_eq_none (by omega : a.payload.length≤w)]

lemma bits_length_le {B : ℕ} (s : State B) (N : ℕ)
    (hn : s.core.n≤N) (hk : s.core.k≤N) (hc : s.payload.length≤N)
    (hp : ∀ w : ℕ, s.payload[w]?.getD 0≤N) :
    s.bits.length≤(3+N*N+N)*(2*N+B+2) := by
  rw [State.bits,UnaryTables.words_length]
  unfold UnaryTables.offset
  calc
    _ ≤ ∑ _ ∈ Finset.range s.count, (2*N+B+2) := by
      apply Finset.sum_le_sum
      intro w _hw
      have hv : s.value w≤2*N+B+1 := by
        unfold State.value
        split
        · have := StoredFloyd.value_le s.core w; omega
        · split
          · omega
          · have := hp (w-(3+s.core.n*s.core.n)); omega
      omega
    _ = s.count*(2*N+B+2) := by simp
    _ ≤ _ := by unfold State.count; gcongr

noncomputable def lengthPolynomial (B : ℕ) : Polynomial ℕ :=
  (3+Polynomial.X*Polynomial.X+Polynomial.X)*(2*Polynomial.X+Polynomial.C (B+2))

lemma lengthPolynomial_eval (B N : ℕ) :
    (lengthPolynomial B).eval N=(3+N*N+N)*(2*N+B+2) := by
  simp [lengthPolynomial,Nat.add_assoc]

lemma intermediate_bound {B : ℕ} (a : Input B) (i : ℕ) (hi : i≤a.count) :
    (State.step^[i] a.initial).bits.length≤(lengthPolynomial B).eval a.bits.length := by
  have hn : a.core.n≤a.bits.length :=
    BoundedIteration.count_le Input.count State.bits Input.initial a
  rw [iterate_pair]
  dsimp only [Input.initial]
  rw [StoredFloyd.iterate_initial a.core i hi,lengthPolynomial_eval]
  apply bits_length_le
  · exact hn
  · exact hi.trans hn
  · exact payload_length_le a
  · exact payload_value_le a

noncomputable def rawCertificate (B : ℕ) :
    TM2ComputableInPolyTime Input.bits State.bits
      (fun a : Input B => State.step^[a.count] a.initial) :=
  BoundedIteration.certificate State.bits State.step Input.initial Input.count (body B)
    (lengthPolynomial B) intermediate_bound

noncomputable def certificate (B : ℕ) :
    TM2ComputableInPolyTime Input.bits State.bits (@Input.output B) where
  tm := (rawCertificate B).tm
  inputAlphabet := (rawCertificate B).inputAlphabet
  outputAlphabet := (rawCertificate B).outputAlphabet
  time := (rawCertificate B).time
  outputsFun a := by simpa only [iterate_output] using (rawCertificate B).outputsFun a

lemma certificate_finiteAlphabet (B : ℕ) (k : (certificate B).tm.K) :
    Finite ((certificate B).tm.Γ k) :=
  BoundedIteration.certificate_finiteAlphabet State.bits State.step Input.initial Input.count
    (body B) (lengthPolynomial B) intermediate_bound (body_finiteAlphabet B) k

end LargeIndependentSets.FloydCarry

end OAI
