import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.BoundedIteration
import OAI.Combinatorics.IndependentSets.Reduction.StoredFloyd

namespace OAI

namespace LargeIndependentSets.FiniteScan
open IndependentSetsCut.CounterMachine
open IndependentSetsGames.Foundations.Complexity
open Turing
open scoped BigOperators

structure State (m : ℕ) where
  input : List Bool
  k : ℕ
  history : ℕ → Fin m

def State.value {m : ℕ} (s : State m) (w : ℕ) : ℕ :=
  if w=0 then s.input.length else if w=1 then s.k else
    if w<2+s.input.length then Expr.bitValue s.input (w-2)
    else (s.history (w-(2+s.input.length))).val

def State.bits {m : ℕ} (s : State m) : List Bool :=
  UnaryTables.words s.value (3+2*s.input.length)

def initial {m : ℕ} (q : Fin m) (input : List Bool) : State m := ⟨input,0,fun _ => q⟩

def step {m : ℕ} (δ : Fin m → Bool → Fin m) (s : State m) : State m where
  input := s.input
  k := s.k+1
  history := if h : s.k<s.input.length then
    Function.update s.history (s.k+1) (δ (s.history s.k) s.input[s.k]) else s.history

@[simp] lemma read_n {m : ℕ} (s : State m) : Expr.wordValue s.bits 0 = s.input.length := by
  rw [State.bits,UnaryTables.wordValue_words _ _ _ (by omega)]
  simp [State.value]
@[simp] lemma read_k {m : ℕ} (s : State m) : Expr.wordValue s.bits 1 = s.k := by
  rw [State.bits,UnaryTables.wordValue_words _ _ _ (by omega)]
  simp [State.value]

lemma read_input {m : ℕ} (s : State m) (i : ℕ) (hi : i<s.input.length) :
    Expr.wordValue s.bits (2+i) = Expr.bitValue s.input i := by
  rw [State.bits,UnaryTables.wordValue_words _ _ _ (by omega)]
  simp [State.value,show 2+i≠1 by omega,show 2+i<2+s.input.length by omega]

lemma read_history {m : ℕ} (s : State m) (i : ℕ) (hi : i ≤ s.input.length) :
    Expr.wordValue s.bits (2+s.input.length+i) = (s.history i).val := by
  rw [State.bits,UnaryTables.wordValue_words _ _ _ (by omega)]
  simp [State.value,
    show 2+s.input.length+i≠1 by omega,show ¬2+s.input.length+i<2+s.input.length by omega]

def nExpr : Expr := .word (.const 0)
def kExpr : Expr := .word (.const 1)
def inputExpr (i : Expr) : Expr := .word (.add (.const 2) i)
def historyExpr (i : Expr) : Expr := .word (.add (.add (.const 2) nExpr) i)

def transitionExpr {m : ℕ} (δ : Fin m → Bool → Fin m) (q b : Expr) : Expr :=
  Expr.listSum (List.finRange m) (fun i => .mul (Expr.equal q (.const i.val))
    (Expr.cond b (.const (δ i true).val) (.const (δ i false).val)))

lemma transitionExpr_eval {m : ℕ} (δ : Fin m → Bool → Fin m) (q b : Expr)
    (s : List Bool) (args : ℕ → ℕ) (i : Fin m) (c : Bool)
    (hq : q.eval s args=i.val) (hb : b.eval s args=if c then 1 else 0) :
    (transitionExpr δ q b).eval s args = (δ i c).val := by
  simp only [transitionExpr,Expr.listSum_eval,Expr.eval,Expr.equal_eval,Expr.cond_eval,hq,hb]
  cases c <;> simp only [Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false,
    one_ne_zero, not_false_eq_true]
  all_goals
    rw [← List.ofFn_eq_map, List.sum_ofFn]
    simp [Fin.val_inj]

@[simp] lemma nExpr_eval {m : ℕ} (s : State m) (args : ℕ → ℕ) :
    nExpr.eval s.bits args = s.input.length := by simp [nExpr,Expr.eval]
@[simp] lemma kExpr_eval {m : ℕ} (s : State m) (args : ℕ → ℕ) :
    kExpr.eval s.bits args = s.k := by simp [kExpr,Expr.eval]

@[simp] lemma inputExpr_eval (i : Expr) (s : List Bool) (args : ℕ → ℕ) :
    (inputExpr i).eval s args = Expr.wordValue s (2+i.eval s args) := by simp [inputExpr,Expr.eval]
@[simp] lemma historyExpr_eval (i : Expr) (s : List Bool) (args : ℕ → ℕ) :
    (historyExpr i).eval s args = Expr.wordValue s (2+nExpr.eval s args+i.eval s args) := by
  simp [historyExpr,Expr.eval]

def countExpr : Expr := .add (.const 3) (.mul (.const 2) nExpr)
def valueExpr {m : ℕ} (δ : Fin m → Bool → Fin m) : Expr :=
  Expr.cond (Expr.equal (.arg 0) (.const 1)) (.add kExpr (.const 1))
    (Expr.cond (.mul (Expr.lt kExpr nExpr)
      (Expr.equal (.arg 0) (.add (.add (.const 3) nExpr) kExpr)))
      (transitionExpr δ (historyExpr kExpr) (inputExpr kExpr)) (.word (.arg 0)))

lemma valueExpr_eval {m : ℕ} (δ : Fin m → Bool → Fin m) (s : State m)
    (w : ℕ) (hw : w<3+2*s.input.length) :
    (valueExpr δ).eval s.bits (fun _ => w) = (step δ s).value w := by
  have old := UnaryTables.wordValue_words s.value (3+2*s.input.length) w hw
  change Expr.wordValue s.bits w = s.value w at old
  by_cases hw1 : w=1
  · subst w
    simp [valueExpr,Expr.eval,State.value,step]
  by_cases hk : s.k<s.input.length
  · have ht : (transitionExpr δ (historyExpr kExpr) (inputExpr kExpr)).eval s.bits (fun _ => w) =
        (δ (s.history s.k) s.input[s.k]).val := by
      apply transitionExpr_eval
      · simp [read_history s s.k hk.le]
      · simp [read_input s s.k hk,Expr.bitValue,List.getElem?_eq_getElem hk]
    simp only [valueExpr,Expr.cond_eval,Expr.equal_eval,Expr.eval,hw1,ite_false,
      ne_eq,not_true_eq_false,ite_true,nExpr_eval,kExpr_eval,Expr.lt_eval,Expr.word_eval,
      hk,one_mul,ht,old]
    simp only [step,dite_eq_left hk,State.value]
    by_cases hw0 : w=0
    · subst w; simp [show ¬0=3+s.input.length+s.k by omega]
    by_cases hwl : w<2+s.input.length
    · have hne : w≠3+s.input.length+s.k := by omega
      simp [hw0,hw1,hwl,hne]
    · have he : w=3+s.input.length+s.k ↔ w-(2+s.input.length)=s.k+1 := by omega
      simp only [hw0,hw1,hwl,ite_false,Function.update_apply]
      by_cases hwe : w=3+s.input.length+s.k
      · rw [ite_eq_left hwe,ite_eq_left (he.mp hwe)]; simp
      · rw [ite_eq_right hwe,ite_eq_right (mt he.mpr hwe)]; simp
  · simp [valueExpr,Expr.eval,hk,hw1,old,step,State.value]

lemma body_spec {m : ℕ} (δ : Fin m → Bool → Fin m) (s : State m) :
    UnaryTables.words (fun j => (valueExpr δ).eval s.bits (fun _ => j))
      (countExpr.eval s.bits (fun _ => 0)) = (step δ s).bits := by
  have hn : countExpr.eval s.bits (fun _ => 0) = 3+2*s.input.length := by
    simp [countExpr,Expr.eval]
  rw [hn]
  exact UnaryTables.words_congr (valueExpr_eval δ s)

noncomputable def body {m : ℕ} (δ : Fin m → Bool → Fin m) :
    TM2ComputableInPolyTime State.bits State.bits (step δ) :=
  UnaryTables.encodedComputer State.bits State.bits (step δ) countExpr (valueExpr δ) (body_spec δ)

lemma body_finiteAlphabet {m : ℕ} (δ : Fin m → Bool → Fin m) :
    MachineFiniteAlphabet.FiniteAlphabet (body δ).tm :=
  UnaryTables.encodedComputer_finiteAlphabet _ _ _ _ _ _

lemma iterate_input {m : ℕ} (δ : Fin m → Bool → Fin m) (q : Fin m) (s : List Bool) (i : ℕ) :
    ((step δ)^[i] (initial q s)).input = s := by
  induction i with
  | zero => rfl
  | succ i ih => simpa [Function.iterate_succ_apply',step] using ih

lemma iterate_k {m : ℕ} (δ : Fin m → Bool → Fin m) (q : Fin m) (s : List Bool) (i : ℕ) :
    ((step δ)^[i] (initial q s)).k = i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [Function.iterate_succ_apply',step,ih]

lemma history_prefix {m : ℕ} (δ : Fin m → Bool → Fin m) (q : Fin m) (s : List Bool)
    (i : ℕ) (hi : i ≤ s.length) (j : ℕ) (hj : j ≤ i) :
    ((step δ)^[i] (initial q s)).history j = (s.take j).foldl δ q := by
  induction i generalizing j with
  | zero =>
    have : j=0 := by omega
    subst j
    rfl
  | succ i ih =>
    have hk : i<s.length := hi
    rw [Function.iterate_succ_apply']
    simp only [step,iterate_k,iterate_input,dite_eq_left hk,Function.update_apply]
    by_cases he : j=i+1
    · rw [ite_eq_left he]
      subst j
      rw [ih hk.le i le_rfl,List.take_succ_eq_append_getElem hk,List.foldl_append]
      rfl
    · rw [ite_eq_right he]
      exact ih hk.le j (by omega)

def output {m : ℕ} (δ : Fin m → Bool → Fin m) (q : Fin m) (s : List Bool) : State m :=
  (step δ)^[s.length] (initial q s)

lemma output_history {m : ℕ} (δ : Fin m → Bool → Fin m) (q : Fin m) (s : List Bool)
    (j : ℕ) (hj : j ≤ s.length) :
    (output δ q s).history j = (s.take j).foldl δ q := history_prefix δ q s _ le_rfl j hj

lemma value_le {m : ℕ} (s : State m) (w : ℕ) : s.value w ≤ s.input.length+s.k+m+1 := by
  unfold State.value
  split
  · omega
  · split
    · omega
    · split
      · unfold Expr.bitValue; split <;> omega
      · have := (s.history (w-(2+s.input.length))).isLt; omega

lemma bits_length_le {m : ℕ} (s : State m) :
    s.bits.length ≤ (3+2*s.input.length)*(s.input.length+s.k+m+2) := by
  rw [State.bits,UnaryTables.words_length]
  unfold UnaryTables.offset
  calc
    _ ≤ ∑ _ ∈ Finset.range (3+2*s.input.length), (s.input.length+s.k+m+2) := by
      apply Finset.sum_le_sum
      intro w _hw
      have := value_le s w
      omega
    _ = _ := by simp

noncomputable def lengthPolynomial (m : ℕ) : Polynomial ℕ :=
  (3+2*Polynomial.X)*(2*Polynomial.X+Polynomial.C (m+2))

lemma lengthPolynomial_eval (m N : ℕ) :
    (lengthPolynomial m).eval N = (3+2*N)*(2*N+m+2) := by
  simp [lengthPolynomial,Nat.add_assoc]

def countedInput {m : ℕ} (q : Fin m) (s : List Bool) : List Bool :=
  BoundedIteration.counted List.length State.bits (initial q) s

lemma intermediate_bound {m : ℕ} (δ : Fin m → Bool → Fin m) (q : Fin m) (s : List Bool)
    (i : ℕ) (hi : i ≤ s.length) :
    ((step δ)^[i] (initial q s)).bits.length ≤ (lengthPolynomial m).eval (countedInput q s).length := by
  rw [lengthPolynomial_eval]
  apply (bits_length_le _).trans
  rw [iterate_input,iterate_k]
  have hn : s.length ≤ (countedInput q s).length :=
    BoundedIteration.count_le List.length State.bits (initial q) s
  gcongr; omega

noncomputable def countedCertificate {m : ℕ} (δ : Fin m → Bool → Fin m) (q : Fin m) :
    TM2ComputableInPolyTime (countedInput q) State.bits (output δ q) :=
  BoundedIteration.certificate State.bits (step δ) (initial q) List.length (body δ)
    (lengthPolynomial m) (intermediate_bound δ q)

lemma countedCertificate_finiteAlphabet {m : ℕ} (δ : Fin m → Bool → Fin m) (q : Fin m) :
    MachineFiniteAlphabet.FiniteAlphabet (countedCertificate δ q).tm :=
  BoundedIteration.certificate_finiteAlphabet _ _ _ _ _ _ _ (body_finiteAlphabet δ)

lemma words_cons (f : ℕ → ℕ) (n : ℕ) :
    UnaryTables.words f (n+1) = (List.replicate (f 0) true ++ [false]) ++
      UnaryTables.words (fun j => f (j+1)) n := by
  simp [UnaryTables.words,List.range_succ_eq_map,List.flatMap_map,Function.comp_def]

def initialCount : Expr := .add (.const 4) (.mul (.const 2) .length)
def initialValue {m : ℕ} (q : Fin m) : Expr :=
  Expr.cond (Expr.le (.arg 0) (.const 1)) .length
    (Expr.cond (Expr.equal (.arg 0) (.const 2)) (.const 0)
      (Expr.cond (Expr.lt (.arg 0) (.add (.const 3) .length))
        (.bit (.sub (.arg 0) (.const 3))) (.const q.val)))

lemma initialValue_zero {m : ℕ} (q : Fin m) (s : List Bool) :
    (initialValue q).eval s (fun _ => 0) = s.length := by simp [initialValue,Expr.eval]

lemma initialValue_succ {m : ℕ} (q : Fin m) (s : List Bool) (w : ℕ) :
    (initialValue q).eval s (fun _ => w+1) = (initial q s).value w := by
  simp only [initialValue,Expr.cond_eval,Expr.le_eval,Expr.equal_eval,Expr.lt_eval,Expr.eval]
  have h1 : w+1≤1 ↔ w=0 := by omega
  have h2 : w+1=2 ↔ w=1 := by omega
  have h3 : w+1<3+s.length ↔ w<2+s.length := by omega
  simp only [h1,h2,h3]
  by_cases hw0 : w=0
  · simp [hw0,initial,State.value]
  by_cases hw1 : w=1
  · simp [hw1,initial,State.value]
  have ht : w+1-3=w-2 := by omega
  simp [hw0,hw1,ht,initial,State.value,Expr.bitValue]
  rfl

lemma initial_spec {m : ℕ} (q : Fin m) (s : List Bool) :
    UnaryTables.words (fun j => (initialValue q).eval s (fun _ => j))
      (initialCount.eval s (fun _ => 0)) = countedInput q s := by
  have hc : initialCount.eval s (fun _ => 0) = (3+2*s.length)+1 := by
    simp [initialCount,Expr.eval]; omega
  rw [hc,words_cons,initialValue_zero]
  unfold countedInput BoundedIteration.counted State.bits
  congr 1
  exact UnaryTables.words_congr (fun j _hj => initialValue_succ q s j)

noncomputable def initialCertificate {m : ℕ} (q : Fin m) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (countedInput q) id :=
  UnaryTables.encodedComputer id (countedInput q) id initialCount (initialValue q) (initial_spec q)

lemma initialCertificate_finiteAlphabet {m : ℕ} (q : Fin m) :
    MachineFiniteAlphabet.FiniteAlphabet (initialCertificate q).tm :=
  UnaryTables.encodedComputer_finiteAlphabet _ _ _ _ _ _

noncomputable def certificate {m : ℕ} (δ : Fin m → Bool → Fin m) (q : Fin m) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) State.bits (output δ q) :=
  MachineSequential.composeBits (initialCertificate q) (countedCertificate δ q)

lemma finiteAlphabet {m : ℕ} (δ : Fin m → Bool → Fin m) (q : Fin m) :
    MachineFiniteAlphabet.FiniteAlphabet (certificate δ q).tm :=
  MachineFiniteAlphabet.composeBits _ _ (initialCertificate_finiteAlphabet q)
    (countedCertificate_finiteAlphabet δ q)
end LargeIndependentSets.FiniteScan

end OAI
