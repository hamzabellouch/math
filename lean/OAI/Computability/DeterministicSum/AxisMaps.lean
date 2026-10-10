import Mathlib
import OAI.Computability.DeterministicSum.IndexedLoops

namespace OAI

/-! Finite coordinate transforms, address bounds and tensor passes. -/

namespace DeterministicThreeSum.Structured.Indexed
open Command Finset
open scoped BigOperators

def Scalar.sum {m : ℕ} : List (Scalar m) → Scalar m
  | [] => .literal 0
  | a::as => .binary .add a (Scalar.sum as)

lemma Scalar.sum_value {m T : ℕ} (env : Fin m → ℕ) (mem : ℕ → Option ℕ)
    (as : List (Scalar m)) : (Scalar.sum as).value T env mem=
      (as.map (Scalar.value T env mem)).sum%T := by
  induction as with
  | nil => simp [Scalar.sum,Scalar.value]
  | cons a as ih =>
    simp only [Scalar.sum,Scalar.value,RingOp.raw,ih,List.map_cons,List.sum_cons]
    simp only [Nat.add_mod,Nat.mod_mod]

lemma Scalar.sum_valid {m w T : ℕ} (env : Fin m → ℕ) (mem : ℕ → Option ℕ)
    (as : List (Scalar m)) (h : ∀ a∈as, a.Valid w T env mem) :
    (Scalar.sum as).Valid w T env mem := by
  induction as with
  | nil => exact wordModulus_pos w
  | cons a as ih => exact ⟨h a (by simp),ih (fun b hb => h b (by simp [hb]))⟩

lemma Scalar.sum_reads {m : ℕ} (env : Fin m → ℕ) (as : List (Scalar m))
    (P : ℕ → Prop) (h : ∀ e∈as, ∀ a∈e.reads env, P a) :
    ∀ a∈(Scalar.sum as).reads env, P a := by
  induction as with
  | nil => simp [Scalar.sum,Scalar.reads]
  | cons e es ih =>
    intro a ha
    simp only [Scalar.sum,Scalar.reads,mem_union] at ha
    rcases ha with ha|ha
    · exact h e (by simp) a ha
    · exact ih (fun e' he' => h e' (by simp [he'])) a ha

lemma Scalar.sum_cast_value {m T : ℕ} (env : Fin m → ℕ) (mem : ℕ → Option ℕ)
    (as : List (Scalar m)) : ((Scalar.sum as).value T env mem:ZMod T)=
      (as.map (fun e => (e.value T env mem:ZMod T))).sum := by
  rw [Scalar.sum_value,ZMod.natCast_mod]
  simp [Function.comp_def]

namespace Axis
abbrev idx : Expr 8 := .parameter ⟨0,by omega⟩
abbrev src : Expr 8 := .parameter ⟨4,by omega⟩
abbrev coeff : Expr 8 := .parameter ⟨5,by omega⟩
abbrev stride : Expr 8 := .parameter ⟨6,by omega⟩

def outer (r : ℕ) : Expr 8 := .binary .quot (.binary .quot idx stride) (.literal r)
def digit (r : ℕ) : Expr 8 := .binary .rem (.binary .quot idx stride) (.literal r)
def suffix : Expr 8 := .binary .rem idx stride

def inputAddress (q r u : ℕ) : Expr 8 := .binary .add src
  (.binary .add (.binary .mul (.binary .add (.binary .mul (outer r) (.literal q)) (.literal u)) stride) suffix)
def coeffAddress (q r u : ℕ) : Expr 8 := .binary .add coeff
  (.binary .add (.binary .mul (digit r) (.literal q)) (.literal u))

def term (q r u : ℕ) : Scalar 8 := .binary .mul (.input (coeffAddress q r u)) (.input (inputAddress q r u))
def row (q r : ℕ) : Scalar 8 := Scalar.sum (List.ofFn (fun u : Fin q => term q r u.val))
def pass (q r : ℕ) : Command := kernel ⟨0,by omega⟩ ⟨1,by omega⟩ ⟨3,by omega⟩ (row q r)

def sourceIndex (q r B j u : ℕ) : ℕ := ((j/B/r)*q+u)*B+j%B
def coefficientIndex (q r B j u : ℕ) : ℕ := (j/B%r)*q+u

def environment (T N P S C B A j : ℕ) : Fin 8 → ℕ :=
  ![j,N,T,P,S,C,B,A]

lemma inputAddress_value (T N P S C B A j q r u : ℕ) :
    (inputAddress q r u).value (environment T N P S C B A j)=S+sourceIndex q r B j u := by
  simp [inputAddress,outer,suffix,Expr.value,Arithmetic.value,environment,sourceIndex]
lemma coeffAddress_value (T N P S C B A j q r u : ℕ) :
    (coeffAddress q r u).value (environment T N P S C B A j)=C+coefficientIndex q r B j u := by
  simp [coeffAddress,digit,Expr.value,Arithmetic.value,environment,coefficientIndex]

lemma quotient_bounds {A B r j : ℕ} (hB : 0<B) (hr : 0<r) (hj : j<A*r*B) :
    j/B/r<A ∧ j/B%r<r ∧ j%B<B := by
  refine ⟨?_,Nat.mod_lt _ hr,Nat.mod_lt _ hB⟩
  apply (Nat.div_lt_iff_lt_mul hr).2
  apply (Nat.div_lt_iff_lt_mul hB).2
  exact hj

lemma sourceIndex_bound {A B q r j u : ℕ} (hB : 0<B) (hr : 0<r)
    (hj : j<A*r*B) (hu : u<q) : sourceIndex q r B j u<A*q*B := by
  obtain ⟨hp,hd,hs⟩:=quotient_bounds hB hr hj
  have h1 : (j/B/r)*q+u<A*q := by nlinarith [Nat.mul_le_mul_right q (show j/B/r+1≤A by omega)]
  have h2:=Nat.mul_le_mul_right B (show (j/B/r)*q+u+1≤A*q by omega)
  dsimp [sourceIndex]
  nlinarith

lemma coefficientIndex_bound {B q r j u : ℕ} (hr : 0<r) (hu : u<q) :
    coefficientIndex q r B j u<r*q := by
  have hd:=Nat.mod_lt (j/B) hr
  have h1:=Nat.mul_le_mul_right q (show j/B%r+1≤r by omega)
  dsimp [coefficientIndex]
  nlinarith

end Axis
end DeterministicThreeSum.Structured.Indexed
namespace DeterministicThreeSum.Structured.Indexed.Axis
open Command Finset
open scoped BigOperators

lemma addresses_valid {w T P S C A B q r j u : ℕ}
    (hq : 0<q) (hr : 0<r) (hB : 0<B) (hj : j<A*r*B) (hu : u<q)
    (hN : A*r*B<wordModulus w) (hS : S+A*q*B<wordModulus w)
    (hC : C+r*q<wordModulus w) :
    (inputAddress q r u).Valid w (environment T (A*r*B) P S C B A j) ∧
    (coeffAddress q r u).Valid w (environment T (A*r*B) P S C B A j) := by
  have hA : 0<A := by
    by_contra h
    have hzero : A=0 := by omega
    simp [hzero] at hj
  have hmB : B≤A*r*B := by
    have hp : 1≤A*r := Nat.mul_pos hA hr
    simpa using Nat.mul_le_mul_right B hp
  have hmq : q≤r*q := by simpa using Nat.mul_le_mul_right q hr
  have hmr : r≤r*q := by simpa using Nat.mul_le_mul_left r hq
  have hi:=sourceIndex_bound hB hr hj hu
  have hc:=coefficientIndex_bound (B:=B) (j:=j) hr hu
  have hf : (j/B/r)*q+u≤((j/B/r)*q+u)*B := by
    simpa using Nat.mul_le_mul_left ((j/B/r)*q+u) hB
  dsimp [sourceIndex] at hi
  dsimp [coefficientIndex] at hc
  constructor
  · simp only [inputAddress,outer,suffix,Expr.Valid,Expr.value,Arithmetic.Valid,Arithmetic.value]
    norm_num [environment]
    omega
  · simp only [coeffAddress,digit,Expr.Valid,Expr.value,Arithmetic.Valid,Arithmetic.value]
    norm_num [environment]
    omega

lemma row_valid {w T P S C A B q r j : ℕ} (mem : ℕ → Option ℕ) (x c : ℕ → ℕ)
    (hq : 0<q) (hr : 0<r) (hB : 0<B) (hj : j<A*r*B)
    (hN : A*r*B<wordModulus w) (hS : S+A*q*B<wordModulus w)
    (hC : C+r*q<wordModulus w)
    (hx : ∀ i, i<A*q*B → mem (S+i)=some (x i) ∧ x i<T)
    (hc : ∀ i, i<r*q → mem (C+i)=some (c i) ∧ c i<T) :
    (row q r).Valid w T (environment T (A*r*B) P S C B A j) mem := by
  apply Scalar.sum_valid
  intro e he
  obtain ⟨u,rfl⟩:=List.mem_ofFn.mp he
  obtain ⟨hsafe,csafe⟩:=addresses_valid (T:=T) (P:=P) hq hr hB hj u.isLt hN hS hC
  refine ⟨⟨csafe,c (coefficientIndex q r B j u.val),?_,?_⟩,
    ⟨hsafe,x (sourceIndex q r B j u.val),?_,?_⟩⟩
  · rw [coeffAddress_value]
    exact (hc _ (coefficientIndex_bound hr u.isLt)).1
  · exact (hc _ (coefficientIndex_bound hr u.isLt)).2
  · rw [inputAddress_value]
    exact (hx _ (sourceIndex_bound hB hr hj u.isLt)).1
  · exact (hx _ (sourceIndex_bound hB hr hj u.isLt)).2

lemma row_value {T P S C A B q r j : ℕ} (mem : ℕ → Option ℕ) (x c : ℕ → ℕ)
    (hr : 0<r) (hB : 0<B) (hj : j<A*r*B)
    (hx : ∀ i, i<A*q*B → mem (S+i)=some (x i))
    (hc : ∀ i, i<r*q → mem (C+i)=some (c i)) :
    ((row q r).value T (environment T (A*r*B) P S C B A j) mem:ZMod T)=
      ∑ u : Fin q, (c (coefficientIndex q r B j u.val):ZMod T)*
        (x (sourceIndex q r B j u.val):ZMod T) := by
  rw [row,Scalar.sum_cast_value,List.map_ofFn,List.sum_ofFn]
  apply sum_congr rfl
  intro u _
  simp only [Function.comp_apply,term,Scalar.value,RingOp.raw,coeffAddress_value,inputAddress_value,
    hc _ (coefficientIndex_bound hr u.isLt),hx _ (sourceIndex_bound hB hr hj u.isLt),Option.getD_some]
  simp

lemma row_reads_outside {T P S C A B q r j : ℕ}
    (hr : 0<r) (hB : 0<B) (hj : j<A*r*B)
    (hS : S+A*q*B≤P ∨ P+A*r*B≤S) (hC : C+r*q≤P ∨ P+A*r*B≤C) :
    ∀ a∈(row q r).reads (environment T (A*r*B) P S C B A j), a<P ∨ P+A*r*B≤a := by
  apply Scalar.sum_reads
  intro e he a ha
  obtain ⟨u,rfl⟩:=List.mem_ofFn.mp he
  simp only [term,Scalar.reads,mem_union,mem_singleton,coeffAddress_value,inputAddress_value] at ha
  have hs:=sourceIndex_bound hB hr hj u.isLt
  have hc:=coefficientIndex_bound (B:=B) (j:=j) hr u.isLt
  rcases ha with rfl|rfl <;> omega

end DeterministicThreeSum.Structured.Indexed.Axis

namespace DeterministicThreeSum.Structured.Indexed.Axis
open Command Finset
open scoped BigOperators

lemma environment_update (T N P S C B A i : ℕ) :
    Function.update (environment T N P S C B A 0) ⟨0,by omega⟩ i=
      environment T N P S C B A i := by
  funext a
  fin_cases a <;> simp [environment]

theorem pass_correct {w T P S C A B q r : ℕ} (s : Data) (x c : ℕ → ℕ)
    (hq : 0<q) (hr : 0<r) (hB : 0<B) (hT : 0<T)
    (hadd : 2*T<wordModulus w) (hmul : T*T<wordModulus w)
    (hN : A*r*B+1<wordModulus w) (hP : P+A*r*B<wordModulus w)
    (hS : S+A*q*B<wordModulus w) (hC : C+r*q<wordModulus w)
    (hdisS : S+A*q*B≤P ∨ P+A*r*B≤S) (hdisC : C+r*q≤P ∨ P+A*r*B≤C)
    (hregs : ∀ a : Fin 8, s.registers a.val=environment T (A*r*B) P S C B A 0 a)
    (hx : ∀ i, i<A*q*B → s.memory (S+i)=some (x i) ∧ x i<T)
    (hc : ∀ i, i<r*q → s.memory (C+i)=some (c i) ∧ c i<T) :
    ∃ cost t, Eval w (pass q r) s cost t ∧ cost≤((row q r).cost+5)*(A*r*B)+1 ∧
      (∀ a, a<8 → a≠0 → t.registers a=s.registers a) ∧
      t.registers 0=A*r*B ∧
      (∀ j, j<A*r*B → ∃ v, t.memory (P+j)=some v ∧ v<T ∧
        (v:ZMod T)=∑ u : Fin q, (c (coefficientIndex q r B j u.val):ZMod T)*
          (x (sourceIndex q r B j u.val):ZMod T)) ∧
      (∀ a, a<P ∨ P+A*r*B≤a → t.memory a=s.memory a) := by
  have henv : (fun a : Fin 8 => s.registers a.val)=environment T (A*r*B) P S C B A 0 := funext hregs
  have hindex : s.registers 0=0 := by simpa [environment] using hregs ⟨0,by omega⟩
  have hbound : s.registers 1=A*r*B := by simpa [environment] using hregs ⟨1,by omega⟩
  have hbase : s.registers 3=P := by simpa [environment] using hregs ⟨3,by omega⟩
  have hmod : s.registers 2=T := by simpa [environment] using hregs ⟨2,by omega⟩
  have hv : ∀ i, i<A*r*B → (row q r).Valid w T
      (Function.update (fun a : Fin 8 => s.registers a.val) ⟨0,by omega⟩ i) s.memory := by
    intro i hi
    rw [henv,environment_update]
    exact row_valid s.memory x c hq hr hB hi (by omega) hS hC hx hc
  have hd : ∀ i, i<A*r*B → ∀ a∈(row q r).reads
      (Function.update (fun a : Fin 8 => s.registers a.val) ⟨0,by omega⟩ i), a<P ∨ P+A*r*B≤a := by
    intro i hi
    rw [henv,environment_update]
    exact row_reads_outside hr hB hi hdisS hdisC
  obtain ⟨cost,t,he,hcost,hframe,ht,hm⟩:=kernel_correct
    (index:=⟨0,by omega⟩) (bound:=⟨1,by omega⟩) (base:=⟨3,by omega⟩) (row q r) s
    (by omega) hT hadd hmul hN hP (by intro h; have hv := congrArg Fin.val h; norm_num at hv) (by intro h; have hv := congrArg Fin.val h; norm_num at hv) (by norm_num) hbound hbase hmod hindex hv hd
  refine ⟨cost,t,he,hcost,hframe,ht,?_,?_⟩
  · intro j hj
    let v := (row q r).value T (environment T (A*r*B) P S C B A j) s.memory
    refine ⟨v,?_,?_,?_⟩
    · rw [hm,henv]
      simp only [written,ite_eq_left (show P≤P+j ∧ P+j<P+A*r*B by omega),Nat.add_sub_cancel_left,environment_update]
      rfl
    · exact (row q r).value_lt _ _ hT (row_valid s.memory x c hq hr hB hj (by omega) hS hC hx hc)
    · exact row_value s.memory x c hr hB hj (fun i hi => (hx i hi).1) (fun i hi => (hc i hi).1)
  · intro a ha
    rw [hm]
    exact written_outside ha

end DeterministicThreeSum.Structured.Indexed.Axis
namespace DeterministicThreeSum.Structured.Indexed.Axis
open Command Finset
open scoped BigOperators

def mapValue (T q r B : ℕ) (x c : ℕ → ℕ) (j : ℕ) : ℕ :=
  (∑ u : Fin q, c (coefficientIndex q r B j u.val)*x (sourceIndex q r B j u.val))%T

lemma mapValue_lt {T : ℕ} (hT : 0<T) (q r B : ℕ) (x c : ℕ → ℕ) (j : ℕ) :
    mapValue T q r B x c j<T := Nat.mod_lt _ hT

lemma mapValue_cast (T q r B : ℕ) (x c : ℕ → ℕ) (j : ℕ) :
    (mapValue T q r B x c j:ZMod T)=∑ u : Fin q,
      (c (coefficientIndex q r B j u.val):ZMod T)*(x (sourceIndex q r B j u.val):ZMod T) := by
  simp [mapValue]

lemma pass_exact {w T P S C A B q r : ℕ} (s : Data) (x c : ℕ → ℕ)
    (hq : 0<q) (hr : 0<r) (hB : 0<B) (hT : 0<T)
    (hadd : 2*T<wordModulus w) (hmul : T*T<wordModulus w)
    (hN : A*r*B+1<wordModulus w) (hP : P+A*r*B<wordModulus w)
    (hS : S+A*q*B<wordModulus w) (hC : C+r*q<wordModulus w)
    (hdisS : S+A*q*B≤P ∨ P+A*r*B≤S) (hdisC : C+r*q≤P ∨ P+A*r*B≤C)
    (hregs : ∀ a : Fin 8, s.registers a.val=environment T (A*r*B) P S C B A 0 a)
    (hx : ∀ i, i<A*q*B → s.memory (S+i)=some (x i) ∧ x i<T)
    (hc : ∀ i, i<r*q → s.memory (C+i)=some (c i) ∧ c i<T) :
    ∃ cost t, Eval w (pass q r) s cost t ∧ cost≤((row q r).cost+5)*(A*r*B)+1 ∧
      (∀ a, a<8 → a≠0 → t.registers a=s.registers a) ∧ t.registers 0=A*r*B ∧
      (∀ j, j<A*r*B → t.memory (P+j)=some (mapValue T q r B x c j)) ∧
      (∀ a, a<P ∨ P+A*r*B≤a → t.memory a=s.memory a) := by
  obtain ⟨cost,t,he,hcost,hframe,ht,hm,houtside⟩:=pass_correct s x c hq hr hB hT hadd hmul hN hP hS hC hdisS hdisC hregs hx hc
  refine ⟨cost,t,he,hcost,hframe,ht,?_,houtside⟩
  intro j hj
  obtain ⟨v,hv,hvT,hvc⟩:=hm j hj
  have heq : (v:ZMod T)=(mapValue T q r B x c j:ZMod T) := hvc.trans (mapValue_cast ..).symm
  have : NeZero T := ⟨by omega⟩
  apply_fun ZMod.val at heq
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hvT,Nat.mod_eq_of_lt (mapValue_lt hT q r B x c j)] at heq
  simpa [heq] using hv

def tensorUpdate (q r : ℕ) : Command := straight [
  .assign 8 (.register 3), .assign 3 (.register 4), .assign 4 (.register 8),
  .binary 7 .mul (.register 7) (.literal r),
  .binary 6 .quot (.register 6) (.literal q),
  .binary 1 .mul (.register 7) (.literal r),
  .binary 1 .mul (.register 1) (.register 6), .assign 0 (.literal 0)]

def tensorUpdateState (s : Data) (A B P S q r : ℕ) : Data :=
  put (put (put (put (put (put (put (put s 8 P) 3 S) 4 P) 7 (A*r)) 6 (B/q))
    1 (A*r*r)) 1 (A*r*r*(B/q))) 0 0

lemma tensorUpdate_correct {w A B P S q r : ℕ} (s : Data)
    (hq : 0<q) (hqW : q<wordModulus w) (hrW : r<wordModulus w)
    (hP : P<wordModulus w) (hS : S<wordModulus w)
    (hA : A*r*r<wordModulus w) (hr : 0<r) (hB : B<wordModulus w)
    (hN : A*r*r*(B/q)<wordModulus w)
    (h3 : s.registers 3=P) (h4 : s.registers 4=S)
    (h6 : s.registers 6=B) (h7 : s.registers 7=A) :
    Eval w (tensorUpdate q r) s 8 (tensorUpdateState s A B P S q r) := by
  have hAr : A*r≤A*r*r := by simpa using Nat.mul_le_mul_left (A*r) hr
  have hAA : A≤A*r := by simpa using Nat.mul_le_mul_left A hr
  apply straight_correct
  simp [tensorUpdateState,execStraight,Atom.eval,operand_register,operand_literal,
    evalBinOp,put,h3,h4,h6,h7,Nat.mod_eq_of_lt hP,Nat.mod_eq_of_lt hS,
    Nat.mod_eq_of_lt hB,Nat.mod_eq_of_lt hqW,Nat.mod_eq_of_lt hrW,
    Nat.mod_eq_of_lt hN,Nat.mod_eq_of_lt (show A*r<wordModulus w by omega),
    hq.ne',Function.update_idem]

def tensorBody (q r : ℕ) : Command := .seq (pass q r) (tensorUpdate q r)
def tensorCommand (q r : ℕ) : Command := .loop .lt (.literal 0) (.register 6) (tensorBody q r)

def tensorValue (T q r : ℕ) (c : ℕ → ℕ) : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
  | 0,x => x
  | d+1,x => tensorValue T q r c d (mapValue T q r (q^d) x c)

def banks (d P S : ℕ) : ℕ × ℕ := if Even d then (P,S) else (S,P)

lemma banks_zero (P S : ℕ) : banks 0 P S=(P,S) := by simp [banks]
lemma banks_succ (d P S : ℕ) : banks (d+1) P S=banks d S P := by
  simp only [banks,Nat.even_add_one]
  by_cases h : Even d <;> simp [h]

end DeterministicThreeSum.Structured.Indexed.Axis
namespace DeterministicThreeSum.Structured.Indexed.Axis
open Command Finset
open scoped BigOperators

def tensorStride (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | d+1 => q^d

lemma tensorStride_div {q : ℕ} (hq : 1<q) (d : ℕ) :
    q^d/q=tensorStride q d := by
  cases d with
  | zero => simp [tensorStride,Nat.div_eq_of_lt hq]
  | succ d => simp [tensorStride,pow_succ,show q≠0 by omega]

lemma stage_lengths {q r A L d : ℕ} (hL : A*(max q r)^(d+1)≤L) :
    A*q*q^d≤L ∧ A*r*q^d≤L ∧ (A*r)*(max q r)^d≤L := by
  have hq : q ≤ max q r := le_max_left ..
  have hr : r ≤ max q r := le_max_right ..
  have hpow : q^d≤(max q r)^d := Nat.pow_le_pow_left hq d
  have h1 : A*q*q^d≤A*(max q r)^(d+1) := by
    rw [pow_succ]; nlinarith [Nat.mul_le_mul (Nat.mul_le_mul_left A hq) hpow]
  have h2 : A*r*q^d≤A*(max q r)^(d+1) := by
    rw [pow_succ]; nlinarith [Nat.mul_le_mul (Nat.mul_le_mul_left A hr) hpow]
  have h3 : A*r*(max q r)^d≤A*(max q r)^(d+1) := by
    rw [pow_succ]
    nlinarith only [Nat.mul_le_mul_right ((max q r)^d) (Nat.mul_le_mul_left A hr)]
  exact ⟨h1.trans hL,h2.trans hL,h3.trans hL⟩

theorem tensorCommand_correct {w T q r L d A P S C : ℕ} (s : Data) (x c : ℕ → ℕ)
    (hq : 1<q) (hr : 0<r) (hA : 0<A) (hT : 0<T)
    (hadd : 2*T<wordModulus w) (hmul : T*T<wordModulus w)
    (hL : A*(max q r)^d≤L) (hLw : L*r+L+3<wordModulus w)
    (hP : P+L+1<wordModulus w) (hS : S+L+1<wordModulus w)
    (hC : C+r*q<wordModulus w)
    (hPS : S+L≤P ∨ P+L≤S)
    (hCP : C+r*q≤P ∨ P+L≤C) (hCS : C+r*q≤S ∨ S+L≤C)
    (hregs : ∀ a : Fin 8, s.registers a.val=
      environment T (A*r*tensorStride q d) P S C (tensorStride q d) A 0 a)
    (hx : ∀ i, i<A*q^d → s.memory (S+i)=some (x i) ∧ x i<T)
    (hc : ∀ i, i<r*q → s.memory (C+i)=some (c i) ∧ c i<T) :
    ∃ cost t, Eval w (tensorCommand q r) s cost t ∧
      cost≤(((row q r).cost+5)*L+11)*d+1 ∧
      (∀ a : Fin 8, t.registers a.val=
        environment T 0 (banks d P S).1 (banks d P S).2 C 0 (A*r^d) 0 a) ∧
      (∀ j, j<A*r^d → t.memory ((banks d P S).2+j)=some (tensorValue T q r c d x j) ∧
        tensorValue T q r c d x j<T) ∧
      (∀ a, (a<P ∨ P+L≤a) → (a<S ∨ S+L≤a) → t.memory a=s.memory a) := by
  induction d generalizing A P S s x with
  | zero =>
    have h6 : s.registers 6=0 := by simpa [environment,tensorStride] using hregs ⟨6,by omega⟩
    have htest : test w s .lt (.literal 0) (.register 6)=false := by
      simp [test,operand_literal,operand_register,evalTest,h6]
    refine ⟨1,s,Eval.loopFalse htest,by simp,?_,?_,by simp⟩
    · simpa only [tensorStride,Nat.mul_zero,banks_zero,pow_zero,Nat.mul_one] using hregs
    · simpa only [tensorValue,banks_zero,pow_zero,Nat.mul_one] using hx
  | succ d ih =>
    obtain ⟨hlenX,hlenY,hlenNext⟩:=stage_lengths hL
    have hp : 0<q^d := pow_pos (by omega) _
    have hAr : 1≤A*r := Nat.mul_pos hA hr
    have hB : q^d≤L := (by simpa using Nat.mul_le_mul_right (q^d) hAr : q^d≤A*r*q^d) |>.trans hlenY
    have hArL : A*r≤L := (by simpa using Nat.mul_le_mul_left (A*r) hp : A*r≤A*r*q^d) |>.trans hlenY
    have hArr : A*r*r<wordModulus w := lt_of_le_of_lt (Nat.mul_le_mul_right r hArL) (by omega)
    have hqW : q<wordModulus w := by
      have hl : q≤r*q := by simpa [Nat.mul_comm] using Nat.mul_le_mul_left q hr
      omega
    have hrW : r<wordModulus w := by
      have hl : r≤r*q := by simpa using Nat.mul_le_mul_left r (show 1≤q by omega)
      omega
    have h6 : s.registers 6=q^d := by simpa [environment,tensorStride] using hregs ⟨6,by omega⟩
    have htest : test w s .lt (.literal 0) (.register 6)=true := by
      simp [test,operand_literal,operand_register,evalTest,h6,Nat.mod_eq_of_lt (show q^d<wordModulus w by omega),hp]
    have hregs' : ∀ a : Fin 8, s.registers a.val=environment T (A*r*q^d) P S C (q^d) A 0 a := hregs
    obtain ⟨cost,u,ep,hcost,hframe,hidx,hmem,houtside⟩:=pass_exact s x c (by omega) hr hp hT hadd hmul
      (by omega : A*r*q^d+1<wordModulus w) (by omega) (by omega) hC
      (by omega) (by omega) hregs' (by simpa only [pow_succ',Nat.mul_assoc] using hx) hc
    have hparam : ∀ a : Fin 8, a.val≠0 → u.registers a.val=environment T (A*r*q^d) P S C (q^d) A 0 a :=
      fun a ha => (hframe a.val a.isLt ha).trans (hregs' a)
    have h3u : u.registers 3=P := by simpa [environment] using hparam ⟨3,by omega⟩ (by norm_num)
    have h4u : u.registers 4=S := by simpa [environment] using hparam ⟨4,by omega⟩ (by norm_num)
    have h6u : u.registers 6=q^d := by simpa [environment] using hparam ⟨6,by omega⟩ (by norm_num)
    have h7u : u.registers 7=A := by simpa [environment] using hparam ⟨7,by omega⟩ (by norm_num)
    have hnext : A*r*r*(q^d/q)<wordModulus w := by
      have hl : q^d/q≤q^d := Nat.div_le_self ..
      have hh : A*r*r*(q^d/q)≤L*r := by
        calc
          _ ≤ A*r*r*q^d := Nat.mul_le_mul_left _ hl
          _ = (A*r*q^d)*r := by ring
          _ ≤ L*r := Nat.mul_le_mul_right r hlenY
      omega
    have eu:=tensorUpdate_correct u (by omega) hqW hrW (by omega) (by omega) hArr hr (by omega) hnext h3u h4u h6u h7u
    let v:=tensorUpdateState u A (q^d) P S q r
    have hregsv : ∀ a : Fin 8, v.registers a.val=
        environment T ((A*r)*r*tensorStride q d) S P C (tensorStride q d) (A*r) 0 a := by
      intro a
      have h2u : u.registers 2=T := by simpa [environment] using hparam ⟨2,by omega⟩ (by norm_num)
      have h5u : u.registers 5=C := by simpa [environment] using hparam ⟨5,by omega⟩ (by norm_num)
      fin_cases a <;> simp [v,tensorUpdateState,put,environment,tensorStride_div hq,h2u,h5u]
    have hc' : ∀ i, i<r*q → v.memory (C+i)=some (c i) ∧ c i<T := by
      intro i hi
      have ho : C+i<P ∨ P+A*r*q^d≤C+i := by omega
      simp only [v,tensorUpdateState,put]
      rw [houtside _ ho]
      exact hc i hi
    have hx' : ∀ i, i<(A*r)*q^d → v.memory (P+i)=some (mapValue T q r (q^d) x c i) ∧
        mapValue T q r (q^d) x c i<T := by
      intro i hi
      exact ⟨hmem i hi,mapValue_lt hT q r (q^d) x c i⟩
    obtain ⟨rest,t,er,hrcost,hregsFinal,hmFinal,houtFinal⟩:=ih v (mapValue T q r (q^d) x c) (by positivity)
      hlenNext hS hP (by omega) hCS hCP hregsv hx' hc'
    refine ⟨1+(cost+8)+1+rest,t,Eval.loopTrue htest (Eval.seq ep eu) er,?_,?_,?_,?_⟩
    · have hcL : cost≤((row q r).cost+5)*L+1 := by
        exact hcost.trans (by gcongr)
      nlinarith only [hcL,hrcost]
    · simpa only [banks_succ,pow_succ',Nat.mul_assoc] using hregsFinal
    · simpa only [banks_succ,tensorValue,pow_succ',Nat.mul_assoc] using hmFinal
    · intro a ha hb
      rw [houtFinal a hb ha]
      exact houtside a (by omega)

end DeterministicThreeSum.Structured.Indexed.Axis
namespace DeterministicThreeSum.Structured.Indexed.Axis
open Command Finset
open scoped BigOperators

def boxIndex (r B a v j : ℕ) : ℕ := (a*r+v)*B+j

lemma boxIndex_lt {A r B a v j : ℕ} (ha : a<A) (hv : v<r) (hj : j<B) :
    boxIndex r B a v j<A*r*B := by
  have h1 : a*r+v<A*r := by nlinarith only [ha,hv,Nat.mul_le_mul_right r (show a+1≤A by omega)]
  have h2 := Nat.mul_le_mul_right B (show a*r+v+1≤A*r by omega)
  dsimp [boxIndex]
  nlinarith only [h2,hj]

lemma boxIndex_parts {r B a v j : ℕ} (hr : 0<r) (hB : 0<B) (hv : v<r) (hj : j<B) :
    boxIndex r B a v j/B/r=a ∧ boxIndex r B a v j/B%r=v ∧ boxIndex r B a v j%B=j := by
  have hdiv : boxIndex r B a v j/B=a*r+v := by
    rw [boxIndex,Nat.mul_comm _ B,Nat.mul_add_div hB,Nat.div_eq_of_lt hj,Nat.add_zero]
  rw [hdiv]
  constructor
  · rw [Nat.mul_comm a r,Nat.mul_add_div hr,Nat.div_eq_of_lt hv,Nat.add_zero]
  constructor
  · simp [Nat.add_mod,Nat.mod_eq_of_lt hv]
  · simp [boxIndex,Nat.add_mod,Nat.mod_eq_of_lt hj]

lemma mapValue_box {T q r B a v j : ℕ} (x c : ℕ → ℕ)
    (hr : 0<r) (hB : 0<B) (hv : v<r) (hj : j<B) :
    (mapValue T q r B x c (boxIndex r B a v j):ZMod T)=
      ∑ u : Fin q, (c (v*q+u.val):ZMod T)*(x (boxIndex q B a u.val j):ZMod T) := by
  obtain ⟨h1,h2,h3⟩:=boxIndex_parts (a:=a) hr hB hv hj
  rw [mapValue_cast]
  simp only [coefficientIndex,sourceIndex]
  rw [h1,h2,h3]
  rfl

theorem pass_box_correct {w T P S C A B q r : ℕ} (s : Data) (x c : ℕ → ℕ)
    (f : Fin r → Fin q → ZMod T) (X : Fin A → Fin q → Fin B → ZMod T)
    (hq : 0<q) (hr : 0<r) (hB : 0<B) (hT : 0<T)
    (hadd : 2*T<wordModulus w) (hmul : T*T<wordModulus w)
    (hN : A*r*B+1<wordModulus w) (hP : P+A*r*B<wordModulus w)
    (hS : S+A*q*B<wordModulus w) (hC : C+r*q<wordModulus w)
    (hdisS : S+A*q*B≤P ∨ P+A*r*B≤S) (hdisC : C+r*q≤P ∨ P+A*r*B≤C)
    (hregs : ∀ a : Fin 8, s.registers a.val=environment T (A*r*B) P S C B A 0 a)
    (hx : ∀ i, i<A*q*B → s.memory (S+i)=some (x i) ∧ x i<T)
    (hc : ∀ i, i<r*q → s.memory (C+i)=some (c i) ∧ c i<T)
    (hf : ∀ v u, (c (v.val*q+u.val):ZMod T)=f v u)
    (hX : ∀ a u j, (x (boxIndex q B a.val u.val j.val):ZMod T)=X a u j) :
    ∃ cost t, Eval w (pass q r) s cost t ∧ cost≤((row q r).cost+5)*(A*r*B)+1 ∧
      (∀ a, a<8 → a≠0 → t.registers a=s.registers a) ∧ t.registers 0=A*r*B ∧
      (∀ (a : Fin A) (v : Fin r) (j : Fin B), ∃ y,
        t.memory (P+boxIndex r B a.val v.val j.val)=some y ∧ y<T ∧
          (y:ZMod T)=∑ u : Fin q, f v u*X a u j) ∧
      (∀ a, a<P ∨ P+A*r*B≤a → t.memory a=s.memory a) := by
  obtain ⟨cost,t,he,hcost,hframe,ht,hm,houtside⟩:=pass_exact s x c hq hr hB hT hadd hmul hN hP hS hC hdisS hdisC hregs hx hc
  refine ⟨cost,t,he,hcost,hframe,ht,?_,houtside⟩
  intro a v j
  refine ⟨_,hm _ (boxIndex_lt a.isLt v.isLt j.isLt),mapValue_lt hT ..,?_⟩
  rw [mapValue_box x c hr hB v.isLt j.isLt]
  simp only [hf,hX]

end DeterministicThreeSum.Structured.Indexed.Axis

end OAI
