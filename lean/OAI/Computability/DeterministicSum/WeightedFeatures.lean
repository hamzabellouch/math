import Mathlib
import OAI.Computability.DeterministicSum.CacheRows

namespace OAI

/-! Monomial formation, weighted feature sums and exact source identities. -/

namespace DeterministicThreeSum.Structured.Indexed.Monomial
open Command

def value (T q : ℕ) (c : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0,_,_ => 1%T
  | d+1,x,e => (c ((x%q)*q+e%q)*value T q c d (x/q) (e/q))%T

lemma value_lt {T q : ℕ} (hT : 0 < T) (c : ℕ → ℕ) (d x e : ℕ) : value T q c d x e < T := by
  cases d <;> exact Nat.mod_lt _ hT

def step (q : ℕ) : Command := straight [
  .binary 11 .rem (.register 8) (.literal q),
  .binary 12 .rem (.register 10) (.literal q),
  .binary 13 .mul (.register 12) (.literal q),
  .binary 13 .add (.register 13) (.register 11),
  .binary 14 .add (.register 17) (.register 13),
  .load 15 (.register 14),
  .binary 9 .mul (.register 9) (.register 15),
  .binary 9 .rem (.register 9) (.register 16),
  .binary 8 .quot (.register 8) (.literal q),
  .binary 10 .quot (.register 10) (.literal q),
  .binary 7 .sub (.register 7) (.literal 1)]
def loop (q : ℕ) : Command := .loop .lt (.literal 0) (.register 7) (step q)

def stepState (s : Data) (T C q d x e a : ℕ) (c : ℕ → ℕ) : Data :=
  let idx:=(x%q)*q+e%q
  put (put (put (put (put (put (put (put (put s 11 (e%q)) 12 (x%q))
    13 idx) 14 (C+idx)) 15 (c idx)) 9 ((a*c idx)%T)) 8 (e/q)) 10 (x/q)) 7 (d-1)

lemma index_lt {q : ℕ} (hq : 0 < q) (x e : ℕ) : (x%q)*q+e%q < q*q := by
  have hx:=Nat.mod_lt x hq
  have he:=Nat.mod_lt e hq
  nlinarith only [Nat.mul_le_mul_right q hx,he]

lemma step_correct {w T C q d x e a : ℕ} (s : Data) (c : ℕ → ℕ)
    (hW : 2 < wordModulus w) (hq : 0 < q) (hqw : q < wordModulus w)
    (hT : 0 < T) (hTT : T*T < wordModulus w)
    (hC : C+q*q < wordModulus w) (hdpos : 0 < d) (hd : d < wordModulus w)
    (hx : x < wordModulus w) (he : e < wordModulus w) (ha : a < T)
    (hc : ∀ i, i < q*q → s.memory (C+i)=some (c i) ∧ c i < T)
    (h7 : s.registers 7=d) (h8 : s.registers 8=e) (h9 : s.registers 9=a)
    (h10 : s.registers 10=x) (h16 : s.registers 16=T) (h17 : s.registers 17=C) :
    Eval w (step q) s 11 (stepState s T C q d x e a c) := by
  have hi:=index_lt hq x e
  have hcit:=(hc _ hi).2
  have hTw : T < wordModulus w := by nlinarith only [hT,hTT]
  have hprod : a*c ((x%q)*q+e%q) < wordModulus w := by
    have hle:=Nat.mul_le_mul ha.le hcit.le
    omega
  have hxq : x%q < wordModulus w := (Nat.mod_lt x hq).trans hqw
  have heq : e%q < wordModulus w := (Nat.mod_lt e hq).trans hqw
  have hidx : (x%q)*q+e%q < wordModulus w := by omega
  have haddr : C+((x%q)*q+e%q) < wordModulus w := by omega
  have hminus : (d+wordModulus w-1)%wordModulus w=d-1 := by
    rw [show d+wordModulus w-1=d-1+wordModulus w by omega,Nat.add_mod]
    simp [Nat.mod_eq_of_lt (show d-1 < wordModulus w by omega)]
  apply straight_correct
  simp [stepState,execStraight,Atom.eval,operand_literal,operand_register,
    evalBinOp,put,hminus,h7,h8,h9,h10,h16,h17,hq.ne',hT.ne',Nat.mod_eq_of_lt hqw,
    Nat.mod_eq_of_lt hd,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt he,
    Nat.mod_eq_of_lt (show (x%q)*q < wordModulus w by omega),Nat.mod_eq_of_lt hidx,
    Nat.mod_eq_of_lt hprod,Nat.mod_eq_of_lt hTw,
    Nat.mod_eq_of_lt haddr,(hc _ hi).1,
    Nat.mod_eq_of_lt (show 1 < wordModulus w by omega),Function.update_idem]

lemma step_frame (s : Data) (T C q d x e a : ℕ) (c : ℕ → ℕ) (r : ℕ)
    (hr : r < 7 ∨ 15 < r) :
    (stepState s T C q d x e a c).registers r=s.registers r := by
  simp only [stepState,put,Function.update_of_ne (show r≠7 by omega),
    Function.update_of_ne (show r≠10 by omega),Function.update_of_ne (show r≠8 by omega),
    Function.update_of_ne (show r≠9 by omega),Function.update_of_ne (show r≠15 by omega),
    Function.update_of_ne (show r≠14 by omega),Function.update_of_ne (show r≠13 by omega),
    Function.update_of_ne (show r≠12 by omega),Function.update_of_ne (show r≠11 by omega)]

theorem loop_correct {w T C q : ℕ} (d x e a : ℕ) (s : Data) (c : ℕ → ℕ)
    (hW : 2 < wordModulus w) (hq : 0 < q) (hqw : q < wordModulus w)
    (hT : 0 < T) (hTT : T*T < wordModulus w) (hC : C+q*q < wordModulus w)
    (hd : d < wordModulus w) (hx : x < wordModulus w) (he : e < wordModulus w) (ha : a < T)
    (hc : ∀ i, i < q*q → s.memory (C+i)=some (c i) ∧ c i < T)
    (h7 : s.registers 7=d) (h8 : s.registers 8=e) (h9 : s.registers 9=a)
    (h10 : s.registers 10=x) (h16 : s.registers 16=T) (h17 : s.registers 17=C) :
    ∃ z, Eval w (loop q) s (13*d+1) z ∧ z.memory=s.memory ∧ z.registers 7=0 ∧
      z.registers 9=(a*value T q c d x e)%T ∧
      (∀ r, r < 7 ∨ 15 < r → z.registers r=s.registers r) := by
  induction d generalizing x e a s with
  | zero =>
    refine ⟨s,Eval.loopFalse ?_,rfl,h7,?_,by simp⟩
    · simp [test,operand_literal,operand_register,evalTest,h7]
    · simpa only [value,Nat.mul_mod_mod,Nat.mul_one,Nat.mod_eq_of_lt ha] using h9
  | succ d ih =>
    let u:=stepState s T C q (d+1) x e a c
    have es:=step_correct s c hW hq hqw hT hTT hC (by omega) hd hx he ha hc h7 h8 h9 h10 h16 h17
    obtain ⟨z,ez,hm,hz7,hz9,hf⟩:=ih (x/q) (e/q) ((a*c ((x%q)*q+e%q))%T) u
      (by omega) ((Nat.div_le_self ..).trans_lt hx) ((Nat.div_le_self ..).trans_lt he)
      (Nat.mod_lt _ hT) hc (by simp [u,stepState,put]) (by simp [u,stepState,put])
      (by simp [u,stepState,put]) (by simp [u,stepState,put])
      (by simpa [u,stepState,put] using h16) (by simpa [u,stepState,put] using h17)
    refine ⟨z,?_,hm,hz7,?_,?_⟩
    · rw [show 13*(d+1)+1=1+11+1+(13*d+1) by omega]
      exact Eval.loopTrue (by
        simp [test,operand_literal,operand_register,evalTest,h7,Nat.mod_eq_of_lt hd]) es ez
    · simpa only [value,Nat.mod_mul_mod,Nat.mul_mod_mod,Nat.mul_assoc] using hz9
    · intro r hr
      rw [hf r hr]
      exact step_frame s T C q (d+1) x e a c r hr
end DeterministicThreeSum.Structured.Indexed.Monomial
namespace DeterministicThreeSum.Structured.Indexed.Monomial
open DeterministicThreeSum.Rectangular Axis SparseAxis Cache Finset
open scoped BigOperators

lemma value_eq_tensor (T q : ℕ) (c : ℕ → ℕ) (d : ℕ) (x e : DigitBox q d) :
    (value T q c d (lowCode q d x) (lowCode q d e):ZMod T)=digitCoefficient T q q c d x e := by
  induction d with
  | zero => simp [value,digitCoefficient]
  | succ d ih =>
    rw [value,(lowCode_parts d x).1,(lowCode_parts d x).2,
      (lowCode_parts d e).1,(lowCode_parts d e).2]
    simpa only [ZMod.natCast_mod,Nat.cast_mul,digitCoefficient] using
      congrArg (fun z : ZMod T => (c (x.1.val*q+e.1.val):ZMod T)*z) (ih x.2 e.2)

theorem value_eq_monomial {T q : ℕ} (hq : 0 < q) (d : ℕ) (x e : DigitBox q d) :
    (value T q (powerTable T q) d (lowCode q d x) (lowCode q d e):ZMod T)=
      Weighted.monomial (digitFunction q d x) (digitFunction q d e) := by
  rw [value_eq_tensor,digitCoefficient_product]
  unfold Weighted.monomial
  apply prod_congr rfl
  intro k _
  exact powerTable_entry hq _ _
end DeterministicThreeSum.Structured.Indexed.Monomial
namespace DeterministicThreeSum.Structured.Indexed.FeatureDot
open Command

def value (T : ℕ) (weights points cache : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _,0 => 0
  | i,n+1 => (weights i*cache (points i)+value T weights points cache (i+1) n)%T

def body : Command := straight [
  .binary 7 .add (.register 3) (.register 0), .load 8 (.register 7),
  .binary 9 .add (.register 4) (.register 0), .load 10 (.register 9),
  .binary 11 .add (.register 5) (.register 8), .load 12 (.register 11),
  .binary 13 .mul (.register 10) (.register 12),
  .binary 13 .rem (.register 13) (.register 2),
  .binary 6 .add (.register 6) (.register 13),
  .binary 6 .rem (.register 6) (.register 2),
  .binary 0 .add (.register 0) (.literal 1)]
def loop : Command := .loop .lt (.register 0) (.register 1) body

def bodyState (s : Data) (T X Z U i x z u a : ℕ) : Data :=
  put (put (put (put (put (put (put (put (put s 7 (X+i)) 8 x) 9 (Z+i)) 10 z)
    11 (U+x)) 12 u) 13 ((z*u)%T)) 6 ((a+(z*u)%T)%T)) 0 (i+1)

lemma body_correct {w T X Z U i x z u a : ℕ} (s : Data)
    (hadd : 2*T < wordModulus w) (hmul : T*T < wordModulus w)
    (hT : 0 < T) (hi : i+1 < wordModulus w)
    (hX : X+i < wordModulus w) (hZ : Z+i < wordModulus w) (hU : U+x < wordModulus w)
    (hz : z < T) (hu : u < T) (ha : a < T)
    (hmemX : s.memory (X+i)=some x) (hmemZ : s.memory (Z+i)=some z)
    (hmemU : s.memory (U+x)=some u)
    (h0 : s.registers 0=i) (h2 : s.registers 2=T)
    (h3 : s.registers 3=X) (h4 : s.registers 4=Z) (h5 : s.registers 5=U) (h6 : s.registers 6=a) :
    Eval w body s 11 (bodyState s T X Z U i x z u a) := by
  have hTw : T < wordModulus w := by omega
  have hp : z*u < wordModulus w := (Nat.mul_le_mul hz.le hu.le).trans_lt hmul
  have hpr : (z*u)%T < T := Nat.mod_lt _ hT
  apply straight_correct
  simp [bodyState,execStraight,Atom.eval,operand_literal,operand_register,
    evalBinOp,put,h0,h2,h3,h4,h5,h6,hT.ne',Nat.mod_eq_of_lt hTw,
    Nat.mod_eq_of_lt (show i < wordModulus w by omega),Nat.mod_eq_of_lt hX,
    Nat.mod_eq_of_lt hZ,Nat.mod_eq_of_lt hU,Nat.mod_eq_of_lt (by omega : X < wordModulus w),
    hmemX,hmemZ,hmemU,Nat.mod_eq_of_lt hp,
    Nat.mod_eq_of_lt (by omega : a+(z*u)%T < wordModulus w),
    Nat.mod_eq_of_lt (by omega : 1 < wordModulus w),Nat.mod_eq_of_lt hi,Function.update_idem]

lemma body_frame (s : Data) (T X Z U i x z u a r : ℕ)
    (hr : r≠0) (hrr : r < 6 ∨ 13 < r) :
    (bodyState s T X Z U i x z u a).registers r=s.registers r := by
  simp only [bodyState,put,Function.update_of_ne hr,
    Function.update_of_ne (show r≠6 by omega),Function.update_of_ne (show r≠13 by omega),
    Function.update_of_ne (show r≠12 by omega),Function.update_of_ne (show r≠11 by omega),
    Function.update_of_ne (show r≠10 by omega),Function.update_of_ne (show r≠9 by omega),
    Function.update_of_ne (show r≠8 by omega),Function.update_of_ne (show r≠7 by omega)]

theorem loop_correct {w T X Z U A : ℕ} (i n a : ℕ) (s : Data)
    (weights points cache : ℕ → ℕ)
    (hadd : 2*T < wordModulus w) (hmul : T*T < wordModulus w) (hT : 0 < T)
    (hin : i+n+1 < wordModulus w) (hX : X+i+n < wordModulus w)
    (hZ : Z+i+n < wordModulus w) (hU : U+A < wordModulus w) (ha : a < T)
    (hx : ∀ j, i ≤ j → j < i+n → s.memory (X+j)=some (points j) ∧ points j < A)
    (hz : ∀ j, i ≤ j → j < i+n → s.memory (Z+j)=some (weights j) ∧ weights j < T)
    (hu : ∀ j, j < A → s.memory (U+j)=some (cache j) ∧ cache j < T)
    (h0 : s.registers 0=i) (h1 : s.registers 1=i+n) (h2 : s.registers 2=T)
    (h3 : s.registers 3=X) (h4 : s.registers 4=Z) (h5 : s.registers 5=U) (h6 : s.registers 6=a) :
    ∃ t, Eval w loop s (13*n+1) t ∧ t.memory=s.memory ∧ t.registers 0=i+n ∧
      t.registers 6=(a+value T weights points cache i n)%T ∧
      (∀ r, r≠0 → (r < 6 ∨ 13 < r) → t.registers r=s.registers r) := by
  induction n generalizing i a s with
  | zero =>
    refine ⟨s,Eval.loopFalse ?_,rfl,by simpa using h0,?_,by simp⟩
    · simp [test,operand_register,evalTest,h0,h1]
    · simpa only [value,Nat.add_zero,Nat.mod_eq_of_lt ha] using h6
  | succ n ih =>
    have hxi:=hx i le_rfl (by omega)
    have hzi:=hz i le_rfl (by omega)
    have hui:=hu (points i) hxi.2
    let u:=bodyState s T X Z U i (points i) (weights i) (cache (points i)) a
    have es:=body_correct s hadd hmul hT (by omega) (by omega) (by omega) (by omega)
      hzi.2 hui.2 ha hxi.1 hzi.1 hui.1 h0 h2 h3 h4 h5 h6
    obtain ⟨t,et,htm,ht0,ht6,htf⟩:=ih (i+1) ((a+(weights i*cache (points i))%T)%T) u
      (by omega) (by omega) (by omega) (Nat.mod_lt _ hT)
      (by intro j hj hj'; exact hx j (by omega) (by omega))
      (by intro j hj hj'; exact hz j (by omega) (by omega)) hu
      (by simp [u,bodyState,put]) (by simp [u,bodyState,put,h1]; omega)
      (by simp [u,bodyState,put,h2]) (by simp [u,bodyState,put,h3])
      (by simp [u,bodyState,put,h4]) (by simp [u,bodyState,put,h5]) (by simp [u,bodyState,put])
    refine ⟨t,?_,htm,by omega,?_,?_⟩
    · rw [show 13*(n+1)+1=1+11+1+(13*n+1) by omega]
      exact Eval.loopTrue (by
        simp [test,operand_register,evalTest,h0,h1,
          Nat.mod_eq_of_lt (by omega : i < wordModulus w),
          Nat.mod_eq_of_lt (by omega : i+(n+1) < wordModulus w)]) es et
    · simpa only [value,Nat.add_mod_mod,Nat.mod_add_mod,Nat.add_assoc] using ht6
    · intro r hr hrr
      rw [htf r hr hrr]
      exact body_frame s T X Z U i (points i) (weights i) (cache (points i)) a r hr hrr

lemma value_cast (T : ℕ) (weights points cache : ℕ → ℕ) (i n : ℕ) :
    (value T weights points cache i n:ZMod T)=
      ∑ j : Fin n, (weights (i+j.val):ZMod T)*(cache (points (i+j.val)):ZMod T) := by
  induction n generalizing i with
  | zero => simp [value]
  | succ n ih =>
    rw [value,ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ,Nat.add_comm,Nat.add_left_comm]
end DeterministicThreeSum.Structured.Indexed.FeatureDot
namespace DeterministicThreeSum.Structured.Indexed.GFeature
open Command

def prepare : Command := straight [
  .binary 21 .add (.register 3) (.register 0), .load 10 (.register 21),
  .binary 22 .add (.register 4) (.register 0), .load 20 (.register 22),
  .assign 7 (.register 18), .assign 8 (.register 5),
  .binary 9 .rem (.literal 1) (.register 2),
  .assign 16 (.register 2), .assign 17 (.register 19)]
def prepared (s : Data) (T C X Z i x z d e : ℕ) : Data :=
  put (put (put (put (put (put (put (put (put s 21 (X+i)) 10 x) 22 (Z+i)) 20 z)
    7 d) 8 e) 9 (1%T)) 16 T) 17 C

def finish : Command := straight [
  .binary 23 .mul (.register 20) (.register 9),
  .binary 23 .rem (.register 23) (.register 2),
  .binary 6 .add (.register 6) (.register 23),
  .binary 6 .rem (.register 6) (.register 2),
  .binary 0 .add (.register 0) (.literal 1)]
def finished (s : Data) (T i z v a : ℕ) : Data :=
  put (put (put s 23 ((z*v)%T)) 6 ((a+(z*v)%T)%T)) 0 (i+1)

def body (q : ℕ) : Command := .seq prepare (.seq (Monomial.loop q) finish)
def loop (q : ℕ) : Command := .loop .lt (.register 0) (.register 1) (body q)

def value (T q : ℕ) (c weights points : ℕ → ℕ) (d e : ℕ) : ℕ → ℕ → ℕ
  | _,0 => 0
  | i,n+1 => (weights i*Monomial.value T q c d (points i) e+value T q c weights points d e (i+1) n)%T

lemma prepare_correct {w T C X Z i x z d e : ℕ} (s : Data)
    (hW : 2 < wordModulus w) (hT : 0 < T) (hTw : T < wordModulus w)
    (hC : C < wordModulus w) (hX : X+i < wordModulus w) (hZ : Z+i < wordModulus w)
    (_hx : x < wordModulus w) (_hz : z < wordModulus w)
    (hd : d < wordModulus w) (he : e < wordModulus w)
    (hmX : s.memory (X+i)=some x) (hmZ : s.memory (Z+i)=some z)
    (h0 : s.registers 0=i) (h2 : s.registers 2=T) (h3 : s.registers 3=X)
    (h4 : s.registers 4=Z) (h5 : s.registers 5=e)
    (h18 : s.registers 18=d) (h19 : s.registers 19=C) :
    Eval w prepare s 9 (prepared s T C X Z i x z d e) := by
  apply straight_correct
  simp [prepared,execStraight,Atom.eval,operand_literal,operand_register,evalBinOp,put,
    h0,h2,h3,h4,h5,h18,h19,hT.ne',Nat.mod_eq_of_lt hTw,Nat.mod_eq_of_lt hC,
    Nat.mod_eq_of_lt hX,Nat.mod_eq_of_lt hZ,Nat.mod_eq_of_lt (by omega : X < wordModulus w),
    Nat.mod_eq_of_lt (by omega : i < wordModulus w),
    hmX,hmZ,Nat.mod_eq_of_lt hd,Nat.mod_eq_of_lt he,
    Nat.mod_eq_of_lt (by omega : 1 < wordModulus w)]

lemma prepare_frame (s : Data) (T C X Z i x z d e r : ℕ) (hr : r < 7 ∨ 23 ≤ r ∨ r=18 ∨ r=19) :
    (prepared s T C X Z i x z d e).registers r=s.registers r := by
  simp only [prepared,put,Function.update_of_ne (show r≠17 by omega),
    Function.update_of_ne (show r≠16 by omega),Function.update_of_ne (show r≠9 by omega),
    Function.update_of_ne (show r≠8 by omega),Function.update_of_ne (show r≠7 by omega),
    Function.update_of_ne (show r≠20 by omega),Function.update_of_ne (show r≠22 by omega),
    Function.update_of_ne (show r≠10 by omega),Function.update_of_ne (show r≠21 by omega)]

lemma finish_correct {w T i z v a : ℕ} (s : Data)
    (hadd : 2*T < wordModulus w) (hmul : T*T < wordModulus w)
    (hT : 0 < T) (hi : i+1 < wordModulus w) (hz : z < T) (hv : v < T) (ha : a < T)
    (h0 : s.registers 0=i) (h2 : s.registers 2=T) (h6 : s.registers 6=a)
    (h9 : s.registers 9=v) (h20 : s.registers 20=z) :
    Eval w finish s 5 (finished s T i z v a) := by
  have hTw : T < wordModulus w := by omega
  have hp : z*v < wordModulus w := (Nat.mul_le_mul hz.le hv.le).trans_lt hmul
  have hm : (z*v)%T < T := Nat.mod_lt _ hT
  apply straight_correct
  simp [finished,execStraight,Atom.eval,operand_literal,operand_register,evalBinOp,put,
    h0,h2,h6,h9,h20,hT.ne',Nat.mod_eq_of_lt hTw,Nat.mod_eq_of_lt (hz.trans hTw),
    Nat.mod_eq_of_lt (hv.trans hTw),Nat.mod_eq_of_lt hp,
    Nat.mod_eq_of_lt (by omega : a+(z*v)%T < wordModulus w),
    Nat.mod_eq_of_lt (by omega : 1 < wordModulus w),
    Nat.mod_eq_of_lt hi,Function.update_idem]

lemma finish_frame (s : Data) (T i z v a r : ℕ) (hr : r≠0) (h6 : r≠6) (h23 : r≠23) :
    (finished s T i z v a).registers r=s.registers r := by
  simp only [finished,put,Function.update_of_ne hr,Function.update_of_ne h6,Function.update_of_ne h23]

lemma body_correct {w T C q X Z i x z d e a : ℕ} (s : Data) (c : ℕ → ℕ)
    (hW : 2 < wordModulus w) (hq : 0 < q) (hqw : q < wordModulus w)
    (hT : 0 < T) (hadd : 2*T < wordModulus w) (hmul : T*T < wordModulus w)
    (hC : C+q*q < wordModulus w) (hi : i+1 < wordModulus w)
    (hX : X+i < wordModulus w) (hZ : Z+i < wordModulus w)
    (hx : x < wordModulus w) (hz : z < T) (hd : d < wordModulus w)
    (he : e < wordModulus w) (ha : a < T)
    (hmX : s.memory (X+i)=some x) (hmZ : s.memory (Z+i)=some z)
    (hc : ∀ j, j < q*q → s.memory (C+j)=some (c j) ∧ c j < T)
    (h0 : s.registers 0=i) (h2 : s.registers 2=T) (h3 : s.registers 3=X)
    (h4 : s.registers 4=Z) (h5 : s.registers 5=e) (h6 : s.registers 6=a)
    (h18 : s.registers 18=d) (h19 : s.registers 19=C) :
    ∃ t, Eval w (body q) s (13*d+15) t ∧ t.memory=s.memory ∧
      t.registers 0=i+1 ∧ t.registers 6=(a+z*Monomial.value T q c d x e)%T ∧
      (∀ r, r≠0 → r≠6 → (r<7 ∨ r=18 ∨ r=19 ∨ 23<r) → t.registers r=s.registers r) := by
  have hTw : T < wordModulus w := by omega
  let u:=prepared s T C X Z i x z d e
  have ep:=prepare_correct s hW hT hTw (by omega) hX hZ hx (hz.trans hTw) hd he hmX hmZ h0 h2 h3 h4 h5 h18 h19
  obtain ⟨v,ev,hvm,hv7,hv9,hvf⟩:=Monomial.loop_correct d x e (1%T) u c hW hq hqw hT hmul hC hd hx he
    (Nat.mod_lt _ hT) hc (by simp [u,prepared,put]) (by simp [u,prepared,put])
    (by simp [u,prepared,put]) (by simp [u,prepared,put]) (by simp [u,prepared,put]) (by simp [u,prepared,put])
  have hv9' : v.registers 9=Monomial.value T q c d x e := by
    simpa only [Nat.mod_mul_mod,Nat.one_mul,Nat.mod_eq_of_lt (Monomial.value_lt hT c d x e)] using hv9
  have vv {r : ℕ} (hr : r<7 ∨ r=18 ∨ r=19 ∨ 23<r) : v.registers r=s.registers r := by
    rw [hvf r (by omega)]
    exact prepare_frame s T C X Z i x z d e r (by omega)
  have v20 : v.registers 20=z := by rw [hvf 20 (by omega)]; simp [u,prepared,put]
  have ef:=finish_correct v hadd hmul hT hi hz (Monomial.value_lt hT c d x e) ha
    ((vv (by omega)).trans h0) ((vv (by omega)).trans h2) ((vv (by omega)).trans h6) hv9' v20
  refine ⟨finished v T i z (Monomial.value T q c d x e) a,?_,hvm,?_,?_,?_⟩
  · simpa only [body,show 9+(13*d+1+5)=13*d+15 by omega] using Eval.seq ep (Eval.seq ev ef)
  · simp [finished,put]
  · simp [finished,put,Nat.add_mod_mod]
  · intro r hr h6 hrange
    rw [finish_frame v T i z (Monomial.value T q c d x e) a r hr h6 (by omega)]
    exact vv hrange
end DeterministicThreeSum.Structured.Indexed.GFeature
namespace DeterministicThreeSum.Structured.Indexed.GFeature
open Command
open scoped BigOperators

theorem loop_correct {w T C q X Z d e : ℕ} (i n a : ℕ) (s : Data)
    (c weights points : ℕ → ℕ)
    (hW : 2 < wordModulus w) (hq : 0 < q) (hqw : q < wordModulus w)
    (hT : 0 < T) (hadd : 2*T < wordModulus w) (hmul : T*T < wordModulus w)
    (hC : C+q*q < wordModulus w) (hin : i+n+1 < wordModulus w)
    (hX : X+i+n < wordModulus w) (hZ : Z+i+n < wordModulus w)
    (hd : d < wordModulus w) (he : e < wordModulus w) (ha : a < T)
    (hx : ∀ j, i ≤ j → j < i+n → s.memory (X+j)=some (points j) ∧ points j < wordModulus w)
    (hz : ∀ j, i ≤ j → j < i+n → s.memory (Z+j)=some (weights j) ∧ weights j < T)
    (hc : ∀ j, j < q*q → s.memory (C+j)=some (c j) ∧ c j < T)
    (h0 : s.registers 0=i) (h1 : s.registers 1=i+n) (h2 : s.registers 2=T)
    (h3 : s.registers 3=X) (h4 : s.registers 4=Z) (h5 : s.registers 5=e)
    (h6 : s.registers 6=a) (h18 : s.registers 18=d) (h19 : s.registers 19=C) :
    ∃ t, Eval w (loop q) s ((13*d+17)*n+1) t ∧ t.memory=s.memory ∧
      t.registers 0=i+n ∧ t.registers 6=(a+value T q c weights points d e i n)%T ∧
      (∀ r, r≠0 → r≠6 → (r<7 ∨ r=18 ∨ r=19 ∨ 23<r) → t.registers r=s.registers r) := by
  induction n generalizing i a s with
  | zero =>
    refine ⟨s,Eval.loopFalse ?_,rfl,by simpa using h0,?_,by simp⟩
    · simp [test,operand_register,evalTest,h0,h1]
    · simpa only [value,Nat.add_zero,Nat.mod_eq_of_lt ha] using h6
  | succ n ih =>
    have hxi:=hx i le_rfl (by omega)
    have hzi:=hz i le_rfl (by omega)
    obtain ⟨u,eu,hum,hu0,hu6,huf⟩:=body_correct s c hW hq hqw hT hadd hmul hC
      (by omega) (by omega) (by omega) hxi.2 hzi.2 hd he ha hxi.1 hzi.1 hc h0 h2 h3 h4 h5 h6 h18 h19
    obtain ⟨t,et,htm,ht0,ht6,htf⟩:=ih (i+1) ((a+weights i*Monomial.value T q c d (points i) e)%T) u
      (by omega) (by omega) (by omega) (Nat.mod_lt _ hT)
      (by intro j hj hj'; rw [hum]; exact hx j (by omega) (by omega))
      (by intro j hj hj'; rw [hum]; exact hz j (by omega) (by omega))
      (by intro j hj; rw [hum]; exact hc j hj) hu0
      (by rw [huf 1 (by omega) (by omega) (by omega),h1]; omega)
      (by rw [huf 2 (by omega) (by omega) (by omega),h2])
      (by rw [huf 3 (by omega) (by omega) (by omega),h3])
      (by rw [huf 4 (by omega) (by omega) (by omega),h4])
      (by rw [huf 5 (by omega) (by omega) (by omega),h5]) hu6
      (by rw [huf 18 (by omega) (by omega) (by omega),h18])
      (by rw [huf 19 (by omega) (by omega) (by omega),h19])
    refine ⟨t,?_,htm.trans hum,by omega,?_,?_⟩
    · rw [show (13*d+17)*(n+1)+1=1+(13*d+15)+1+((13*d+17)*n+1) by ring]
      exact Eval.loopTrue (by
        simp [test,operand_register,evalTest,h0,h1,
          Nat.mod_eq_of_lt (by omega : i < wordModulus w),
          Nat.mod_eq_of_lt (by omega : i+(n+1) < wordModulus w)]) eu et
    · simpa only [value,Nat.mod_add_mod,Nat.add_mod_mod,Nat.add_assoc] using ht6
    · intro r hr h6 hrr
      exact (htf r hr h6 hrr).trans (huf r hr h6 hrr)

lemma value_cast (T q : ℕ) (c weights points : ℕ → ℕ) (d e i n : ℕ) :
    (value T q c weights points d e i n : ZMod T)=
      ∑ j : Fin n, (weights (i+j.val):ZMod T)*(Monomial.value T q c d (points (i+j.val)) e:ZMod T) := by
  induction n generalizing i with
  | zero => simp [value]
  | succ n ih =>
    rw [value,ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ,Nat.add_comm,Nat.add_left_comm]
end DeterministicThreeSum.Structured.Indexed.GFeature
namespace DeterministicThreeSum.Structured.Indexed
open DeterministicThreeSum.Rectangular Axis SparseAxis Cache Finset
open scoped BigOperators

theorem E_value {T m b d D H n : ℕ} (hm : 0 < m)
    (P : MvPolynomial (Fin d) (ZMod T)) (hP : P.totalDegree ≤ D) (a : ℕ → ℕ)
    (ha : ∀ (u : DigitBox m d) (v : DigitBox b d),
      (∑ k, (digitFunction m d u k).val)+(∑ k, (digitFunction b d v k).val) ≤ D →
      (a (lowCode (m*b) d (zipDigit m b d u v)):ZMod T)=
        Sparse.coefficient (ZMod T) m b P (digitFunction m d u) (digitFunction b d v))
    (j : DigitBox b d) (x : Fin n → DigitBox m d) (z : Fin n → ZMod T)
    (points weights : ℕ → ℕ)
    (hx : ∀ k : Fin n, points k.val=lowCode m d (x k))
    (hz : ∀ k : Fin n, (weights k.val : ZMod T)=z k) :
    (FeatureDot.value T weights points
      (tensorValue T m m (powerTable T m) d (gathered false m b d D H (lowCode b d j) a)) 0 n : ZMod T)=
      ∑ k : Fin n, z k*Weighted.U P (digitFunction b d j) (digitFunction m d (x k)) := by
  rw [FeatureDot.value_cast]
  apply sum_congr rfl
  intro k _
  simp only [Nat.zero_add,hx,hz,Uvalue_source hm P hP a ha j]

theorem G_value {T m d n : ℕ} (hm : 0 < m) (i : DigitBox m d)
    (x : Fin n → DigitBox m d) (z : Fin n → ZMod T) (points weights : ℕ → ℕ)
    (hx : ∀ k : Fin n, points k.val=lowCode m d (x k))
    (hz : ∀ k : Fin n, (weights k.val : ZMod T)=z k) :
    (GFeature.value T m (powerTable T m) weights points d (lowCode m d i) 0 n : ZMod T)=
      ∑ k : Fin n, z k*Weighted.monomial (digitFunction m d (x k)) (digitFunction m d i) := by
  rw [GFeature.value_cast]
  apply sum_congr rfl
  intro k _
  simp only [Nat.zero_add,hx,hz,Monomial.value_eq_monomial hm]

lemma group_enumeration_sum {R A : Type} [AddCommMonoid R] (members : Finset A) (n : ℕ)
    (enumerate : Fin n ≃ {a // a ∈ members}) (f : A → R) :
    (∑ k : Fin n, f (enumerate k).val)=∑ a∈members, f a := by
  exact (enumerate.sum_comp (fun a => f a.val)).trans (sum_coe_sort members f)
end DeterministicThreeSum.Structured.Indexed

end OAI
