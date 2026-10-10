import Mathlib
import OAI.Computability.DeterministicSum.TensorEncoding
import OAI.Computability.DeterministicSum.NewtonCommands
import OAI.Computability.DeterministicSum.PolynomialBounds

namespace OAI

/-! Exact transform coefficients and integer-table compilation. -/

namespace DeterministicThreeSum.Structured.Indexed.SparseAxis
open Finset DeterministicThreeSum.Rectangular Axis
open scoped BigOperators
noncomputable section

def digitFunction (q : ℕ) : (d : ℕ) → DigitBox q d → Fin d → Fin q
  | 0,_ => Fin.elim0
  | d+1,x => Fin.cons x.1 (digitFunction q d x.2)

def functionDigit (q : ℕ) : (d : ℕ) → (Fin d → Fin q) → DigitBox q d
  | 0,_ => 0
  | d+1,f => (f 0,functionDigit q d (Fin.tail f))

lemma functionDigit_digitFunction (q d : ℕ) (x : DigitBox q d) :
    functionDigit q d (digitFunction q d x)=x := by
  induction d with
  | zero => exact Subsingleton.elim _ _
  | succ d ih => simp [functionDigit,digitFunction,ih]

lemma digitFunction_functionDigit (q d : ℕ) (f : Fin d → Fin q) :
    digitFunction q d (functionDigit q d f)=f := by
  induction d with
  | zero => funext i; exact Fin.elim0 i
  | succ d ih => simp [functionDigit,digitFunction,ih]

def digitFunctionEquiv (q d : ℕ) : DigitBox q d ≃ (Fin d → Fin q) where
  toFun := digitFunction q d
  invFun := functionDigit q d
  left_inv := functionDigit_digitFunction q d
  right_inv := digitFunction_functionDigit q d

lemma digitCoefficient_product (T q r : ℕ) (c : ℕ → ℕ) (d : ℕ)
    (v : DigitBox r d) (u : DigitBox q d) :
    digitCoefficient T q r c d v u =
      ∏ k : Fin d, (c ((digitFunction r d v k).val*q+(digitFunction q d u k).val):ZMod T) := by
  induction d with
  | zero => simp [digitCoefficient]
  | succ d ih => simp [digitCoefficient,digitFunction,Fin.prod_univ_succ,ih]

end
end DeterministicThreeSum.Structured.Indexed.SparseAxis
namespace DeterministicThreeSum.Structured.Indexed.NewtonPass
open Command Axis DeterministicThreeSum.Rectangular DeterministicThreeSum.Newton SparseAxis Finset
open scoped BigOperators
noncomputable section

lemma value_cons {q : ℕ} (hq : 0<q) (d a n : ℕ) (hn : n<q^d) :
    DigitSum.value q (d+1) (a*q^d+n)=a%q+DigitSum.value q d n := by
  induction d generalizing n with
  | zero =>
    have hn0 : n=0 := by simpa using hn
    simp [hn0,DigitSum.value]
  | succ d ih =>
    have hd : n/q<q^d := (Nat.div_lt_iff_lt_mul hq).mpr (by simpa only [pow_succ] using hn)
    have hx : a*q^(d+1)+n=(a*q^d)*q+n := by rw [pow_succ]; ring
    have hm : ((a*q^d)*q+n)%q=n%q := by simp [Nat.add_mod]
    have hdiv : ((a*q^d)*q+n)/q=a*q^d+n/q := by
      rw [Nat.mul_comm (a*q^d) q,Nat.mul_add_div hq]
    rw [DigitSum.value,hx,hm,hdiv,ih _ hd,DigitSum.value]
    omega

lemma digitCode_degree {q : ℕ} (hq : 0<q) (d : ℕ) (u : DigitBox q d) :
    DigitSum.value q d (digitCode q d u)=degree (digitFunction q d u) := by
  induction d with
  | zero => simp [DigitSum.value,degree]
  | succ d ih =>
    rw [digitCode,value_cons hq d _ _ (digitCode_lt hq d u.2),Nat.mod_eq_of_lt u.1.isLt,ih]
    simp [degree,digitFunction,Fin.sum_univ_succ]

def inverseTable (T q : ℕ) (node : Fin q → ZMod T) (z : ℕ) : ℕ :=
  if h : z<q*q then (((entry node)⁻¹)
    ⟨z/q,(Nat.div_lt_iff_lt_mul (by nlinarith : 0<q)).mpr h⟩
    ⟨z%q,Nat.mod_lt _ (by nlinarith : 0<q)⟩).val else 0

def conversionTable (T q : ℕ) (node : Fin q → ZMod T) (z : ℕ) : ℕ :=
  if h : z<q*q then (conversion node
    ⟨z%q,Nat.mod_lt _ (by nlinarith : 0<q)⟩
    ⟨z/q,(Nat.div_lt_iff_lt_mul (by nlinarith : 0<q)).mpr h⟩).val else 0

lemma inverseTable_entry {T q : ℕ} (hT : 0<T) (node : Fin q → ZMod T) (i j : Fin q) :
    (inverseTable T q node (i.val*q+j.val):ZMod T)=((entry node)⁻¹) i j := by
  let : NeZero T := ⟨by omega⟩
  have h : i.val*q+j.val<q*q := by nlinarith [i.isLt,j.isLt]
  have hq : 0<q := Nat.zero_lt_of_lt i.isLt
  have hd : (i.val*q+j.val)/q=i.val := by
    rw [Nat.mul_comm i.val q,Nat.mul_add_div hq,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have hm : (i.val*q+j.val)%q=j.val := by simp [Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
  simp [inverseTable,h,hd,hm]

lemma conversionTable_entry {T q : ℕ} (hT : 0<T) (node : Fin q → ZMod T) (i j : Fin q) :
    (conversionTable T q node (i.val*q+j.val):ZMod T)=conversion node j i := by
  let : NeZero T := ⟨by omega⟩
  have h : i.val*q+j.val<q*q := by nlinarith [i.isLt,j.isLt]
  have hq : 0<q := Nat.zero_lt_of_lt i.isLt
  have hd : (i.val*q+j.val)/q=i.val := by
    rw [Nat.mul_comm i.val q,Nat.mul_add_div hq,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have hm : (i.val*q+j.val)%q=j.val := by simp [Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
  simp [conversionTable,h,hd,hm]

lemma tensorValue_coefficients {T q d : ℕ} (hT : 0<T) (hq : 0<q)
    (node : Fin q → ZMod T) (x : ℕ → ℕ) (a : ℕ) (v : DigitBox q d) :
    (tensorValue T q q (inverseTable T q node) d x (a*q^d+digitCode q d v):ZMod T)=
      coefficients node (fun u => (x (a*q^d+digitCode q d (functionDigit q d u)):ZMod T))
        (digitFunction q d v) := by
  rw [tensorValue_eq_tensor hq hq]
  unfold coefficients Matrix.mulVec dotProduct tensor
  rw [← (digitFunctionEquiv q d).sum_comp]
  apply sum_congr rfl
  intro u _
  simp only [digitCoefficient_product,inverseTable_entry hT,
    digitFunctionEquiv,Equiv.coe_fn_mk,functionDigit_digitFunction]

theorem output_source {T q d D : ℕ} (hT : 0<T) (hq : 0<q)
    (node : Fin q → ZMod T) (x : ℕ → ℕ) (a : ℕ) (v : DigitBox q d) :
    (tensorValue T q q (conversionTable T q node) d
      (filtered q d D (tensorValue T q q (inverseTable T q node) d x))
      (a*q^d+digitCode q d v):ZMod T)=
    (truncatedPolynomial node
      (fun u => (x (a*q^d+digitCode q d (functionDigit q d u)):ZMod T)) D).coeff
      (exponentVector (digitFunction q d v)) := by
  rw [tensorValue_eq_tensor hq hq,coefficient_truncated]
  rw [← (digitFunctionEquiv q d).sum_comp]
  apply sum_congr rfl
  intro u _
  have hm : (a*q^d+digitCode q d u)%(q^d)=digitCode q d u := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt (digitCode_lt hq d u)]
  change digitCoefficient T q q (conversionTable T q node) d v u *
      (filtered q d D (tensorValue T q q (inverseTable T q node) d x)
        (a*q^d+digitCode q d u):ZMod T) =
    (if degree (digitFunction q d u)≤D then
      coefficients node (fun u => (x (a*q^d+digitCode q d (functionDigit q d u)):ZMod T))
        (digitFunction q d u) else 0) *
      ∏ i, conversion node (digitFunction q d u i) (digitFunction q d v i)
  simp only [digitCoefficient_product,conversionTable_entry hT,filtered,hm,digitCode_degree hq]
  by_cases hh : degree (digitFunction q d u)≤D
  · simp only [not_lt.mpr hh,ite_false,hh,ite_true,tensorValue_coefficients hT hq]
    ring
  · simp [hh,show D<degree (digitFunction q d u) by omega]

end
end DeterministicThreeSum.Structured.Indexed.NewtonPass
namespace DeterministicThreeSum.Structured.Indexed
open Command

def integerCommand (a : ℤ) : Command :=
  if 0≤a then straight [.assign 0 (.literal a.natAbs),
      .binary 0 .rem (.register 0) (.register 2)]
  else straight [.assign 0 (.literal a.natAbs),
      .binary 0 .rem (.register 0) (.register 2),
      .binary 0 .sub (.register 2) (.register 0),
      .binary 0 .rem (.register 0) (.register 2)]

def integerValue (T : ℕ) (a : ℤ) : ℕ :=
  if 0≤a then a.natAbs%T else (T-a.natAbs%T)%T

lemma integerValue_lt {T : ℕ} (hT : 0 < T) (a : ℤ) : integerValue T a<T := by
  unfold integerValue; split_ifs <;> exact Nat.mod_lt _ hT

lemma integerValue_cast {T : ℕ} (hT : 0 < T) (a : ℤ) : (integerValue T a:ZMod T)=(a:ZMod T) := by
  let : NeZero T := ⟨by omega⟩
  unfold integerValue
  split_ifs with ha
  · have he : (a.natAbs:ℤ)=a := by omega
    rw [ZMod.natCast_mod]
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ZMod T)) he
  · have he : a=-(a.natAbs:ℤ) := by omega
    rw [he,ZMod.natCast_mod,Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ hT))]
    simp

lemma integerCommand_correct {w T : ℕ} (s : Data) (a : ℤ)
    (hT : 0 < T) (hTw : T<wordModulus w) (ha : a.natAbs<wordModulus w)
    (h2 : s.registers 2=T) :
    ∃ cost, Eval w (integerCommand a) s cost (put s 0 (integerValue T a)) ∧ cost≤4 := by
  have hV : a.natAbs%T<wordModulus w := (Nat.mod_lt _ hT).trans hTw
  have hsub : T-a.natAbs%T<wordModulus w := lt_of_le_of_lt (Nat.sub_le ..) hTw
  have hs : T+wordModulus w-a.natAbs%T=(T-a.natAbs%T)+wordModulus w := by
    have hh:=Nat.mod_lt a.natAbs hT; omega
  by_cases hpos : 0≤a
  · refine ⟨2,?_,by omega⟩
    rw [integerCommand,ite_eq_left hpos,integerValue,ite_eq_left hpos]
    apply straight_correct
    simp [execStraight,Atom.eval,operand_literal,operand_register,evalBinOp,put,h2,
      Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hTw,hT.ne',Function.update_idem]
  · refine ⟨4,?_,by omega⟩
    rw [integerCommand,ite_eq_right hpos,integerValue,ite_eq_right hpos]
    apply straight_correct
    simp [execStraight,Atom.eval,operand_literal,operand_register,evalBinOp,put,h2,
      Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hTw,Nat.mod_eq_of_lt hV,hT.ne',Function.update_idem,
      hs,Nat.mod_eq_of_lt hsub]

def integerTable (i : ℕ) : List ℤ → Command
  | [] => .skip
  | a::rest => .seq (integerCommand a) (.seq (straight [
      .binary 1 .add (.register 3) (.literal i),.store (.register 1) (.register 0)])
      (integerTable (i+1) rest))

def integerTableMemory (T base i : ℕ) : List ℤ → (ℕ → Option ℕ) → (ℕ → Option ℕ)
  | [],mem => mem
  | a::rest,mem => integerTableMemory T base (i+1) rest (Function.update mem (base+i) (some (integerValue T a)))

lemma integerTable_correct {w T base i : ℕ} (s : Data) (xs : List ℤ)
    (hT : 0 < T) (hTw : T<wordModulus w) (hbase : base+i+xs.length<wordModulus w)
    (ha : ∀ a∈xs, a.natAbs<wordModulus w) (h2 : s.registers 2=T) (h3 : s.registers 3=base) :
    ∃ cost z, Eval w (integerTable i xs) s cost z ∧ cost≤6*xs.length ∧
      z.memory=integerTableMemory T base i xs s.memory ∧
      (∀ r, 2≤r → z.registers r=s.registers r) := by
  induction xs generalizing s i with
  | nil => exact ⟨0,s,Eval.skip s,by simp,rfl,by simp⟩
  | cons a xs ih =>
    obtain ⟨c,he,hc⟩:=integerCommand_correct s a hT hTw (ha a (by simp)) h2
    let s1:=put s 0 (integerValue T a)
    let s2:=put s1 1 (base+i)
    let s3:Data:={s2 with memory:=Function.update s.memory (base+i) (some (integerValue T a))}
    have hb : base+i<wordModulus w := by simpa only [List.length_cons] using (show base+i<wordModulus w by simp only [List.length_cons] at hbase; omega)
    have ee : Eval w (straight [.binary 1 .add (.register 3) (.literal i),
        .store (.register 1) (.register 0)]) s1 2 s3 := by
      apply straight_correct
      simp [s3,s2,s1,execStraight,Atom.eval,operand_literal,operand_register,evalBinOp,put,h3,
        Nat.mod_eq_of_lt (show base<wordModulus w by omega),Nat.mod_eq_of_lt (show i<wordModulus w by omega),
        Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt ((integerValue_lt hT a).trans hTw)]
    have hr (r : ℕ) (hr : 2≤r) : s3.registers r=s.registers r := by
      simp [s3,s2,s1,put,show r≠1 by omega,show r≠0 by omega]
    obtain ⟨cr,z,er,hcr,hmz,hzr⟩:=ih (i:=i+1) s3 (by simp only [List.length_cons] at hbase; omega)
      (fun a ha' => ha a (by simp [ha'])) ((hr 2 (by omega)).trans h2) ((hr 3 (by omega)).trans h3)
    refine ⟨c+(2+cr),z,Eval.seq he (Eval.seq ee er),?_,?_,fun r h => (hzr r h).trans (hr r h)⟩
    · simp only [List.length_cons]; omega
    · exact hmz
end DeterministicThreeSum.Structured.Indexed

end OAI
