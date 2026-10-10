import Mathlib
import OAI.Computability.DeterministicSum.NewtonCoefficients

namespace OAI

/-! Costed modular powers, inverses and common-denominator tables. -/

namespace DeterministicThreeSum.Structured.ModularPower
open Command

def bit : Command := .atom (.binary 4 .rem (.register 3) (.literal 2))
def conditional : Command := .ite .eq (.register 4) (.literal 1) Modular.mul .skip
def square : Command := straight [.binary 1 .mul (.register 1) (.register 1),
  .binary 1 .rem (.register 1) (.register 2),.binary 3 .quot (.register 3) (.literal 2)]
def step : Command := .seq bit (.seq conditional square)
def loop : Command := .loop .lt (.literal 0) (.register 3) step

def nextAcc (T a b e : ℕ) : ℕ := if e%2=1 then a*b%T else a

def nextState (T a b e : ℕ) (s : Data) : Data :=
  put (put (put (put s 4 (e%2)) 0 (nextAcc T a b e)) 1 (b*b%T)) 3 (e/2)

lemma conditional_correct {w T a b e : ℕ} (s : Data)
    (hW : 2 < wordModulus w) (hT : 0 < T) (hmul : T*T < wordModulus w)
    (ha : a < T) (hb : b < T)
    (h0 : s.registers 0=a) (h1 : s.registers 1=b) (h2 : s.registers 2=T)
    (h4 : s.registers 4=e%2) :
    ∃ c z, Eval w conditional s c z ∧ c ≤ 4 ∧
      z=put s 0 (nextAcc T a b e) := by
  have ht : test w s .eq (.register 4) (.literal 1)=decide (e%2=1) := by
    simp [test,operand_register,operand_literal,evalTest,h4,Nat.mod_eq_of_lt (by omega : 1 < wordModulus w),
      Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt e (by omega : 0 < 2)) hW)]
  by_cases h : e%2=1
  · refine ⟨4,put s 0 (a*b%T),?_,by omega,by simp [nextAcc,h]⟩
    exact Eval.iteTrue (by simpa [h] using ht) (Modular.mul_correct s hT hmul ha hb h0 h1 h2)
  · refine ⟨1,s,Eval.iteFalse (by simpa [h] using ht) (Eval.skip s),by omega,?_⟩
    simp only [nextAcc,ite_eq_right h]
    apply Data.ext
    · exact by simpa only [← h0,put] using (Function.update_eq_self 0 s.registers).symm
    · rfl

lemma step_correct {w T a b e : ℕ} (s : Data)
    (hW : 2 < wordModulus w) (hT : 0 < T) (hmul : T*T < wordModulus w)
    (ha : a < T) (hb : b < T) (he : e < wordModulus w)
    (h0 : s.registers 0=a) (h1 : s.registers 1=b) (h2 : s.registers 2=T) (h3 : s.registers 3=e) :
    ∃ c, Eval w step s c (nextState T a b e s) ∧ c ≤ 8 := by
  have hTw : T < wordModulus w := by nlinarith
  have hbw : b < wordModulus w := hb.trans hTw
  have hprod : b*b < wordModulus w := (Nat.mul_le_mul hb.le hb.le).trans_lt hmul
  let u:=put s 4 (e%2)
  have eu : Eval w bit s 1 u := by
    apply Eval.atom
    simp [Atom.eval,operand_register,operand_literal,evalBinOp,h3,Nat.mod_eq_of_lt he,Nat.mod_eq_of_lt hW,u]
  obtain ⟨c,v,ev,hc,hv⟩:=conditional_correct (e:=e) u hW hT hmul ha hb
    (by simp [u,put,h0]) (by simp [u,put,h1]) (by simp [u,put,h2]) (by simp [u,put])
  have es : Eval w square v 3 (nextState T a b e s) := by
    rw [hv]
    apply straight_correct
    simp [nextState,u,execStraight,Atom.eval,operand_literal,operand_register,evalBinOp,put,
      h1,h2,h3,Nat.mod_eq_of_lt hbw,Nat.mod_eq_of_lt hprod,Nat.mod_eq_of_lt hTw,
      Nat.mod_eq_of_lt he,Nat.mod_eq_of_lt hW,hT.ne',Function.update_idem]
  exact ⟨1+(c+3),Eval.seq eu (Eval.seq ev es),by omega⟩

lemma nextAcc_lt {T a b e : ℕ} (hT : 0 < T) (ha : a < T) : nextAcc T a b e < T := by
  unfold nextAcc
  split_ifs
  · exact Nat.mod_lt _ hT
  · exact ha

lemma next_cast (T a b e : ℕ) :
    (nextAcc T a b e:ZMod T)*((b*b%T:ℕ):ZMod T)^(e/2)=(a:ZMod T)*(b:ZMod T)^e := by
  have he : e%2+2*(e/2)=e := Nat.mod_add_div ..
  have hbit : e%2=0 ∨ e%2=1 := Nat.mod_two_eq_zero_or_one e
  rcases hbit with h|h
  · have hne : ¬e%2=1 := by omega
    simp only [nextAcc,ite_eq_right hne,ZMod.natCast_mod,Nat.cast_mul]
    conv_rhs => rw [← he,h,zero_add,pow_mul]
    simp [pow_two]
  · simp only [nextAcc,ite_eq_left h,ZMod.natCast_mod,Nat.cast_mul]
    conv_rhs => rw [← he,h,pow_add,pow_mul]
    simp [pow_two,mul_assoc]

theorem loop_correct {w T a b e k : ℕ} (s : Data)
    (hW : 2 < wordModulus w) (hT : 0 < T) (hmul : T*T < wordModulus w)
    (ha : a < T) (hb : b < T) (hew : e < wordModulus w) (hek : e < 2^k)
    (h0 : s.registers 0=a) (h1 : s.registers 1=b) (h2 : s.registers 2=T) (h3 : s.registers 3=e) :
    ∃ cost z, Eval w loop s cost z ∧ cost ≤ 10*k+1 ∧ z.memory=s.memory ∧
      z.registers 0 < T ∧ z.registers 3=0 ∧
      (z.registers 0:ZMod T)=(a:ZMod T)*(b:ZMod T)^e ∧
      (∀ j, j≠0 → j≠1 → j≠3 → j≠4 → z.registers j=s.registers j) := by
  induction k generalizing a b e s with
  | zero =>
    have he : e=0 := by simpa using hek
    have ht : test w s .lt (.literal 0) (.register 3)=false := by
      simp [test,operand_literal,operand_register,evalTest,h3,he]
    exact ⟨1,s,Eval.loopFalse ht,by simp,rfl,by simpa only [h0] using ha,by omega,
      by simp [h0,he],by simp⟩
  | succ k ih =>
    by_cases he : e=0
    · have ht : test w s .lt (.literal 0) (.register 3)=false := by
        simp [test,operand_literal,operand_register,evalTest,h3,he]
      exact ⟨1,s,Eval.loopFalse ht,by omega,rfl,by simpa only [h0] using ha,by omega,
        by simp [h0,he],by simp⟩
    have ht : test w s .lt (.literal 0) (.register 3)=true := by
      simp [test,operand_literal,operand_register,evalTest,h3,Nat.mod_eq_of_lt hew,show 0 < e by omega]
    obtain ⟨c,ec,hc⟩:=step_correct s hW hT hmul ha hb hew h0 h1 h2 h3
    have hehalf : e/2 < 2^k := by rw [Nat.div_lt_iff_lt_mul (by omega : 0 < 2)]; simpa only [pow_succ] using hek
    obtain ⟨cr,z,er,hcr,hmem,haz,hez,hval,hreg⟩:=ih (a:=nextAcc T a b e) (b:=b*b%T) (e:=e/2) (nextState T a b e s)
      (nextAcc_lt (b:=b) (e:=e) hT ha) (Nat.mod_lt _ hT) ((Nat.div_le_self e 2).trans_lt hew) hehalf
      (by simp [nextState,put]) (by simp [nextState,put]) (by simp [nextState,put,h2]) (by simp [nextState,put])
    refine ⟨1+c+1+cr,z,Eval.loopTrue ht ec er,by omega,hmem,haz,hez,hval.trans (next_cast T a b e),?_⟩
    intro j hj0 hj1 hj3 hj4
    rw [hreg j hj0 hj1 hj3 hj4]
    simp [nextState,put,hj0,hj1,hj3,hj4]
end DeterministicThreeSum.Structured.ModularPower
namespace DeterministicThreeSum.Structured.ModularPower
open Command

def inverseSetup (p : ℕ) : Command := straight [
  .assign 0 (.literal 1),.binary 3 .quot (.register 2) (.literal p),
  .binary 3 .sub (.register 2) (.register 3),.binary 3 .sub (.register 3) (.literal 1)]
def inverse (p : ℕ) : Command := .seq (inverseSetup p) loop

lemma prime_power_totient {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p^(k+1)).totient=p^(k+1)-p^(k+1)/p := by
  rw [Nat.totient_prime_pow_succ hp,pow_succ,Nat.mul_div_cancel _ hp.pos]
  rw [Nat.mul_sub_left_distrib,Nat.mul_one]

lemma inverseSetup_correct {w T p : ℕ} (s : Data)
    (hp : 1 < p) (hT : 1 < T) (hTw : T < wordModulus w) (hpw : p < wordModulus w)
    (h2 : s.registers 2=T) :
    Eval w (inverseSetup p) s 4 (put (put s 0 1) 3 (T-T/p-1)) := by
  have hdiv : T/p < T := Nat.div_lt_self (by omega) hp
  have hdw : T/p < wordModulus w := hdiv.trans hTw
  have hd : T-T/p < wordModulus w := (Nat.sub_le ..).trans_lt hTw
  have hew : T-T/p-1 < wordModulus w := (Nat.sub_le ..).trans_lt hd
  have hsub : T+wordModulus w-T/p=(T-T/p)+wordModulus w := by omega
  have hsub' : (T-T/p)+wordModulus w-1=(T-T/p-1)+wordModulus w := by omega
  apply straight_correct
  simp [execStraight,Atom.eval,operand_register,operand_literal,evalBinOp,put,h2,
    Nat.mod_eq_of_lt (show 1 < wordModulus w by omega),Nat.mod_eq_of_lt hTw,
    Nat.mod_eq_of_lt hpw,show p≠0 by omega,Nat.mod_eq_of_lt hdw,hsub,hsub',
    Nat.mod_eq_of_lt hd,Nat.mod_eq_of_lt hew,Function.update_idem]

lemma euler_inverse {T a : ℕ} (hT : 0 < T) (ha : a.Coprime T) :
    (a:ZMod T)^ (T.totient-1)*(a:ZMod T)=1 := by
  have hp : 0 < T.totient := Nat.totient_pos.mpr hT
  have hh := Nat.ModEq.pow_totient ha
  have he : (a:ZMod T)^T.totient=1 := by
    rw [← ZMod.natCast_eq_natCast_iff] at hh
    simpa only [Nat.cast_pow,Nat.cast_one] using hh
  rw [← pow_succ,Nat.sub_add_cancel (by omega : 1 ≤ T.totient)]
  exact he

theorem inverse_correct {w p e a k : ℕ} (s : Data) (hp : p.Prime)
    (hmul : (p^(e+1))*(p^(e+1)) < wordModulus w) (hpw : p < wordModulus w)
    (ha : a < p^(e+1)) (hunit : a.Coprime (p^(e+1))) (hbits : p^(e+1) < 2^k)
    (h1 : s.registers 1=a) (h2 : s.registers 2=p^(e+1)) :
    ∃ cost z, Eval w (inverse p) s cost z ∧ cost ≤ 10*k+5 ∧ z.memory=s.memory ∧
      z.registers 0 < p^(e+1) ∧ (z.registers 0:ZMod (p^(e+1)))*(a:ZMod (p^(e+1)))=1 ∧
      (∀ j, j≠0 → j≠1 → j≠3 → j≠4 → z.registers j=s.registers j) := by
  let T:=p^(e+1)
  have hT : 1 < T := one_lt_pow₀ hp.one_lt (by omega)
  have hTw : T < wordModulus w := by change T*T < wordModulus w at hmul; nlinarith
  have hW : 2 < wordModulus w := by change T*T < wordModulus w at hmul; nlinarith
  let u:=put (put s 0 1) 3 (T-T/p-1)
  have es : Eval w (inverseSetup p) s 4 u := inverseSetup_correct s hp.one_lt hT hTw hpw h2
  have heb : T-T/p-1 < T := by have := Nat.zero_le (T/p); omega
  obtain ⟨c,z,ec,hc,hm,hv,he,heq,hr⟩:=loop_correct (a:=1) (b:=a) (e:=T-T/p-1) u
    hW (by omega) hmul hT ha (heb.trans hTw) (heb.trans hbits)
    (by simp [u,put]) (by simp [u,put,h1]) (by simp [u,put,h2,T]) (by simp [u,put])
  refine ⟨4+c,z,Eval.seq es ec,by omega,hm,hv,?_,?_⟩
  · rw [heq]
    simpa only [Nat.cast_one,one_mul,← prime_power_totient hp e,T] using euler_inverse (by omega : 0 < T) hunit
  · intro j hj0 hj1 hj3 hj4
    rw [hr j hj0 hj1 hj3 hj4]
    simp [u,put,hj0,hj3]
end DeterministicThreeSum.Structured.ModularPower
namespace DeterministicThreeSum.Structured.Indexed
open Command

def integerInverse (p D : ℕ) : Command := .seq (integerCommand (D:ℤ))
  (.seq (.atom (.assign 1 (.register 0))) (ModularPower.inverse p))

lemma integerValue_nat (T D : ℕ) : integerValue T (D:ℤ)=D%T := by simp [integerValue]

lemma coprime_remainder {T D : ℕ} (h : D.Coprime T) : (D%T).Coprime T := by
  change Nat.gcd (D%T) T=1
  rw [← Nat.gcd_rec T D,Nat.gcd_comm]
  exact h

theorem integerInverse_correct {w p e D : ℕ} (s : Data) (hp : p.Prime)
    (hmul : (p^(e+1))*(p^(e+1)) < wordModulus w)
    (hD : D < wordModulus w) (hunit : ¬p∣D) (h2 : s.registers 2=p^(e+1)) :
    ∃ cost z, Eval w (integerInverse p D) s cost z ∧ cost ≤ 10*w+10 ∧
      z.memory=s.memory ∧ z.registers 0 < p^(e+1) ∧
      (z.registers 0:ZMod (p^(e+1)))*(D:ZMod (p^(e+1)))=1 ∧
      (∀ j, j=2 ∨ 5≤j → z.registers j=s.registers j) := by
  let T:=p^(e+1)
  have hT : 0 < T := by exact pow_pos hp.pos _
  have hTw : T < wordModulus w := by change T*T < wordModulus w at hmul; nlinarith
  have hpw : p < wordModulus w := (Nat.le_pow (by omega)).trans_lt hTw
  obtain ⟨c,he,hc⟩:=integerCommand_correct s (D:ℤ) hT hTw (by simpa using hD) h2
  rw [integerValue_nat] at he
  let u:=put s 0 (D%T)
  let v:=put u 1 (D%T)
  have he1 : Eval w (.atom (.assign 1 (.register 0))) u 1 v := by
    simpa [u,v,operand_register,put,Nat.mod_eq_of_lt ((Nat.mod_lt D hT).trans hTw)] using eval_assign (w:=w) u 1 (.register 0)
  have hDT : D.Coprime T := (hp.coprime_iff_not_dvd.mpr hunit).symm.pow_right (e+1)
  obtain ⟨cr,z,her,hcr,hm,hv,hinv,hf⟩ := ModularPower.inverse_correct (w:=w) (p:=p) (e:=e) (a:=D%T) (k:=w) v hp hmul hpw
    (Nat.mod_lt D hT) (coprime_remainder hDT) hTw (by simp [v,put]) (by simp [v,u,put,h2,T])
  refine ⟨c+(1+cr),z,Eval.seq he (Eval.seq he1 her),by omega,hm,hv,?_,?_⟩
  · simpa only [ZMod.natCast_mod] using hinv
  · intro j hj
    rw [hf j (by omega) (by omega) (by omega) (by omega)]
    simp [v,u,put,show j≠0 by omega,show j≠1 by omega]
end DeterministicThreeSum.Structured.Indexed
namespace DeterministicThreeSum.Structured.Indexed
open Command

def scaledTable (i : ℕ) : List ℤ → Command
  | [] => .skip
  | a::rest => .seq (integerCommand a) (.seq (.atom (.assign 1 (.register 5)))
      (.seq Modular.mul (.seq (straight [.binary 1 .add (.register 3) (.literal i),
        .store (.register 1) (.register 0)]) (scaledTable (i+1) rest))))

def scaledMemory (T scale base i : ℕ) : List ℤ → (ℕ → Option ℕ) → (ℕ → Option ℕ)
  | [],mem => mem
  | a::rest,mem => scaledMemory T scale base (i+1) rest
      (Function.update mem (base+i) (some ((integerValue T a*scale)%T)))

theorem scaledTable_correct {w T scale base i : ℕ} (s : Data) (xs : List ℤ)
    (hT : 0 < T) (hmul : T*T < wordModulus w) (hscale : scale < T)
    (hbase : base+i+xs.length < wordModulus w) (ha : ∀ a∈xs, a.natAbs < wordModulus w)
    (h2 : s.registers 2=T) (h3 : s.registers 3=base) (h5 : s.registers 5=scale) :
    ∃ cost z, Eval w (scaledTable i xs) s cost z ∧ cost ≤ 9*xs.length ∧
      z.memory=scaledMemory T scale base i xs s.memory ∧
      (∀ r, 2≤r → z.registers r=s.registers r) := by
  have hTw : T < wordModulus w := by nlinarith
  have hscaleW : scale < wordModulus w := hscale.trans hTw
  induction xs generalizing s i with
  | nil => exact ⟨0,s,Eval.skip s,by simp,rfl,by simp⟩
  | cons a xs ih =>
    obtain ⟨c,he,hc⟩:=integerCommand_correct s a hT hTw (ha a (by simp)) h2
    let u:=put s 0 (integerValue T a)
    let v:=put u 1 scale
    have he1 : Eval w (.atom (.assign 1 (.register 5))) u 1 v := by
      simpa [u,v,put,operand_register,h5,Nat.mod_eq_of_lt hscaleW] using eval_assign (w:=w) u 1 (.register 5)
    have he2:=Modular.mul_correct v hT hmul (integerValue_lt hT a) hscale
      (by simp [v,u,put]) (by simp [v,put]) (by simp [v,u,put,h2])
    let vv:=put v 0 (integerValue T a*scale%T)
    let z0:Data:={put vv 1 (base+i) with memory:=Function.update s.memory (base+i) (some (integerValue T a*scale%T))}
    have haddress : base+i < wordModulus w := by simp only [List.length_cons] at hbase; omega
    have he3 : Eval w (straight [.binary 1 .add (.register 3) (.literal i),.store (.register 1) (.register 0)]) vv 2 z0 := by
      apply straight_correct
      simp [execStraight,Atom.eval,evalBinOp,operand_register,operand_literal,z0,vv,v,u,put,h3,
        Nat.mod_eq_of_lt haddress,Nat.mod_eq_of_lt (show base < wordModulus w by omega),
        Nat.mod_eq_of_lt (show i < wordModulus w by omega),
        Nat.mod_eq_of_lt ((Nat.mod_lt _ hT).trans hTw)]
    obtain ⟨cr,z,her,hcr,hmr,hfr⟩:=ih (i:=i+1) z0 (by simp only [List.length_cons] at hbase; omega)
      (fun a ha' => ha a (by simp [ha'])) (by simp [z0,vv,v,u,put,h2])
      (by simp [z0,vv,v,u,put,h3]) (by simp [z0,vv,v,u,put,h5])
    refine ⟨c+(1+(2+(2+cr))),z,Eval.seq he (Eval.seq he1 (Eval.seq he2 (Eval.seq he3 her))),by simp only [List.length_cons]; omega,?_,?_⟩
    · exact hmr
    · intro r hr
      rw [hfr r hr]
      simp [z0,vv,v,u,put,show r≠0 by omega,show r≠1 by omega]

lemma scaledMemory_outside (T scale base i : ℕ) (xs : List ℤ) (mem : ℕ → Option ℕ) (a : ℕ)
    (ha : a<base+i ∨ base+i+xs.length≤a) : scaledMemory T scale base i xs mem a=mem a := by
  induction xs generalizing i mem with
  | nil => rfl
  | cons b xs ih =>
    rw [scaledMemory,ih (i+1) _ (by simp only [List.length_cons] at ha; omega)]
    exact Function.update_of_ne (by simp only [List.length_cons] at ha; omega) _ _

lemma scaledMemory_entry (T scale base i : ℕ) (xs : List ℤ) (mem : ℕ → Option ℕ) (j : ℕ) (hj : j<xs.length) :
    scaledMemory T scale base i xs mem (base+i+j)=some (integerValue T xs[j]*scale%T) := by
  induction xs generalizing i mem j with
  | nil => simp at hj
  | cons b xs ih =>
    cases j with
    | zero =>
      simp only [scaledMemory,List.getElem_cons_zero,Nat.add_zero]
      rw [scaledMemory_outside (ha:=Or.inl (by omega))]
      simp
    | succ j =>
      simpa only [scaledMemory,List.getElem_cons_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
        ih (i+1) (Function.update mem (base+i) (some (integerValue T b*scale%T))) j (by simpa using hj)

lemma scaled_cast {T scale : ℕ} (hT : 0 < T) (a : ℤ) :
    ((integerValue T a*scale%T:ℕ):ZMod T)=(a:ZMod T)*(scale:ZMod T) := by
  rw [ZMod.natCast_mod,Nat.cast_mul,integerValue_cast hT]
end DeterministicThreeSum.Structured.Indexed
namespace DeterministicThreeSum.Structured.Indexed
open Command

def commonTable (p D : ℕ) (xs : List ℤ) : Command :=
  .seq (.atom (.assign 6 (.register 3))) (.seq (integerInverse p D)
    (.seq (straight [.assign 5 (.register 0),.assign 3 (.register 6)]) (scaledTable 0 xs)))

theorem commonTable_correct {w p e D base : ℕ} (s : Data) (xs : List ℤ) (hp : p.Prime)
    (hmul : (p^(e+1))*(p^(e+1)) < wordModulus w) (hD : D < wordModulus w)
    (hunit : ¬p∣D) (hbase : base+xs.length < wordModulus w)
    (hints : ∀ a∈xs, a.natAbs < wordModulus w)
    (h2 : s.registers 2=p^(e+1)) (h3 : s.registers 3=base) :
    ∃ cost z, Eval w (commonTable p D xs) s cost z ∧ cost ≤ 10*w+13+9*xs.length ∧
      (∀ i (hi : i < xs.length), ∃ v, z.memory (base+i)=some v ∧ v < p^(e+1) ∧
        (v:ZMod (p^(e+1)))*(D:ZMod (p^(e+1)))=(xs[i]:ZMod (p^(e+1)))) ∧
      (∀ a, a < base ∨ base+xs.length ≤ a → z.memory a=s.memory a) ∧
      (∀ r, r=2 ∨ r=3 ∨ 7≤r → z.registers r=s.registers r) := by
  let T:=p^(e+1)
  have hT : 0 < T := by exact pow_pos hp.pos _
  have hTw : T < wordModulus w := by change T*T < wordModulus w at hmul; nlinarith
  let u:=put s 6 base
  have he0 : Eval w (.atom (.assign 6 (.register 3))) s 1 u := by
    simpa [u,operand_register,h3,Nat.mod_eq_of_lt (show base < wordModulus w by omega)] using eval_assign (w:=w) s 6 (.register 3)
  obtain ⟨c,v,he,hc,hm,hv,hinv,hf⟩:=integerInverse_correct (p:=p) (e:=e) (D:=D) u hp hmul hD hunit (by simp [u,put,h2])
  have hv6 : v.registers 6=base := by simpa [u,put] using hf 6 (by omega)
  have hv2 : v.registers 2=T := by simpa [u,put,h2,T] using hf 2 (by omega)
  let z0:=put (put v 5 (v.registers 0)) 3 base
  have he1 : Eval w (straight [.assign 5 (.register 0),.assign 3 (.register 6)]) v 2 z0 := by
    apply straight_correct
    simp [z0,execStraight,Atom.eval,operand_register,put,hv6,Nat.mod_eq_of_lt (hv.trans hTw),Nat.mod_eq_of_lt (show base < wordModulus w by omega)]
  obtain ⟨cr,z,her,hcr,hmr,hfr⟩:=scaledTable_correct (T:=T) (scale:=v.registers 0) (base:=base) (i:=0) z0 xs hT hmul hv
    (by simpa only [Nat.add_zero] using hbase) hints (by simp [z0,put,hv2]) (by simp [z0,put]) (by simp [z0,put])
  refine ⟨1+(c+(2+cr)),z,Eval.seq he0 (Eval.seq he (Eval.seq he1 her)),by omega,?_,?_,?_⟩
  · intro i hi
    refine ⟨integerValue T xs[i]*v.registers 0%T,?_,Nat.mod_lt _ hT,?_⟩
    · rw [hmr]
      simpa only [Nat.add_zero] using scaledMemory_entry T (v.registers 0) base 0 xs z0.memory i hi
    · rw [scaled_cast hT,mul_assoc,hinv,mul_one]
  · intro a ha
    rw [hmr,scaledMemory_outside (ha:=by simpa only [Nat.add_zero] using ha)]
    exact congrFun hm a
  · intro r hr
    rw [hfr r (by omega)]
    by_cases hreq : r=3
    · subst r; simp [z0,put,h3]
    have hr5 : r≠5 := by omega
    simp only [z0,put,Function.update_of_ne hreq,Function.update_of_ne hr5]
    rw [hf r (by omega)]
    simp [u,put,show r≠6 by omega]
end DeterministicThreeSum.Structured.Indexed

end OAI
