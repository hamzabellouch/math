import Mathlib
import OAI.Computability.DeterministicSum.Structured

namespace OAI

/-! Signed word encoding, no-wrap bounds and modular arithmetic commands. -/

namespace DeterministicThreeSum

lemma wordModulus_pos (w : ℕ) : 0<wordModulus w := by unfold wordModulus; positivity

lemma encodeWord_lt (w : ℕ) (a : ℤ) : encodeWord w a<wordModulus w := by
  have hp : (0:ℤ)<wordModulus w := by exact_mod_cast wordModulus_pos w
  have hn := Int.emod_nonneg a hp.ne'
  have hl := Int.emod_lt_of_pos a hp
  unfold encodeWord
  omega

lemma encodeWord_add (w : ℕ) (a b : ℤ) :
    encodeWord w (a+b)=(encodeWord w a+encodeWord w b)%wordModulus w := by
  have hp : (0:ℤ)<wordModulus w := by exact_mod_cast wordModulus_pos w
  have hn := Int.emod_nonneg a hp.ne'
  have hn' := Int.emod_nonneg b hp.ne'
  unfold encodeWord
  rw [Int.add_emod]
  rw [Int.toNat_emod (add_nonneg hn hn') hp.le, Int.toNat_add hn hn']
  simp

lemma encodeWord_eq_zero_iff {w : ℕ} {a : ℤ} (ha : |a|<(wordModulus w:ℤ)) :
    encodeWord w a=0 ↔ a=0 := by
  have hp : (0:ℤ)<wordModulus w := by exact_mod_cast wordModulus_pos w
  constructor
  · intro he
    have he' : a%(wordModulus w:ℤ)=0 := by
      have hn := Int.emod_nonneg a hp.ne'
      unfold encodeWord at he
      omega
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (Int.dvd_of_emod_eq_zero he')
    have hh : (Int.natAbs a:ℤ)<Int.natAbs (wordModulus w:ℤ) := by
      simpa only [Int.natCast_natAbs,abs_of_pos hp] using ha
    exact_mod_cast hh
  · rintro rfl; simp [encodeWord]

lemma wordWidth_lower (factor n : ℕ) (_hn : 1≤n+2) :
    (n+2)^factor≤wordModulus (wordWidth factor n) := by
  have hx : (0:ℝ)<n+2 := by positivity
  have hb : (1:ℝ)<2 := by norm_num
  have hceil := Nat.le_ceil ((factor:ℝ)*Real.logb 2 (n+2))
  have he := Real.rpow_le_rpow_of_exponent_le hb.le hceil
  have hid : (2:ℝ)^((factor:ℝ)*Real.logb 2 (n+2))=(n+2:ℝ)^factor := by
    rw [mul_comm,Real.rpow_mul (by norm_num),Real.rpow_logb (by norm_num) (by norm_num) hx]
    rw [Real.rpow_natCast]
  rw [hid,Real.rpow_natCast] at he
  unfold wordWidth wordModulus
  exact_mod_cast he

lemma cubic_sum_no_wrap {n w : ℕ} (hn : 3≤n) (hw : (n+2)^4≤wordModulus w)
    (a b c : ℤ) (ha : |a|≤(n:ℤ)^3) (hb : |b|≤(n:ℤ)^3) (hc : |c|≤(n:ℤ)^3) :
    |a+b+c|<(wordModulus w:ℤ) := by
  have hn' : (3:ℤ)≤n := by exact_mod_cast hn
  have hw' : ((n:ℤ)+2)^4≤wordModulus w := by exact_mod_cast hw
  have ht : 3*(n:ℤ)^3<((n:ℤ)+2)^4 := by nlinarith [sq_nonneg (n:ℤ),sq_nonneg ((n:ℤ)^2)]
  have htri := abs_add_le (a+b) c
  have htri' := abs_add_le a b
  linarith

lemma polynomial_sum_no_wrap {n C w : ℕ} (hn : 3≤n) (_hC : 0<C)
    (hw : (n+2)^(C+4)≤wordModulus w)
    (a b c : ℤ) (ha : |a|≤(n:ℤ)^C) (hb : |b|≤(n:ℤ)^C) (hc : |c|≤(n:ℤ)^C) :
    |a+b+c|<(wordModulus w:ℤ) := by
  have hn' : (3:ℤ)≤n := by exact_mod_cast hn
  have hw' : ((n:ℤ)+2)^(C+4)≤wordModulus w := by exact_mod_cast hw
  have hpow : (n:ℤ)^C≤((n:ℤ)+2)^C := pow_le_pow_left₀ (by omega) (by omega) C
  have hp : (0:ℤ)<((n:ℤ)+2)^C := pow_pos (by omega) _
  have hfour : (3:ℤ)<((n:ℤ)+2)^4 := by
    have hbound : (5:ℤ)^4≤((n:ℤ)+2)^4 := pow_le_pow_left₀ (by norm_num) (by omega) 4
    norm_num at hbound ⊢
    omega
  have ht : 3*(n:ℤ)^C<((n:ℤ)+2)^(C+4) := by rw [pow_add]; nlinarith
  have htri := abs_add_le (a+b) c
  have htri' := abs_add_le a b
  linarith

end DeterministicThreeSum
namespace DeterministicThreeSum.Structured
open Command

def straight : List Atom → Command
  | [] => .skip
  | a::as => .seq (.atom a) (straight as)

def execStraight (w : ℕ) : List Atom → Data → Option Data
  | [],s => some s
  | a::as,s => (a.eval w s).bind (execStraight w as)

lemma straight_correct {w : ℕ} {as : List Atom} {s t : Data}
    (he : execStraight w as s=some t) : Eval w (straight as) s as.length t := by
  induction as generalizing s with
  | nil => simp only [execStraight,Option.some.injEq] at he; subst t; exact Eval.skip s
  | cons a as ih =>
    obtain ⟨u,ha,hu⟩ := Option.bind_eq_some_iff.mp he
    simpa only [straight,List.length_cons,Nat.add_comm] using Eval.seq (Eval.atom ha) (ih hu)

lemma straight_writes (as : List Atom) : (straight as).writes=as.foldr (fun a S => a.writes∪S) ∅ := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [straight,Command.writes,List.foldr_cons,ih]

lemma eval_add {w r a b : ℕ} (s : Data)
    (_ha : a<wordModulus w) (_hb : b<wordModulus w) (hsum : a+b<wordModulus w)
    (u v : Operand) (hu : operand w s u=a) (hv : operand w s v=b) :
    Eval w (.atom (.binary r .add u v)) s 1 (put s r (a+b)) := by
  apply Eval.atom
  simp [Atom.eval,hu,hv,evalBinOp,Nat.mod_eq_of_lt hsum]

lemma eval_remainder {w r a b : ℕ} (s : Data) (hb : 0<b)
    (u v : Operand) (hu : operand w s u=a) (hv : operand w s v=b) :
    Eval w (.atom (.binary r .rem u v)) s 1 (put s r (a%b)) := by
  apply Eval.atom
  simp [Atom.eval,hu,hv,evalBinOp,hb.ne']

lemma eval_indirect_load {w r a v : ℕ} (s : Data) (u : Operand)
    (hu : operand w s u=a) (hv : s.memory a=some v) :
    Eval w (.atom (.load r u)) s 1 (put s r v) := by
  apply Eval.atom
  simp [Atom.eval,hu,hv]

lemma eval_indirect_store {w a v : ℕ} (s : Data) (u z : Operand)
    (hu : operand w s u=a) (hz : operand w s z=v) :
    Eval w (.atom (.store u z)) s 1 {s with memory:=Function.update s.memory a (some v)} := by
  apply Eval.atom
  simp [Atom.eval,hu,hz]

end DeterministicThreeSum.Structured
namespace DeterministicThreeSum.Structured.Modular
open Command

def add : Command := straight [.binary 0 .add (.register 0) (.register 1),
  .binary 0 .rem (.register 0) (.register 2)]
def mul : Command := straight [.binary 0 .mul (.register 0) (.register 1),
  .binary 0 .rem (.register 0) (.register 2)]
def sub : Command := straight [.binary 0 .add (.register 0) (.register 2),
  .binary 0 .sub (.register 0) (.register 1),
  .binary 0 .rem (.register 0) (.register 2)]

lemma add_correct {w T a b : ℕ} (s : Data) (hT : 0<T)
    (hw : 2*T<wordModulus w) (ha : a<T) (hb : b<T)
    (h0 : s.registers 0=a) (h1 : s.registers 1=b) (h2 : s.registers 2=T) :
    Eval w add s 2 (put s 0 ((a+b)%T)) := by
  apply straight_correct
  simp [execStraight,Atom.eval,evalBinOp,operand_register,put,h0,h1,h2,
    Nat.mod_eq_of_lt (show a<wordModulus w by omega),
    Nat.mod_eq_of_lt (show b<wordModulus w by omega),
    Nat.mod_eq_of_lt (show a+b<wordModulus w by omega),
    Nat.mod_eq_of_lt (show T<wordModulus w by omega),hT.ne',Function.update_idem]

lemma mul_correct {w T a b : ℕ} (s : Data) (hT : 0<T)
    (hw : T*T<wordModulus w) (ha : a<T) (hb : b<T)
    (h0 : s.registers 0=a) (h1 : s.registers 1=b) (h2 : s.registers 2=T) :
    Eval w mul s 2 (put s 0 ((a*b)%T)) := by
  have hT' : T<wordModulus w := by nlinarith
  have hp : a*b<wordModulus w := lt_of_le_of_lt (Nat.mul_le_mul ha.le hb.le) hw
  apply straight_correct
  simp [execStraight,Atom.eval,evalBinOp,operand_register,put,h0,h1,h2,
    Nat.mod_eq_of_lt (show a<wordModulus w by omega),
    Nat.mod_eq_of_lt (show b<wordModulus w by omega),
    Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt hT',hT.ne',Function.update_idem]

lemma sub_correct {w T a b : ℕ} (s : Data) (hT : 0<T)
    (hw : 2*T<wordModulus w) (ha : a<T) (hb : b<T)
    (h0 : s.registers 0=a) (h1 : s.registers 1=b) (h2 : s.registers 2=T) :
    Eval w sub s 3 (put s 0 ((a+T-b)%T)) := by
  have hs : (a+T+wordModulus w-b)%wordModulus w=a+T-b := by
    rw [show a+T+wordModulus w-b=(a+T-b)+wordModulus w by omega]
    simp [Nat.mod_eq_of_lt (show a+T-b<wordModulus w by omega)]
  apply straight_correct
  simp [execStraight,Atom.eval,evalBinOp,operand_register,put,h0,h1,h2,
    Nat.mod_eq_of_lt (show a<wordModulus w by omega),
    Nat.mod_eq_of_lt (show b<wordModulus w by omega),
    Nat.mod_eq_of_lt (show a+T<wordModulus w by omega),
    Nat.mod_eq_of_lt (show T<wordModulus w by omega),hT.ne',hs,Function.update_idem]

lemma cast_add (T a b : ℕ) : (((a+b)%T:ℕ):ZMod T)=(a:ZMod T)+(b:ZMod T) := by
  simp
lemma cast_mul (T a b : ℕ) : (((a*b)%T:ℕ):ZMod T)=(a:ZMod T)*(b:ZMod T) := by
  simp
lemma cast_sub {T a b : ℕ} (hb : b<T) :
    (((a+T-b)%T:ℕ):ZMod T)=(a:ZMod T)-(b:ZMod T) := by
  rw [ZMod.natCast_mod,Nat.cast_sub (by omega : b≤a+T)]
  simp

def mac : Command := .seq mul (.seq (.atom (.assign 1 (.register 3)))
  (.seq add (.atom (.assign 3 (.register 0)))))

lemma mac_correct {w T a b acc : ℕ} (s : Data) (hT : 0<T)
    (hadd : 2*T<wordModulus w) (hmul : T*T<wordModulus w)
    (ha : a<T) (hb : b<T) (hc : acc<T)
    (h0 : s.registers 0=a) (h1 : s.registers 1=b)
    (h2 : s.registers 2=T) (h3 : s.registers 3=acc) :
    ∃ t, Eval w mac s 6 t ∧ t.memory=s.memory ∧
      t.registers 3=(acc+a*b)%T ∧
      (∀ r, r≠0 → r≠1 → r≠3 → t.registers r=s.registers r) := by
  let u:=put s 0 ((a*b)%T)
  let v:=put u 1 acc
  let z:=put v 0 (((a*b)%T+acc)%T)
  let t:=put z 3 (((a*b)%T+acc)%T)
  have hu : Eval w mul s 2 u := mul_correct s hT hmul ha hb h0 h1 h2
  have hv : Eval w (.atom (.assign 1 (.register 3))) u 1 v := by
    apply Eval.atom
    simp [Atom.eval,operand_register,put,u,v,h3,Nat.mod_eq_of_lt (show acc<wordModulus w by omega)]
  have hz : Eval w add v 2 z := add_correct v hT hadd (Nat.mod_lt _ hT) hc
    (by simp [v,u,put]) (by simp [v,put]) (by simp [v,u,put,h2])
  have ht : Eval w (.atom (.assign 3 (.register 0))) z 1 t := by
    apply Eval.atom
    simp [Atom.eval,operand_register,put,z,t,Nat.mod_eq_of_lt
      (show (a*b+acc)%T<wordModulus w by have:=Nat.mod_lt (a*b+acc) hT;omega)]
  refine ⟨t,?_,rfl,?_,?_⟩
  · exact Eval.seq hu (Eval.seq hv (Eval.seq hz ht))
  · simp [t,put,Nat.add_mod,Nat.add_comm]
  · intro r hr0 hr1 hr3
    simp [t,z,v,u,put,hr0,hr1,hr3]

end DeterministicThreeSum.Structured.Modular

end OAI
