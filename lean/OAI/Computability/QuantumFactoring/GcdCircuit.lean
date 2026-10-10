import Mathlib
import OAI.Computability.QuantumFactoring.StaticPredicates
import OAI.Computability.QuantumFactoring.RootCircuit
import OAI.Computability.QuantumFactoring.ContinuedFractionRecovery

namespace OAI

section
open scoped BigOperators


/-! Clocked Euclidean arithmetic, including zero operands.  The clock is
linear in bit width, and every step is an actual Boolean modular divider. -/
namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

def euclidRun : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0,a,b => (a,b)
  | k+1,a,b => if b=0 then (a,0) else euclidRun k b (a%b)

lemma euclidRun_zero (k a : ℕ) : euclidRun k a 0=(a,0) := by
  cases k <;> simp [euclidRun]

lemma euclidRun_terminal (s a b h : ℕ) (hb : b < 2^s) :
    euclidRun (2*s+h) a b=(Nat.gcd a b,0) := by
  induction s generalizing a b h with
  | zero =>
    have : b=0 := by simpa using hb
    subst b
    simp [euclidRun_zero]
  | succ s ih =>
    by_cases hb0 : b=0
    · subst b; simp [euclidRun_zero]
    have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
    have he : 2*(s+1)+h=(2*s+h+1)+1 := by omega
    by_cases hr0 : a%b=0
    · rw [he,euclidRun,ite_eq_right hb0,hr0,euclidRun_zero]
      rw [Nat.gcd_comm a b,Nat.gcd_rec b a,hr0,Nat.gcd_zero_left]
    · have hr := Nat.pos_of_ne_zero hr0
      have hh := OrderTrial.euclid_two_halving hr (Nat.mod_lt a hbpos)
      have hb' : b%(a%b) < 2^s := by rw [pow_succ] at hb; omega
      rw [he,euclidRun,ite_eq_right hb0,euclidRun,ite_eq_right hr0,ih _ _ h hb']
      congr 1
      calc
        Nat.gcd (a%b) (b%(a%b)) = Nat.gcd b (a%b) := by
          rw [Nat.gcd_comm (a%b) (b%(a%b)),← Nat.gcd_rec (a%b) b,Nat.gcd_comm]
        _ = Nat.gcd a b := by rw [Nat.gcd_comm b (a%b),← Nat.gcd_rec b a,Nat.gcd_comm]

def euclidStep (w : ℕ) : BooleanNetwork (w+w) (w+w) :=
  let z := wordConstant (BitVec.ofNat w 0)
  let done := equalOn (rootGuess w) z
  (wordMux done (rootModulus w) (rootGuess w)).pair
    (wordMux done z (mod w))

def euclidPrefix (w : ℕ) : ℕ → BooleanNetwork (w+w) (w+w)
  | 0 => select id
  | k+1 => (euclidStep w).comp (euclidPrefix w k)

def gcdNet (w : ℕ) : BooleanNetwork (w+w) w :=
  (euclidPrefix w (2*w)).comp (rootModulus w)

lemma euclidStep_semantics (w : ℕ) (a b : Basis w) :
    ∃ a' b' : Basis w,
      (euclidStep w).eval (Fin.append a b)=Fin.append a' b' ∧
      (bitsValue a').toNat=(if (bitsValue b).toNat=0 then (bitsValue a).toNat else (bitsValue b).toNat) ∧
      (bitsValue b').toNat=(if (bitsValue b).toNat=0 then 0 else (bitsValue a).toNat%(bitsValue b).toNat) := by
  let z := (wordConstant (n:=w+w) (BitVec.ofNat w 0)).eval (Fin.append a b)
  have hz : (bitsValue z).toNat=0 := by simp [z,wordConstant_eval]
  have hc : (equalOn (rootGuess w) (wordConstant (BitVec.ofNat w 0))).eval (Fin.append a b) 0=true ↔
      (bitsValue b).toNat=0 := by
    rw [equalOn_value,rootGuess_eval,wordConstant_eval]
    simp
  by_cases hb : (bitsValue b).toNat=0
  · refine ⟨a,z,?_,by simp [hb],by simpa [hb] using hz⟩
    rw [euclidStep,eval_pair,wordMux_eval,wordMux_eval,ite_eq_left (hc.mpr hb),ite_eq_left (hc.mpr hb),rootModulus_eval]
  · refine ⟨b,(mod w).eval (Fin.append a b),?_,by simp [hb],?_⟩
    · rw [euclidStep,eval_pair,wordMux_eval,wordMux_eval,ite_eq_right (fun condition => hb (hc.mp condition)),ite_eq_right (fun condition => hb (hc.mp condition)),rootGuess_eval]
    · rw [mod_word,BitVec.toNat_umod,ite_eq_right hb]

lemma euclidPrefix_semantics (w k : ℕ) (a b : Basis w) :
    ∃ a' b' : Basis w,
      (euclidPrefix w k).eval (Fin.append a b)=Fin.append a' b' ∧
      ((bitsValue a').toNat,(bitsValue b').toNat)=euclidRun k (bitsValue a).toNat (bitsValue b).toNat := by
  induction k generalizing a b with
  | zero => exact ⟨a,b,rfl,rfl⟩
  | succ k ih =>
    obtain ⟨a₁,b₁,he,ha,hb⟩ := euclidStep_semantics w a b
    obtain ⟨a',b',he',hv⟩ := ih a₁ b₁
    refine ⟨a',b',by rw [euclidPrefix,eval_comp,he,he'],?_⟩
    rw [hv,ha,hb,euclidRun]
    split_ifs with hb0
    · exact euclidRun_zero k _
    · rfl

lemma gcdNet_value (w : ℕ) (a b : Basis w) :
    (bitsValue ((gcdNet w).eval (Fin.append a b))).toNat=
      Nat.gcd (bitsValue a).toNat (bitsValue b).toNat := by
  obtain ⟨a',b',he,hv⟩ := euclidPrefix_semantics w (2*w) a b
  have ht := euclidRun_terminal w (bitsValue a).toNat (bitsValue b).toNat 0 (bitsValue b).isLt
  rw [Nat.add_zero] at ht
  rw [ht] at hv
  rw [gcdNet,eval_comp,he,rootModulus_eval]
  exact congrArg Prod.fst hv

lemma euclidStep_count (w : ℕ) : (euclidStep w).net.count ≤ 216*w*w+300*w+100 := by
  have hc := equalOn_count (rootGuess w) (wordConstant (n:=w+w) (BitVec.ofNat w 0))
  simp only [rootGuess,count_select,wordConstant_count,zero_add] at hc
  have hm := mod_count w
  simp only [euclidStep,count_pair,wordMux_count,rootModulus,rootGuess,count_select,wordConstant_count]
  omega

lemma euclidPrefix_count (w k : ℕ) :
    (euclidPrefix w k).net.count ≤ k*(216*w*w+300*w+100) := by
  induction k with
  | zero => simp [euclidPrefix]
  | succ k ih =>
    rw [euclidPrefix,count_comp]
    have := euclidStep_count w
    rw [Nat.succ_mul]
    omega

lemma gcdNet_count (w : ℕ) : (gcdNet w).net.count ≤ 2*w*(216*w*w+300*w+100) := by
  simpa only [gcdNet,count_comp,rootModulus,count_select,add_zero] using euclidPrefix_count w (2*w)

end ExactQuantumFactoring.BitArithmetic


end

end OAI
