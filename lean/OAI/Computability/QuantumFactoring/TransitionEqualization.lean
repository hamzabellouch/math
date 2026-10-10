import Mathlib
import OAI.Computability.QuantumFactoring.DyadicCompletion
import OAI.Computability.QuantumFactoring.ListTransition
import OAI.Computability.QuantumFactoring.OrderTransition

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials OrderTrial

lemma OrderTrial.DyadicAt.pow {d : ℕ} {x : ℚ} (h : DyadicAt d x) (k : ℕ) :
    DyadicAt (d*k) (x^k) := by
  induction k with
  | zero => simpa using DyadicAt.integer 0 1
  | succ k ih =>
    simpa only [pow_succ,Nat.mul_succ] using ih.mul h

namespace Completion

def target (n : ℕ) : ℚ := 1-1/(2:ℚ)^n
def transitionWidth (n : ℕ) : ℕ := n*(n^5+1)
def listSuccess (m n K : ℕ) : ℚ :=
  1-(1-(favorableCount m n : ℚ)/(2:ℚ)^(Nat.clog 2 m))^K
def orderSuccess (d K : ℕ) : ℚ :=
  1-(1-(Nat.totient d:ℚ)*prescribedMass d)^K

lemma target_at (n : ℕ) : DyadicAt n (target n) :=
  (DyadicAt.integer n 1).sub ⟨1,by simp⟩

lemma listSuccess_at {m n : ℕ} (hb : m ≤ 2^n) (K : ℕ) :
    DyadicAt (n*K) (listSuccess m n K) := by
  have hx : DyadicAt n ((favorableCount m n:ℚ)/(2:ℚ)^(Nat.clog 2 m)) :=
    (show DyadicAt (Nat.clog 2 m) _ from ⟨favorableCount m n,by simp⟩).mono
      (Nat.clog_le_of_le_pow hb)
  exact (DyadicAt.integer (n*K) 1).sub (((DyadicAt.integer n 1).sub hx).pow K)

lemma orderSuccess_at {n d : ℕ} (hd : d ≤ 2^n) (K : ℕ) :
    DyadicAt ((n+10)*K) (orderSuccess d K) := by
  have hx : DyadicAt (n+10) ((Nat.totient d:ℚ)*prescribedMass d) := by
    exact_mod_cast (lambda_at hd).int_mul (Nat.totient d)
  exact (DyadicAt.integer ((n+10)*K) 1).sub (((DyadicAt.integer (n+10) 1).sub hx).pow K)

lemma target_pos {n : ℕ} (hn : 1 ≤ n) : 0<target n := by
  have hp : (1:ℚ)<2^n := one_lt_pow₀ (by norm_num) (by omega)
  unfold target
  have hh := (div_lt_one (by positivity : (0:ℚ)<2^n)).mpr hp
  linarith

/-- The source repetition bound suffices for the unchanged equalization target.
No high-probability event is being declared to have probability one. -/
lemma target_le_ordinary {n : ℕ} (hn : 1 ≤ n) {s : ℚ}
    (hs : 1-1/(2:ℚ)^(2*n) ≤ s) :
    target n ≤ (1-1/(2:ℚ)^(2*n))*s := by
  have hp : (2:ℚ) ≤ 2^n := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 2) hn)
  have hpp : (0:ℚ)<2^n := by positivity
  have he : (2:ℚ)^(2*n)=(2^n)^2 := by rw [Nat.mul_comm 2 n,pow_mul]
  have hu : 0 ≤ 1/(2:ℚ)^n := by positivity
  have hl : 1/(2:ℚ)^n ≤ 1/2 := by exact one_div_le_one_div_of_le (by norm_num) hp
  have hδ : 1/(2:ℚ)^(2*n)=(1/(2:ℚ)^n)^2 := by rw [he,div_pow,one_pow]
  have hfactor : 0 ≤ 1-1/(2:ℚ)^(2*n) := by rw [hδ]; nlinarith
  have hh := mul_le_mul_of_nonneg_left hs hfactor
  unfold target
  rw [hδ] at hh ⊢
  nlinarith [sq_nonneg ((1/(2:ℚ)^n)^2)]

lemma listSuccess_lower {m n : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hb : m<2^n)
    (hodd : Odd m) (p₀ p₁ : Component m) (hne : p₁≠p₀) :
    1-1/(2:ℚ)^(2*n) ≤ listSuccess m n (n^5) := by
  have hh := list_good_lower hn hm hb hodd p₀ p₁ hne
  rw [list_good_mass _ hb hodd p₀] at hh
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [listSuccess,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_pow,
    Rat.cast_ofNat,Rat.cast_natCast] using hh

lemma listSuccess_le_one {m n : ℕ} (hm : m≠0) (hb : m<2^n)
    (hodd : Odd m) (p₀ : Component m) (K : ℕ) : listSuccess m n K ≤ 1 := by
  have hh := (mass_bounds (tensorState (fairState (Nat.clog 2 m)) K)
    (GoodList hm hb p₀ K) (tensor_normalized _ K (fairState_normalized _))).2
  rw [list_good_mass hm hb hodd p₀] at hh
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [listSuccess,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_pow,
    Rat.cast_ofNat,Rat.cast_natCast] using hh

lemma orderSuccess_lower {w n s : ℕ} (hn : 128 ≤ n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2 ≤ (bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) : 1-1/(2:ℚ)^(2*n) ≤ orderSuccess (orderOf u) (n^5) := by
  have hh := orderResult_lower hn hs a m hm u ha hdB
  rw [orderResult_mass (by omega) hs a m hm u ha hdB] at hh
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [orderSuccess,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_pow,
    Rat.cast_ofNat,Rat.cast_mul,Rat.cast_natCast] using hh

lemma orderSuccess_le_one {w n s : ℕ} (hn : 1 ≤ n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2 ≤ (bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) (K : ℕ) : orderSuccess (orderOf u) K ≤ 1 := by
  have hh := (mass_bounds (tensorState (rawState s n a m) K)
    (fun x => orderResult s n a m K x=orderOf u)
    (tensor_normalized _ K (raw_normalized s n a m))).2
  rw [orderResult_mass hn hs a m hm u ha hdB] at hh
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [orderSuccess,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_pow,
    Rat.cast_ofNat,Rat.cast_mul,Rat.cast_natCast] using hh

/-- Local same-record equalization, now specialized to the actual list law and
actual source constants. The guess is tested for a single fixed padded list. -/
theorem list_passed_mass {m n : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hb : m<2^n)
    (hodd : Odd m) (p₀ p₁ : Component m) (hne : p₁≠p₀)
    (y₀ : Basis (transitionWidth n)) :
    outcomeMass (passed (GoodList (by omega : m≠0) hb p₀ (n^5)) y₀
      (listSuccess m n (n^5)) (target n))
      (fresh (tensorState (fairState (Nat.clog 2 m)) (n^5))
        (transitionWidth n) (2*n) (n*n^5))=(target n:ℝ) := by
  have hlow := listSuccess_lower hn hm hb hodd p₀ p₁ hne
  have hp := target_pos (by omega : 1 ≤ 2*n)
  apply passed_mass _ _ _ _ _ (tensor_normalized _ _ (fairState_normalized _))
    (by rw [list_good_mass _ hb hodd p₀]; simp [listSuccess])
    (listSuccess_at hb.le _) (target_at n) (by unfold coinBits; omega)
    (by exact hp.trans_le hlow) (listSuccess_le_one (by omega) hb hodd p₀ _)
    (by omega) (target_pos (by omega)) (target_le_ordinary (by omega) hlow)

/-- Local same-record equalization for the literal n^5 repeated order trial. -/
theorem order_passed_mass {w n s : ℕ} (hn : 128 ≤ n) (hs : 2^(s+2)=(2^n)^16)
    (a m : Basis w) (hm : 2 ≤ (bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hdB : orderOf u<2^n) (y₀ : Basis (transitionWidth n)) :
    outcomeMass (passed (fun x => orderResult s n a m (n^5) x=orderOf u) y₀
      (orderSuccess (orderOf u) (n^5)) (target n))
      (fresh (tensorState (rawState s n a m) (n^5))
        (transitionWidth n) (2*n) ((n+10)*n^5))=(target n:ℝ) := by
  have hlow := orderSuccess_lower hn hs a m hm u ha hdB
  have hp := target_pos (by omega : 1 ≤ 2*n)
  apply passed_mass _ _ _ _ _ (tensor_normalized _ _ (raw_normalized s n a m))
    (by rw [orderResult_mass (by omega) hs a m hm u ha hdB]; simp [orderSuccess])
    (orderSuccess_at hdB.le _) (target_at n) (by unfold coinBits; omega)
    (by exact hp.trans_le hlow) (orderSuccess_le_one (by omega) hs a m hm u ha hdB _)
    (by omega) (target_pos (by omega)) (target_le_ordinary (by omega) hlow)

end Completion
end ExactQuantumFactoring


end

end OAI
