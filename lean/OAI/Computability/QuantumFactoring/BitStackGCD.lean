import Mathlib
import OAI.Computability.QuantumFactoring.BitStackMultiplier

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def gcdStep (x : ℕ×ℕ) : ℕ×ℕ := if x.2=0 then x else (x.2,x.1%x.2)
def gcdRound (x : ℕ×ℕ) : ℕ×ℕ := gcdStep (gcdStep x)

lemma gcdStep_value (x : ℕ×ℕ) : (gcdStep x).1.gcd (gcdStep x).2=x.1.gcd x.2 := by
  unfold gcdStep
  split
  · rfl
  · dsimp only
    rw [Nat.gcd_comm x.2]
    exact (Nat.gcd_rec x.2 x.1).symm.trans (Nat.gcd_comm x.2 x.1)

lemma mod_half {b r : ℕ} (hr : 0<r) (hlt : r<b) : b%r≤b/2 := by
  by_cases h : 2*r≤b
  · have ht:=Nat.mod_lt b hr
    omega
  · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega : b-r<r)]
    omega

lemma gcdRound_half (x : ℕ×ℕ) : (gcdRound x).2≤x.2/2 := by
  by_cases hb : x.2=0
  · simp [gcdRound,gcdStep,hb]
  · have hp : 0<x.2:=by omega
    have hr:=Nat.mod_lt x.1 hp
    by_cases hz : x.1%x.2=0
    · simp [gcdRound,gcdStep,hb,hz]
    · simp only [gcdRound,gcdStep,hb,ite_false,hz]
      exact mod_half (by omega) hr

lemma gcdRound_value (x : ℕ×ℕ) : (gcdRound x).1.gcd (gcdRound x).2=x.1.gcd x.2 := by
  rw [gcdRound,gcdStep_value,gcdStep_value]

lemma gcdRound_iterate_bound (i : ℕ) (x : ℕ×ℕ) :
    (gcdRound^[i] x).2≤x.2/2^i := by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    calc
      (gcdRound (gcdRound^[i] x)).2≤(gcdRound^[i] x).2/2:=gcdRound_half _
      _≤(x.2/2^i)/2:=Nat.div_le_div_right ih
      _=x.2/2^(i+1):=by rw [Nat.div_div_eq_div_mul,pow_succ]

lemma gcdRound_iterate_value (i : ℕ) (x : ℕ×ℕ) :
    (gcdRound^[i] x).1.gcd (gcdRound^[i] x).2=x.1.gcd x.2 := by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply',gcdRound_value,ih]

lemma gcdRound_result (x : ℕ×ℕ) : (gcdRound^[x.2.bits.length] x).1=x.1.gcd x.2 := by
  have hz : (gcdRound^[x.2.bits.length] x).2=0:=by
    have hh:=gcdRound_iterate_bound x.2.bits.length x
    have hzdiv : x.2/2^x.2.bits.length=0:=by
      rw [Nat.size_eq_bits_len];exact Nat.div_eq_of_lt (Nat.lt_size_self x.2)
    rw [hzdiv] at hh
    omega
  simpa only [hz,Nat.gcd_zero_right] using gcdRound_iterate_value x.2.bits.length x

lemma gcdStep_sizeSum (x : ℕ×ℕ) :
    (gcdStep x).1.bits.length+(gcdStep x).2.bits.length≤x.1.bits.length+x.2.bits.length := by
  have hm:=bits_length_mono (Nat.mod_le x.1 x.2)
  unfold gcdStep
  split
  · exact le_rfl
  · change x.2.bits.length+(x.1%x.2).bits.length≤x.1.bits.length+x.2.bits.length
    omega

lemma gcdRound_iterate_sizeSum (i : ℕ) (x : ℕ×ℕ) :
    (gcdRound^[i] x).1.bits.length+(gcdRound^[i] x).2.bits.length≤
      x.1.bits.length+x.2.bits.length := by
  induction i with
  | zero=>rfl
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    exact ((gcdStep_sizeSum _).trans (gcdStep_sizeSum _)).trans ih


end ExactQuantumFactoring.BitStackProgram
end

end OAI
