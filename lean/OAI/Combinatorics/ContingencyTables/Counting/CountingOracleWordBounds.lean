import OAI.Combinatorics.ContingencyTables.Counting.CountingOracleScheduleBounds
import OAI.Combinatorics.ContingencyTables.Counting.CompanionEstimatorAmplification
import OAI.Combinatorics.ContingencyTables.Counting.CountingTerminalSchedule

namespace OAI

/-! # Polynomial word sizes for the executed density oracle -/

namespace ContingencyTables.CountingOracleWordBounds
open CompanionFactorialApplication CompanionOracleDensity GridBoundary
open Polynomial
open scoped BigOperators Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

lemma binWordBits_bound (A : Instance I J) (h : ℕ) :
    binWordBits A h ≤ A.d*(CountingTerminalSchedule.capacityBits A+1+4*(h+A.d)) := by
  have hb (i : Fin (dimension A)) :
      Nat.clog 2 (freeRange A (index A i)+1) ≤ CountingTerminalSchedule.capacityBits A+1 := by
    let t := index A i
    have hs : (A.b t.val.1 t.val.2+1).size ≤ CountingTerminalSchedule.capacityBits A := by
      change (A.b t.val.1 t.val.2+1).size ≤ ∑ a : I×J,(A.b a.1 a.2+1).size
      exact Finset.single_le_sum (f := fun a : I×J => (A.b a.1 a.2+1).size)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (t.val.1,t.val.2))
    have hp := Nat.lt_size_self (A.b t.val.1 t.val.2+1)
    apply Nat.clog_le_of_le_pow
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hs
    change A.b t.val.1 t.val.2+1+1 ≤ 2^(CountingTerminalSchedule.capacityBits A+1)
    rw [pow_succ]
    omega
  unfold binWordBits
  calc
    _ ≤ ∑ _i : Fin (dimension A),
        (CountingTerminalSchedule.capacityBits A+1+4*(h+A.d)) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.add_le_add_right (hb i) _
    _ = dimension A*(CountingTerminalSchedule.capacityBits A+1+4*(h+A.d)) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (ForestScaledPenalty.free_card_le A)

lemma oracle_time_bound (A : Instance I J) (C K E : ℕ) (theta : ℚ)
    (hE : 1/theta ≤ (E:ℚ)) :
    oracleTime A C K 1 theta ≤
      2*(10000*A.d^2*K)^2*(rationalHeight A C+A.d*K+2+16*E) := by
  unfold oracleTime
  apply Nat.ceil_le.mpr
  have ht : (1:ℝ)/(theta:ℝ) ≤ (E:ℝ) := by exact_mod_cast hE
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add_left (mul_le_mul_of_nonneg_left ht (show (0:ℝ) ≤ 16 by norm_num))
      (height A C+(A.d:ℝ)*K+2))
    (show 0 ≤ mixingConstant A K by unfold mixingConstant; positivity)
  convert hh using 1 <;>
    simp only [mixingConstant,←rationalHeight_cast A C,Nat.cast_mul,Nat.cast_add,
      Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] <;> ring

lemma samples_bound (j E : ℕ) (delta : ℚ) (hd : 0 < delta)
    (hE : 1/delta ≤ (E:ℚ)) : sampleCount j delta 1 ≤ 65536*(j+1)*E^2 := by
  unfold sampleCount
  apply Nat.ceil_le.mpr
  have he0 : 0 ≤ 1/delta := (one_div_pos.mpr hd).le
  have hs : (1/delta)^2 ≤ (E:ℚ)^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hs (show (0:ℚ) ≤ 65536*(j+1) by positivity)
  convert hh using 1 <;> push_cast <;> ring

lemma offset_bound (A : Instance I J) (E : ℕ) (delta : ℚ)
    (hE : 1/delta ≤ (E:ℚ)) : offsetAccuracy A delta ≤ 4096*A.d*E := by
  unfold offsetAccuracy
  apply Nat.ceil_le.mpr
  have hh := mul_le_mul_of_nonneg_left hE (show (0:ℚ) ≤ 4096*A.d by positivity)
  convert hh using 1 <;> push_cast <;> ring

def timeBound (M E : ℕ) : ℕ :=
  2*(10000*M^2*M)^2*(M+M*M+2+4096*E)
def sampleBound (M E : ℕ) : ℕ := 65536*(M+1)*E^2
def binBound (M E : ℕ) : ℕ := M*(M+1+4*(4096*M*E+M))
def estimatorBound (M E : ℕ) : ℕ :=
  M*(sampleBound M E*(timeBound M E*(9*M)))+
    sampleBound M E*(timeBound M E*(9*M)+binBound M E)

lemma oracle_time_uniform (A : Instance I J) (C K M E : ℕ) (theta : ℚ)
    (hd : A.d ≤ M) (hK : K ≤ M) (hH : rationalHeight A C ≤ M)
    (hE : 1/theta ≤ ((256*E:ℕ):ℚ)) :
    oracleTime A C K 1 theta ≤ timeBound M E := by
  apply (oracle_time_bound A C K (256*E) theta hE).trans
  unfold timeBound
  apply Nat.mul_le_mul
  · exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left
      (Nat.mul_le_mul (Nat.mul_le_mul_left 10000 (Nat.pow_le_pow_left hd 2)) hK) 2)
  · have hk := Nat.mul_le_mul hd hK
    omega

lemma estimator_bound (A : Instance I J) (C K j M E : ℕ) (delta : ℚ)
    (hd : A.d ≤ M) (hK : K ≤ M) (hH : rationalHeight A C ≤ M)
    (hj : j ≤ M) (hL : CountingTerminalSchedule.capacityBits A ≤ M)
    (hdelta : 0 < delta) (hE : 1/delta ≤ (E:ℚ)) :
    estimatorWordBits A C K j delta 1 ≤ estimatorBound M E := by
  have hE' : 1/delta ≤ ((256*E:ℕ):ℚ) := hE.trans (by exact_mod_cast (show E ≤ 256*E by omega))
  have ht := oracle_time_uniform A C K M E delta hd hK hH hE'
  have hcorr : 1/(delta/256) ≤ ((256*E:ℕ):ℚ) := by
    have hh := mul_le_mul_of_nonneg_left hE (show (0:ℚ) ≤ 256 by norm_num)
    convert hh using 1 <;> push_cast <;> field_simp
  have htc : oracleTime A C K 1 (correctionTheta delta) ≤ timeBound M E := by
    simpa only [correctionTheta,Rat.cast_div,Rat.cast_ofNat] using
      oracle_time_uniform A C K M E (delta/256) hd hK hH hcorr
  have hs : sampleCount j delta 1 ≤ sampleBound M E :=
    (samples_bound j E delta hdelta hE).trans (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left 65536 (Nat.add_le_add_right hj 1)))
  have ha : offsetAccuracy A delta ≤ 4096*M*E :=
    (offset_bound A E delta hE).trans (Nat.mul_le_mul_right E (Nat.mul_le_mul_left 4096 hd))
  have hb : binWordBits A (offsetAccuracy A delta) ≤ binBound M E := by
    apply (binWordBits_bound A _).trans
    unfold binBound
    exact Nat.mul_le_mul hd (Nat.add_le_add (Nat.add_le_add_right hL 1)
      (Nat.mul_le_mul_left 4 (Nat.add_le_add ha hd)))
  have hw : oracleStepBits A C ≤ 9*M := by
    have hl : Nat.clog 2 (8*A.d) ≤ 8*A.d :=
      Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
    unfold oracleStepBits
    omega
  unfold estimatorWordBits estimatorBound oracleIntegerBits
  exact Nat.add_le_add (Nat.mul_le_mul hj (Nat.mul_le_mul hs (Nat.mul_le_mul ht hw)))
    (Nat.mul_le_mul hs (Nat.add_le_add (Nat.mul_le_mul htc hw) hb))

def innerPolynomial : Polynomial ℕ := 400*(X+1)*X
def timePolynomial : Polynomial ℕ :=
  2*(10000*X^2*X)^2*(X+X*X+2+4096*innerPolynomial)
def samplePolynomial : Polynomial ℕ := 65536*(X+1)*innerPolynomial^2
def binPolynomial : Polynomial ℕ := X*(X+1+4*(4096*X*innerPolynomial+X))
def estimatorPolynomial : Polynomial ℕ :=
  X*(samplePolynomial*(timePolynomial*(9*X)))+
    samplePolynomial*(timePolynomial*(9*X)+binPolynomial)
def medianPolynomial : Polynomial ℕ := 64*(X+1)*estimatorPolynomial

lemma estimatorPolynomial_eval (M : ℕ) :
    estimatorPolynomial.eval M=estimatorBound M (400*(M+1)*M) := by
  simp only [estimatorPolynomial,samplePolynomial,timePolynomial,innerPolynomial,binPolynomial,
    estimatorBound,sampleBound,timeBound,binBound,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]

lemma median_bound_separate (A : Instance I J) (C K j M : ℕ) (xi delta : ℚ)
    (hd : A.d ≤ M) (hK : K ≤ M) (hH : rationalHeight A C ≤ M)
    (hj : j ≤ M) (hL : CountingTerminalSchedule.capacityBits A ≤ M)
    (hxi : 0 < xi) (hi : 1/xi ≤ (M:ℚ))
    (hr : CommonBasesFPRAS.repetitionCount delta ≤ 64*(M+1)) :
    medianEstimatorBits A C K j xi delta ≤ medianPolynomial.eval M := by
  have hdelta : 0 < innerTolerance (xi/2) j := by unfold innerTolerance; positivity
  have heq : 1/innerTolerance (xi/2) j=(400:ℚ)*(j+1)*(1/xi) := by
    unfold innerTolerance
    field_simp
    ring
  have he : 1/innerTolerance (xi/2) j ≤ ((400*(M+1)*M:ℕ):ℚ) := by
    rw [heq]
    have hh := mul_le_mul
      (show (400:ℚ)*(j+1) ≤ 400*(M+1) by exact_mod_cast Nat.mul_le_mul_left 400 (Nat.add_le_add_right hj 1))
      hi (one_div_pos.mpr hxi).le (by positivity)
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using hh
  have hb := estimator_bound A C K j M (400*(M+1)*M) (innerTolerance (xi/2) j)
    hd hK hH hj hL hdelta he
  unfold medianEstimatorBits
  rw [medianPolynomial,Polynomial.eval_mul,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one,estimatorPolynomial_eval]
  exact Nat.mul_le_mul hr hb

lemma median_bound (A : Instance I J) (C K j M : ℕ) (xi : ℚ)
    (hd : A.d ≤ M) (hK : K ≤ M) (hH : rationalHeight A C ≤ M)
    (hj : j ≤ M) (hL : CountingTerminalSchedule.capacityBits A ≤ M)
    (hxi : 0 < xi) (hi : 1/xi ≤ (M:ℚ))
    (hr : CommonBasesFPRAS.repetitionCount xi ≤ 64*(M+1)) :
    medianEstimatorBits A C K j xi xi ≤ medianPolynomial.eval M :=
  median_bound_separate A C K j M xi xi hd hK hH hj hL hxi hi hr

end
end ContingencyTables.CountingOracleWordBounds

end OAI
