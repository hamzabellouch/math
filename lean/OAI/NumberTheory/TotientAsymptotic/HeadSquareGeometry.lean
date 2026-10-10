import OAI.NumberTheory.TotientAsymptotic.FullWitnessWeight
import OAI.NumberTheory.TotientAsymptotic.NormalRemainderLayer

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma head_prime_discard_bound {x : ℝ} (hx : 2 ≤ x) (hB : 5 ≤ B x)
    {p : ℕ} (hp : p.Prime) (hpX : ((p-1 : ℕ) : ℝ) ≤ x) :
    p ∈ Nat.primesLE (discardPrimeBound (B x)) := by
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpx : (p : ℝ) ≤ x+1 := by
    have hcast : ((p-1 : ℕ) : ℝ)=(p : ℝ)-1 := by rw [Nat.cast_sub hp.one_lt.le]; norm_num
    rw [hcast] at hpX
    linarith
  have hpx2 : (p : ℝ) ≤ x^2 := hpx.trans (by nlinarith)
  have hlogp := Real.log_le_log (zero_lt_one.trans hp1) hpx2
  rw [Real.log_pow] at hlogp
  norm_num only [Nat.cast_ofNat] at hlogp
  have hBp : B p ≤ B x+1 := by
    have hh := Real.log_le_log (Real.log_pos hp1) hlogp
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlogx.ne'] at hh
    have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    change Real.log (Real.log (p : ℝ)) ≤ Real.log (Real.log x)+1
    linarith
  have hcoord : B p ≤ (6/5 : ℝ)*B x := hBp.trans (by linarith)
  have hpbound : (p : ℝ) ≤ Real.exp (Real.exp ((6/5 : ℝ)*B x)) :=
    (Real.log_le_iff_le_exp (zero_lt_one.trans hp1)).mp
      ((Real.log_le_iff_le_exp (Real.log_pos hp1)).mp hcoord)
  exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast hpbound.trans (discardPrimeBound_bounds (by linarith : 2 ≤ B x)).2.2.2,hp⟩

lemma wholeWitnessPrime_full {x : ℝ} {H j : ℕ} (q : RemainderDatum (L x H) × ℕ)
    (hj : j ≤ L x H) :
    wholeWitnessPrime q.2 q.1 j=fullWitnessPrimes q ⟨j,by omega⟩ := by
  cases j with
  | zero => simp [wholeWitnessPrime,fullWitnessPrimes]
  | succ j =>
    have hj' : 1 ≤ j+1 ∧ j+1 ≤ L x H := by omega
    simp only [wholeWitnessPrime,Nat.add_one_ne_zero,ite_false,remainderPrime,dite_eq_left hj',
      Nat.add_sub_cancel,fullWitnessPrimes]
    exact (Fin.cons_succ (α := fun _ : Fin (L x H+1) => ℕ)
      q.2 q.1.primes (⟨j,by omega⟩ : Fin (L x H))).symm


lemma full_witness_prime_bound : ∀ᶠ x : ℝ in atTop, ∀ H : ℕ, P H ≤ H →
    ∀ t : ℝ, t ≤ x → ∀ q : RemainderDatum (L x H) × ℕ,
      IsBasicRemainder x H q.1 → IsBasicTuple x H t (witnessTuple q.2 q.1) →
      ∀ j, fullWitnessPrimes q j ∈ Nat.primesLE (discardPrimeBound (B x)) := by
  filter_upwards [basic_suffix_discard_bound,eventually_ge_atTop (2 : ℝ),
    B_tendsto.eventually (eventually_ge_atTop (5 : ℝ)),
    m_tendsto.eventually (eventually_ge_atTop 1)] with x hbound hx hB hm
  intro H hPH t ht q hη hτ j
  by_cases hj : j.val=0
  · have hj0 : j=0 := Fin.ext hj
    rw [hj0]
    change q.2 ∈ Nat.primesLE (discardPrimeBound (B x))
    have hpre := (isPrefixDatum_iff x H (prefixOfRemainder x H q.1)).mpr ⟨q.1,hη,rfl⟩
    have hD := basic_prefix_denominator_pos hPH hpre
    have hval := hτ.2.2.2.trans ht
    rw [witnessTuple,tupleValue_eq_head] at hval
    have hle : ((q.2-1 : ℕ) : ℝ) ≤ x := by
      have hnat : q.2-1 ≤ (q.2-1)*((prefixOfRemainder x H q.1).d*
          ∏ i, ((prefixOfRemainder x H q.1).primes i-1)) :=
        Nat.le_mul_of_pos_right _ hD
      exact (Nat.cast_le.mpr hnat).trans hval
    exact head_prime_discard_bound hx hB hτ.1 hle
  · have hjL : j.val ≤ L x H := by have := j.isLt; omega
    rw [← wholeWitnessPrime_full q hjL,wholeWitnessPrime,ite_eq_right hj]
    have hb0 : fordBandScale x 0=B x := by simp [fordBandScale]
    rw [← hb0]
    exact hbound H 0 j.val (by omega) (Nat.zero_le _) hjL hm (by rw [hb0]; linarith) q.1 hη

end TotientAsymptotic

end

end OAI
