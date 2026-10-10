import Mathlib
import OAI.Combinatorics.KMedian.Compression.CircuitBitBound

namespace OAI


                                               
section
namespace MetricKMedian.Binary
open Finset

def HasHeight (q : ℚ) (L : ℕ) : Prop := |q.num| ≤ (2:ℤ)^L ∧ (q.den:ℤ) ≤ (2:ℤ)^L

namespace HasHeight
variable {q r : ℚ} {L M : ℕ}

 theorem mono (h : HasHeight q L) (hLM : L≤M) : HasHeight q M :=
  ⟨h.1.trans (pow_le_pow_right₀ (by norm_num) hLM),h.2.trans (pow_le_pow_right₀ (by norm_num) hLM)⟩

 theorem zero (L : ℕ) : HasHeight 0 L := by
  constructor
  · simp
  · simp only [Rat.den_zero,Int.natCast_one]
    exact one_le_pow₀ (by norm_num)

 theorem one (L : ℕ) : HasHeight 1 L := by
  constructor <;> simp only [Rat.num_one,Rat.den_one,abs_one,Int.natCast_one] <;>
    exact one_le_pow₀ (by norm_num)

 theorem neg (h : HasHeight q L) : HasHeight (-q) L := by
  simpa only [HasHeight,Rat.num_neg_eq_neg_num,Rat.den_neg_eq_den,abs_neg] using h

 theorem mul (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q*r) (L+M) := by
  have hdq : (q.den:ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hdr : (r.den:ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hh := Gaussian.ratio_num_den_bound (q.num*r.num) ((q.den:ℤ)*r.den) (mul_ne_zero hdq hdr)
    ((2:ℤ)^(L+M)) (by
      rw [abs_mul,pow_add]
      exact mul_le_mul hq.1 hr.1 (abs_nonneg _) (by positivity)) (by
      rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),abs_of_nonneg (Int.natCast_nonneg _),pow_add]
      exact mul_le_mul hq.2 hr.2 (by positivity) (by positivity))
  have he : ((q.num*r.num:ℤ):ℚ)/(((q.den:ℤ)*r.den:ℤ):ℚ)=q*r := by
    push_cast
    rw [mul_div_mul_comm,Rat.num_div_den,Rat.num_div_den]
  rwa [he] at hh

 theorem inv (hq : HasHeight q L) : HasHeight q⁻¹ L := by
  by_cases hq0 : q=0
  · rw [hq0,inv_zero]
    exact zero L
  have hqn : q.num ≠ 0 := by
    intro h
    apply hq0
    rw [← Rat.num_div_den q,h,Int.cast_zero,zero_div]
  have hh := Gaussian.ratio_num_den_bound (q.den:ℤ) q.num hqn ((2:ℤ)^L)
    (by simpa only [abs_of_nonneg (Int.natCast_nonneg _)] using hq.2) hq.1
  have he : ((q.den:ℤ):ℚ)/(q.num:ℚ)=q⁻¹ := by
    conv_rhs => rw [← Rat.num_div_den q]
    simp only [inv_div,Int.cast_natCast]
  rwa [he] at hh

 theorem div (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q/r) (L+M) := by
  simpa only [div_eq_mul_inv] using hq.mul hr.inv

 theorem add (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q+r) (L+M+1) := by
  have hdq : (q.den:ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hdr : (r.den:ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hterm₁ : |q.num*(r.den:ℤ)| ≤ (2:ℤ)^(L+M) := by
    rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),pow_add]
    exact mul_le_mul hq.1 hr.2 (by positivity) (by positivity)
  have hterm₂ : |r.num*(q.den:ℤ)| ≤ (2:ℤ)^(L+M) := by
    rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),Nat.add_comm L M,pow_add]
    exact mul_le_mul hr.1 hq.2 (by positivity) (by positivity)
  have hh := Gaussian.ratio_num_den_bound (q.num*r.den+r.num*q.den) ((q.den:ℤ)*r.den)
    (mul_ne_zero hdq hdr) ((2:ℤ)^(L+M+1)) (by
      have hab := abs_add_le (q.num*(r.den:ℤ)) (r.num*(q.den:ℤ))
      rw [pow_succ]
      linarith) (by
      rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),abs_of_nonneg (Int.natCast_nonneg _)]
      have hb : (q.den:ℤ)*r.den ≤ (2:ℤ)^(L+M) := by
        rw [pow_add]
        exact mul_le_mul hq.2 hr.2 (by positivity) (by positivity)
      exact hb.trans (pow_le_pow_right₀ (by norm_num) (by omega)))
  have he : ((q.num*r.den+r.num*q.den:ℤ):ℚ)/(((q.den:ℤ)*r.den:ℤ):ℚ)=q+r := by
    push_cast
    rw [add_div, mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr r.den_ne_zero),
      mul_comm (r.num:ℚ) (q.den:ℚ),mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr q.den_ne_zero),
      Rat.num_div_den,Rat.num_div_den]
  rwa [he] at hh

 theorem sub (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q-r) (L+M+1) := by
  simpa only [sub_eq_add_neg] using hq.add hr.neg

 theorem sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i∈s, HasHeight (f i) L) :
    HasHeight (∑ i∈s, f i) (s.card*(L+1)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [sum_empty,card_empty,zero_mul] using zero 0
  | @insert a s ha ih =>
      rw [sum_insert ha,card_insert_of_notMem ha]
      have hs := ih (fun i hi => h i (mem_insert_of_mem hi))
      have hh := (h a (mem_insert_self _ _)).add hs
      convert hh using 1
      ring

 theorem partialSum {n : ℕ} (f : Fin n → ℚ) (s : Finset (Fin n))
    (h : ∀ i, HasHeight (f i) L) : HasHeight (∑ i∈s, f i) (n*(L+1)) := by
  have hh := sum s f (fun i _ => h i)
  apply hh.mono
  exact Nat.mul_le_mul_right _ ((card_le_card (subset_univ s)).trans_eq (card_fin n))

end HasHeight
end MetricKMedian.Binary
end

end OAI
