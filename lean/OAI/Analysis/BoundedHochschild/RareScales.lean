import Mathlib
import OAI.Analysis.BoundedHochschild.CatalanWords

namespace OAI

/-! Rare-event probabilities, time scales and label counts. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open Filter Topology
namespace HochschildRare

 
def q (n : ℕ) : ℝ := (1/2:ℝ)^(2^n)
def p (n : ℕ) : ℝ := q n^2
def time (n : ℕ) : ℕ := 2^(3*2^n)
def slots (n : ℕ) : ℕ := (n+1)*time n
def labels (n : ℕ) : ℕ := slots n^4

lemma q_pos (n : ℕ) : 0 < q n := by unfold q; positivity
lemma q_le (n : ℕ) : q n ≤ 1/2 := by
  unfold q
  exact pow_le_of_le_one (by norm_num) (by norm_num) (by positivity)
lemma p_pos (n : ℕ) : 0 < p n := sq_pos_of_pos (q_pos n)
lemma p_le (n : ℕ) : p n ≤ 1/4 := by
  have := q_le n
  have := q_pos n
  unfold p
  nlinarith
lemma q_succ (n : ℕ) : q (n+1) = p n := by
  dsimp [q, p]
  rw [Nat.pow_succ, pow_mul]
lemma p_succ (n : ℕ) : p (n+1) = p n^2 := by rw [p,q_succ]
lemma p_succ_le (n : ℕ) : p (n+1) ≤ 1/16 := by
  rw [p_succ]
  have := p_pos n
  have := p_le n
  nlinarith
lemma p_antitone : Antitone p := by
  apply antitone_nat_of_succ_le
  intro n
  rw [p_succ]
  exact pow_le_of_le_one (p_pos n).le (by linarith [p_le n]) (by decide)

lemma tail_bound (n k : ℕ) : p (n+1+k) ≤ p n^2*(1/16:ℝ)^k := by
  induction k with
  | zero => simp only [add_zero,pow_zero,mul_one,p_succ,le_refl]
  | succ k ih =>
    rw [show n+1+(k+1) = (n+1+k)+1 by omega,p_succ,pow_two,pow_succ]
    have hp := (p_antitone (show n+1 ≤ n+1+k by omega)).trans (p_succ_le n)
    calc
      p (n+1+k)*p (n+1+k) ≤ (p n^2*(1/16:ℝ)^k)*(1/16) :=
        mul_le_mul ih hp (p_pos _).le (by positivity)
      _ = _ := by ring

lemma geometric_bound (n : ℕ) : p n ≤ (1/4:ℝ)^(n+1) := by
  induction n with
  | zero => norm_num [p,q]
  | succ n ih =>
    rw [p_succ,pow_two,pow_succ]
    exact mul_le_mul ih (p_le n) (p_pos _).le (by positivity)

lemma summable_p : Summable p :=
  Summable.of_nonneg_of_le (fun n => (p_pos n).le) geometric_bound
    ((summable_geometric_of_norm_lt_one (by norm_num : ‖(1/4:ℝ)‖ < 1)).comp_injective
      Nat.succ_injective)

lemma sum_p_le : ∑' n, p n ≤ 1/3 := by
  have hg : (∑' n : ℕ, (1/4:ℝ)^(n+1)) = 1/3 := by
    simp_rw [pow_succ]
    rw [tsum_mul_right,tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/4:ℝ)‖ < 1)]
    norm_num
  rw [← hg]
  exact summable_p.tsum_le_tsum geometric_bound
    ((summable_geometric_of_norm_lt_one (by norm_num : ‖(1/4:ℝ)‖ < 1)).comp_injective
      Nat.succ_injective)

lemma sum_tail_le (n : ℕ) : ∑' k, p (n+1+k) ≤ (16/15:ℝ)*p n^2 := by
  have hs : Summable (fun k => p n^2*(1/16:ℝ)^k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/16:ℝ)‖ < 1)).mul_left _
  have hsp : Summable (fun k => p (n+1+k)) := Summable.of_nonneg_of_le
    (fun k => (p_pos _).le) (tail_bound n) hs
  have hsum := hsp.tsum_le_tsum (tail_bound n) hs
  rw [tsum_mul_left,tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/16:ℝ)‖ < 1)] at hsum
  norm_num at hsum
  nlinarith [hsum]

lemma time_pos (n : ℕ) : 0 < time n := by unfold time; positivity
lemma slots_pos (n : ℕ) : 0 < slots n := Nat.mul_pos (Nat.succ_pos _) (time_pos n)
lemma labels_pos (n : ℕ) : 0 < labels n := pow_pos (slots_pos n) _

lemma successor_le_two_pow (n : ℕ) : n+1 ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.pow_succ]
    have : 0 < 2^n := by positivity
    omega

lemma q_geometric_bound (n : ℕ) : q n ≤ (1/2:ℝ)^(n+1) :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) (successor_le_two_pow n)

lemma tendsto_stage_q : Tendsto (fun n : ℕ => (n+1:ℝ)*q n) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => mul_nonneg (by positivity) (q_pos n).le)
    (fun n => mul_le_mul_of_nonneg_left (q_geometric_bound n) (by positivity))
  have ht := (tendsto_self_mul_const_pow_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) < 1)).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using ht

lemma time_mul_p_mul_q (n : ℕ) : (time n:ℝ)*p n*q n = 1 := by
  unfold time p q
  push_cast
  rw [show 3*2^n = 2^n*3 by omega,pow_mul,div_pow,one_pow]
  field_simp

lemma slots_mul_p_sq (n : ℕ) : (slots n:ℝ)*p n^2 = (n+1:ℝ)*q n := by
  have he := time_mul_p_mul_q n
  have he' : (time n:ℝ)*p n^2 = q n := by
    rw [p] at he ⊢
    nlinarith [congrArg (fun x : ℝ => x*q n) he]
  simp only [slots,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  rw [mul_assoc,he']

lemma geometric_miss_bound (x : ℝ) (_hx : 0 ≤ x) (hx1 : x ≤ 1) (N : ℕ) :
    (1+(N:ℝ)*x)*(1-x)^N ≤ 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hh : (1+((N:ℝ)+1)*x)*(1-x) ≤ 1+(N:ℝ)*x := by
      nlinarith [mul_nonneg (show 0 ≤ (N:ℝ)+1 by positivity) (sq_nonneg x)]
    calc
      (1+((N+1:ℕ):ℝ)*x)*(1-x)^(N+1) =
          ((1+((N:ℝ)+1)*x)*(1-x))*(1-x)^N := by push_cast; ring
      _ ≤ (1+(N:ℝ)*x)*(1-x)^N :=
        mul_le_mul_of_nonneg_right hh (pow_nonneg (by linarith) _)
      _ ≤ 1 := ih

lemma miss_le_q (n : ℕ) : (1-p n)^time n ≤ q n := by
  have hb := geometric_miss_bound (p n) (p_pos n).le (by linarith [p_le n]) (time n)
  have ht := time_mul_p_mul_q n
  have hp : 0 ≤ (1-p n)^time n := pow_nonneg (by linarith [p_le n]) _
  have htpos : 0 < (time n:ℝ)*p n := mul_pos (by exact_mod_cast time_pos n) (p_pos n)
  apply (mul_le_mul_iff_right₀ htpos).mp
  nlinarith

lemma slots_ge_stage (n : ℕ) : n+1 ≤ slots n := by
  exact le_mul_of_one_le_right (by omega) (time_pos n)

lemma slots_tendsto : Tendsto slots atTop atTop := by
  exact tendsto_atTop_mono slots_ge_stage (tendsto_add_atTop_nat 1)

lemma slots_real_tendsto : Tendsto (fun n => (slots n:ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp slots_tendsto

lemma bad_bound_tendsto : Tendsto (fun n =>
    (16/15:ℝ)*(n+1)*q n + (slots n:ℝ)⁻¹ + (1/2:ℝ)*(slots n:ℝ)⁻¹^2 +
    (n+1:ℝ)*(1-p n)^time n) atTop (𝓝 0) := by
  have hmiss : Tendsto (fun n : ℕ => (n+1:ℝ)*(1-p n)^time n) atTop (𝓝 0) :=
    squeeze_zero (fun n => mul_nonneg (by positivity)
      (pow_nonneg (by linarith [p_le n]) _))
      (fun n => mul_le_mul_of_nonneg_left (miss_le_q n) (by positivity)) tendsto_stage_q
  have hinv := tendsto_inv_atTop_zero.comp slots_real_tendsto
  convert (((tendsto_stage_q.const_mul (16/15)).add hinv).add
    ((hinv.pow 2).const_mul (1/2))).add hmiss using 1 <;> simp [mul_assoc]

end HochschildRare
end

end OAI
