import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Polynomial
import OAI.NumberTheory.Catalan.Energy.BarrierChebyshevUSeries
import OAI.NumberTheory.Catalan.Energy.BarrierTailPairRational

namespace OAI

noncomputable section

namespace InternalCatalan

section

private theorem barrierTail_norm_le (tail : List (ℂ × ℂ)) (k : ℕ) :
    (∀ zr ∈ tail, ‖zr.1‖ ≤ (99 / 100 : ℝ) ∧ ‖zr.2‖ ≤ 1) →
      ‖(tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum‖ ≤
        (tail.length : ℝ) * (99 / 100 : ℝ) ^ k := by
  induction tail with
  | nil => simp
  | cons zr tail ih =>
    intro hb
    have hz := hb zr (List.mem_cons_self)
    have ht := ih (fun w hw => hb w (List.mem_cons_of_mem _ hw))
    have hone : ‖zr.2 * zr.1 ^ k‖ ≤ (99 / 100 : ℝ) ^ k := by
      rw [norm_mul, norm_pow]
      calc
        _ ≤ 1 * (99 / 100 : ℝ) ^ k := by
          gcongr
          · exact hz.2
          · exact hz.1
        _ = _ := one_mul _
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ ‖zr.2 * zr.1 ^ k‖ + ‖(tail.map (fun w : ℂ × ℂ => w.2 * w.1 ^ k)).sum‖ :=
        norm_add_le _ _
      _ ≤ (99 / 100 : ℝ) ^ k + (tail.length : ℝ) * (99 / 100 : ℝ) ^ k :=
        add_le_add hone ht
      _ = _ := by ring

private theorem barrierTrial_abs_le (cs : List ℤ) (tail : List (ℂ × ℂ))
    (hc : cs.length ≤ 10)
    (ha : ∀ a ∈ cs, |(a : ℝ) / 100000000| < 1)
    (ht : tail.length ≤ 13)
    (hb : ∀ zr ∈ tail, ‖zr.1‖ ≤ (99 / 100 : ℝ) ∧ ‖zr.2‖ ≤ 1) (k : ℕ) :
    |barrierTrial cs tail k| ≤ 15 * (99 / 100 : ℝ) ^ k := by
  by_cases hk : k = 0
  · simp [barrierTrial, hk]
  have htail : |(tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re| ≤
      13 * (99 / 100 : ℝ) ^ k := by
    exact (Complex.abs_re_le_norm _).trans ((barrierTail_norm_le tail k hb).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast ht) (by positivity)))
  simp only [barrierTrial, ite_eq_right hk]
  calc
    _ ≤ |barrierFiniteCoeff cs k| +
        |(tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re| := by
      simpa only [Real.norm_eq_abs] using norm_add_le (barrierFiniteCoeff cs k)
        ((tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re)
    _ ≤ 2 * (99 / 100 : ℝ) ^ k + 13 * (99 / 100 : ℝ) ^ k :=
      add_le_add (barrierFiniteCoeff_abs_le cs hc ha k) htail
    _ = _ := by ring

theorem barrier_trials_abs_le (k : ℕ) :
    |barrierP2 k| ≤ 15 * (99 / 100 : ℝ) ^ k ∧
    |barrierV2 k| ≤ 15 * (99 / 100 : ℝ) ^ k ∧
    |barrierP1 k| ≤ 15 * (99 / 100 : ℝ) ^ k ∧
    |barrierV1 k| ≤ 15 * (99 / 100 : ℝ) ^ k := by
  have hp : ∀ zr ∈ barrierP2Tail, ‖zr.1‖ ≤ (99 / 100 : ℝ) ∧ ‖zr.2‖ ≤ 1 := by
    intro zr hz
    have h := barrierP2_tail_norm_bounds zr hz
    exact ⟨h.1.trans (by norm_num), h.2.le⟩
  have hv : ∀ zr ∈ barrierV2Tail, ‖zr.1‖ ≤ (99 / 100 : ℝ) ∧ ‖zr.2‖ ≤ 1 := by
    intro zr hz
    have h := barrierV2_tail_norm_bounds zr hz
    exact ⟨h.1.trans (by norm_num), h.2.le⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact barrierTrial_abs_le barrierP2Finite barrierP2Tail
      barrier_finite_lengths.1.le barrierP2_finite_abs_lt_one
      (barrier_tail_lengths.1.le.trans (by norm_num)) hp k
  · exact barrierTrial_abs_le barrierV2Finite barrierV2Tail
      barrier_finite_lengths.2.1.le barrierV2_finite_abs_lt_one
      barrier_tail_lengths.2.le hv k
  · exact barrierTrial_abs_le barrierP1Finite []
      (barrier_finite_lengths.2.2.1.le.trans (by norm_num)) barrierP1_finite_abs_lt_one
      (by simp) (by simp) k
  · exact barrierTrial_abs_le barrierV1Finite []
      (barrier_finite_lengths.2.2.2.le.trans (by norm_num)) barrierV1_finite_abs_lt_one
      (by simp) (by simp) k

theorem barrier_trials_abs_summable :
    Summable (fun k => |barrierP2 k|) ∧ Summable (fun k => |barrierV2 k|) ∧
    Summable (fun k => |barrierP1 k|) ∧ Summable (fun k => |barrierV1 k|) := by
  have hg : Summable (fun k : ℕ => (15 : ℝ) * (99 / 100 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(99 / 100 : ℝ)‖ < 1)).mul_left 15
  refine ⟨hg.of_norm_bounded (by intro k; simpa using (barrier_trials_abs_le k).1),
    hg.of_norm_bounded (by intro k; simpa using (barrier_trials_abs_le k).2.1),
    hg.of_norm_bounded (by intro k; simpa using (barrier_trials_abs_le k).2.2.1),
    hg.of_norm_bounded (by intro k; simpa using (barrier_trials_abs_le k).2.2.2)⟩

def barrierTrialNormSq (u : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)

private theorem summable_barrier_weighted_square (u : ℕ → ℝ)
    (hu : ∀ k, |u k| ≤ 15 * (99 / 100 : ℝ) ^ k)
    (hs : Summable (fun k => |u k|)) :
    Summable (fun k : ℕ => u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) := by
  have ht : Summable (fun k : ℕ => |u (k + 1)|) :=
    (summable_nat_add_iff 1).mpr hs
  apply (ht.mul_left 15).of_norm_bounded
  intro k
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
  have hkp : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num) hk
  have h15 : |u (k + 1)| ≤ 15 := by
    have hp : (99 / 100 : ℝ) ^ (k + 1) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have hh := (hu (k + 1)).trans (mul_le_mul_of_nonneg_left hp (by norm_num))
    simpa only [mul_one] using hh
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hkp]
  calc
    _ ≤ |u (k + 1)| ^ 2 := div_le_self (sq_nonneg _) hk
    _ ≤ 15 * |u (k + 1)| := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right h15 (abs_nonneg (u (k + 1)))

theorem barrier_trials_norm_summable :
    Summable (fun k : ℕ => barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ∧
    Summable (fun k : ℕ => barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ∧
    Summable (fun k : ℕ => barrierP1 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ∧
    Summable (fun k : ℕ => barrierV1 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) := by
  exact ⟨summable_barrier_weighted_square barrierP2
      (fun k => (barrier_trials_abs_le k).1) barrier_trials_abs_summable.1,
    summable_barrier_weighted_square barrierV2
      (fun k => (barrier_trials_abs_le k).2.1) barrier_trials_abs_summable.2.1,
    summable_barrier_weighted_square barrierP1
      (fun k => (barrier_trials_abs_le k).2.2.1) barrier_trials_abs_summable.2.2.1,
    summable_barrier_weighted_square barrierV1
      (fun k => (barrier_trials_abs_le k).2.2.2) barrier_trials_abs_summable.2.2.2⟩

theorem barrierTrialNormSq_nonneg (u : ℕ → ℝ) : 0 ≤ barrierTrialNormSq u := by
  exact tsum_nonneg (fun k => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

open Polynomial Filter
open scoped BigOperators

def barrierTrialT (u : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, u (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x /
    ((k + 1 : ℕ) : ℝ)

def barrierTrialS (u : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, u (k + 1) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)

private theorem barrierTrialT_term_norm_le (u : ℕ → ℝ) (k : ℕ) {x : ℝ}
    (hx : |x| ≤ 1) :
    ‖u (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x /
      ((k + 1 : ℕ) : ℝ)‖ ≤ |u (k + 1)| := by
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
  have hkp : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num) hk
  have ht := Chebyshev.abs_eval_T_real_le_one ((k + 1 : ℕ) : ℤ) hx
  rw [norm_div, norm_mul]
  simp only [Real.norm_eq_abs, abs_of_pos hkp]
  calc
    _ ≤ |u (k + 1)| * 1 / ((k + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht (abs_nonneg _)) hkp.le
    _ = |u (k + 1)| / ((k + 1 : ℕ) : ℝ) := by rw [mul_one]
    _ ≤ |u (k + 1)| := div_le_self (abs_nonneg _) hk

private theorem barrierTrialS_term_norm_le (u : ℕ → ℝ) (k : ℕ) {x : ℝ}
    (hx : |x| ≤ 1) :
    ‖u (k + 1) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)‖ ≤ |u (k + 1)| := by
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
  have hkp : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num) hk
  have ht : |x| ^ (k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
  rw [norm_div, norm_mul]
  simp only [Real.norm_eq_abs, abs_pow, abs_of_pos hkp]
  calc
    _ ≤ |u (k + 1)| * 1 / ((k + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht (abs_nonneg _)) hkp.le
    _ = |u (k + 1)| / ((k + 1 : ℕ) : ℝ) := by rw [mul_one]
    _ ≤ |u (k + 1)| := div_le_self (abs_nonneg _) hk

theorem barrierTrialT_summable (u : ℕ → ℝ) (hu : Summable (fun k => |u k|))
    {x : ℝ} (hx : |x| ≤ 1) :
    Summable (fun k : ℕ => u (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x /
      ((k + 1 : ℕ) : ℝ)) := by
  exact ((summable_nat_add_iff 1).mpr hu).of_norm_bounded
    (fun k => barrierTrialT_term_norm_le u k hx)

theorem barrierTrialS_summable (u : ℕ → ℝ) (hu : Summable (fun k => |u k|))
    {x : ℝ} (hx : |x| ≤ 1) :
    Summable (fun k : ℕ => u (k + 1) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
  exact ((summable_nat_add_iff 1).mpr hu).of_norm_bounded
    (fun k => barrierTrialS_term_norm_le u k hx)

theorem barrierTrialT_tendstoUniformlyOn (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) :
    TendstoUniformlyOn
      (fun m x => ∑ k ∈ Finset.range m,
        u (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ))
      (barrierTrialT u) atTop (Set.Icc (-1) 1) := by
  unfold barrierTrialT
  apply tendstoUniformlyOn_tsum_nat ((summable_nat_add_iff 1).mpr hu)
  intro k x hx
  exact barrierTrialT_term_norm_le u k (abs_le.mpr hx)

theorem barrierTrialS_tendstoUniformlyOn (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) :
    TendstoUniformlyOn
      (fun m x => ∑ k ∈ Finset.range m,
        u (k + 1) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ))
      (barrierTrialS u) atTop (Set.Icc (-1) 1) := by
  unfold barrierTrialS
  apply tendstoUniformlyOn_tsum_nat ((summable_nat_add_iff 1).mpr hu)
  intro k x hx
  exact barrierTrialS_term_norm_le u k (abs_le.mpr hx)

theorem barrier_trials_potentials_uniform {u : ℕ → ℝ}
    (hu : u ∈ [barrierP2, barrierV2, barrierP1, barrierV1]) :
    TendstoUniformlyOn
      (fun m x => ∑ k ∈ Finset.range m,
        u (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ))
      (barrierTrialT u) atTop (Set.Icc (-1) 1) ∧
    TendstoUniformlyOn
      (fun m x => ∑ k ∈ Finset.range m,
        u (k + 1) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ))
      (barrierTrialS u) atTop (Set.Icc (-1) 1) := by
  have hs : Summable (fun k => |u k|) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact barrier_trials_abs_summable.1
    · exact barrier_trials_abs_summable.2.1
    · exact barrier_trials_abs_summable.2.2.1
    · exact barrier_trials_abs_summable.2.2.2
  exact ⟨barrierTrialT_tendstoUniformlyOn u hs, barrierTrialS_tendstoUniformlyOn u hs⟩

end

section

open scoped BigOperators

theorem barrierTrialNormSq_nil_eq_sum (cs : List ℤ) :
    barrierTrialNormSq (barrierTrial cs []) =
      ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) ^ 2 / ((k + 1 : ℕ) : ℝ) := by
  unfold barrierTrialNormSq
  have heq (k : ℕ) : barrierTrial cs [] (k + 1) =
      (cs.getD k 0 : ℝ) / 100000000 := by
    simp [barrierTrial, barrierFiniteCoeff]
  simp_rw [heq]
  apply tsum_eq_sum
  intro k hk
  have hlen : cs.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
  rw [List.getD_eq_default cs 0 hlen]
  norm_num

theorem barrier_case1_norm_sharp_upper :
    barrierTrialNormSq barrierP1 + (1 / 2 : ℝ) * barrierTrialNormSq barrierV1 <
      (931985203901 / 1000000000000 : ℝ) := by
  change barrierTrialNormSq (barrierTrial barrierP1Finite []) +
      (1 / 2 : ℝ) * barrierTrialNormSq (barrierTrial barrierV1Finite []) < _
  rw [barrierTrialNormSq_nil_eq_sum, barrierTrialNormSq_nil_eq_sum]
  norm_num [barrierP1Finite, barrierV1Finite, Finset.sum_range_succ]

theorem barrier_case1_norm_coarse_upper :
    barrierTrialNormSq barrierP1 + (1 / 2 : ℝ) * barrierTrialNormSq barrierV1 <
      (9321 / 10000 : ℝ) := by
  exact barrier_case1_norm_sharp_upper.trans (by norm_num)

theorem barrierTrialNormSq_le_prefix_add_geometric_tail
    (u : ℕ → ℝ) (K : ℕ) (r B : ℝ)
    (hs : Summable (fun k : ℕ => u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)))
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hB : 0 ≤ B)
    (htail : ∀ j : ℕ, |u (j + K + 1)| ≤ B * r ^ j) :
    barrierTrialNormSq u ≤
      (∑ k ∈ Finset.range K, u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) +
        B ^ 2 / (((K + 1 : ℕ) : ℝ) * (1 - r ^ 2)) := by
  have hK : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
  have hr2 : r ^ 2 < 1 := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1.le)]
  have hshift : Summable (fun j : ℕ =>
      u (j + K + 1) ^ 2 / ((j + K + 1 : ℕ) : ℝ)) :=
    (summable_nat_add_iff K).mpr hs
  have hpoint (j : ℕ) :
      u (j + K + 1) ^ 2 / ((j + K + 1 : ℕ) : ℝ) ≤
        (B ^ 2 / ((K + 1 : ℕ) : ℝ)) * (r ^ 2) ^ j := by
    have hb : 0 ≤ B * r ^ j := mul_nonneg hB (pow_nonneg hr0 j)
    have hu : u (j + K + 1) ^ 2 ≤ (B * r ^ j) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (u (j + K + 1))) hb).mpr (htail j)
    have hd : ((K + 1 : ℕ) : ℝ) ≤ ((j + K + 1 : ℕ) : ℝ) := by
      simp only [Nat.cast_add, Nat.cast_one]
      linarith [show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j]
    have hpow : (r ^ j) ^ 2 = (r ^ 2) ^ j := by
      simp only [← pow_mul, Nat.mul_comm]
    calc
      _ ≤ (B * r ^ j) ^ 2 / ((j + K + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hu (Nat.cast_nonneg _)
      _ ≤ (B * r ^ j) ^ 2 / ((K + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hK hd
      _ = _ := by rw [mul_pow, hpow]; ring
  have hgeom := (hasSum_geometric_of_lt_one (sq_nonneg r) hr2).mul_left
    (B ^ 2 / ((K + 1 : ℕ) : ℝ))
  have hbound := hasSum_le hpoint hshift.hasSum hgeom
  have hsplit := Summable.sum_add_tsum_nat_add K hs
  unfold barrierTrialNormSq
  calc
    _ = (∑ k ∈ Finset.range K, u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) +
        ∑' j : ℕ, u (j + K + 1) ^ 2 / ((j + K + 1 : ℕ) : ℝ) := hsplit.symm
    _ ≤ (∑ k ∈ Finset.range K, u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) +
        (B ^ 2 / ((K + 1 : ℕ) : ℝ)) * (1 - r ^ 2)⁻¹ :=
      add_le_add le_rfl hbound
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

end
section

open Polynomial
open scoped BigOperators

theorem barrierTrialT_nil_eq_sum (cs : List ℤ) (x : ℝ) :
    barrierTrialT (barrierTrial cs []) x =
      ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) *
          (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ) := by
  unfold barrierTrialT
  have heq (k : ℕ) : barrierTrial cs [] (k + 1) =
      (cs.getD k 0 : ℝ) / 100000000 := by
    simp [barrierTrial, barrierFiniteCoeff]
  simp_rw [heq]
  apply tsum_eq_sum
  intro k hk
  have hlen : cs.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
  rw [List.getD_eq_default cs 0 hlen]
  norm_num

theorem barrierTrialS_nil_eq_sum (cs : List ℤ) (x : ℝ) :
    barrierTrialS (barrierTrial cs []) x =
      ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  unfold barrierTrialS
  have heq (k : ℕ) : barrierTrial cs [] (k + 1) =
      (cs.getD k 0 : ℝ) / 100000000 := by
    simp [barrierTrial, barrierFiniteCoeff]
  simp_rw [heq]
  apply tsum_eq_sum
  intro k hk
  have hlen : cs.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
  rw [List.getD_eq_default cs 0 hlen]
  norm_num

end

section

open Polynomial Set Filter
open scoped BigOperators

theorem barrierTrialT_continuousOn (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) :
    ContinuousOn (barrierTrialT u) (Icc (-1 : ℝ) 1) := by
  refine (barrierTrialT_tendstoUniformlyOn u hu).continuousOn (Frequently.of_forall ?_)
  intro m
  refine continuousOn_finsetSum _ (fun k _ => ?_)
  have hterm : Continuous (fun x : ℝ =>
      u (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x *
        (((k + 1 : ℕ) : ℝ)⁻¹)) :=
    (continuous_const.mul (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).continuous).mul
      continuous_const
  simpa only [div_eq_mul_inv] using hterm.continuousOn

theorem barrierTrialS_continuousOn (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|)) :
    ContinuousOn (barrierTrialS u) (Icc (-1 : ℝ) 1) := by
  refine (barrierTrialS_tendstoUniformlyOn u hu).continuousOn (Frequently.of_forall ?_)
  intro m
  refine continuousOn_finsetSum _ (fun k _ => ?_)
  have hterm : Continuous (fun x : ℝ =>
      u (k + 1) * x ^ (k + 1) * (((k + 1 : ℕ) : ℝ)⁻¹)) :=
    (continuous_const.mul (continuous_id.pow (k + 1))).mul continuous_const
  simpa only [div_eq_mul_inv] using hterm.continuousOn

end

open Polynomial

private theorem barrier_Tseries_term_hasDerivAt (a : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => a * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval y /
        ((k + 1 : ℕ) : ℝ))
      (a * (Chebyshev.U ℝ (k : ℤ)).eval x) x := by
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hindex : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by simp
  have ht : HasDerivAt
      (fun y : ℝ => (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval y)
      (((k + 1 : ℕ) : ℝ) * (Chebyshev.U ℝ (k : ℤ)).eval x) x := by
    simpa only [Chebyshev.T_derivative_eq_U, eval_mul, eval_intCast,
      hindex, Int.cast_natCast, eval_natCast] using
      (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).hasDerivAt x
  apply ((ht.const_mul a).div_const ((k + 1 : ℕ) : ℝ)).congr_deriv
  field_simp [hk]

private theorem barrier_Sseries_term_hasDerivAt (a : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => a * y ^ (k + 1) / ((k + 1 : ℕ) : ℝ))
      (a * x ^ k) x := by
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hp : HasDerivAt (fun y : ℝ => y ^ (k + 1))
      (((k + 1 : ℕ) : ℝ) * x ^ k) x := by
    simpa only [Nat.add_sub_cancel] using hasDerivAt_pow (k + 1) x
  apply ((hp.const_mul a).div_const ((k + 1 : ℕ) : ℝ)).congr_deriv
  field_simp [hk]

theorem barrierTrialT_hasDerivAt_series (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|))
    (huw : Summable (fun k : ℕ => (k : ℝ) * |u k|))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (barrierTrialT u)
      (∑' k : ℕ, u (k + 1) * (Chebyshev.U ℝ (k : ℤ)).eval x) x := by
  unfold barrierTrialT
  apply hasDerivAt_tsum_of_isPreconnected ((summable_nat_add_iff 1).mpr huw)
    isOpen_Ioo isPreconnected_Ioo
    (fun k y _ => barrier_Tseries_term_hasDerivAt (u (k + 1)) k y)
    _ (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1)
    (barrierTrialT_summable u hu (x := 0) (by norm_num)) hx
  intro k y hy
  have hyabs : |y| ≤ 1 := abs_le.mpr ⟨hy.1.le, hy.2.le⟩
  rw [norm_mul]
  simp only [Real.norm_eq_abs]
  calc
    |u (k + 1)| * |(Chebyshev.U ℝ (k : ℤ)).eval y| ≤
        |u (k + 1)| * ((k : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (barrierChebyshevU_abs_le k hyabs) (abs_nonneg _)
    _ = ((k + 1 : ℕ) : ℝ) * |u (k + 1)| := by push_cast; ring

theorem barrierTrialS_hasDerivAt_series (u : ℕ → ℝ)
    (hu : Summable (fun k => |u k|))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (barrierTrialS u) (∑' k : ℕ, u (k + 1) * x ^ k) x := by
  unfold barrierTrialS
  apply hasDerivAt_tsum_of_isPreconnected ((summable_nat_add_iff 1).mpr hu)
    isOpen_Ioo isPreconnected_Ioo
    (fun k y _ => barrier_Sseries_term_hasDerivAt (u (k + 1)) k y)
    _ (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1)
    (barrierTrialS_summable u hu (x := 0) (by norm_num)) hx
  intro k y hy
  have hyabs : |y| ≤ 1 := abs_le.mpr ⟨hy.1.le, hy.2.le⟩
  rw [norm_mul]
  simp only [Real.norm_eq_abs, abs_pow]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg y) hyabs : |y| ^ k ≤ 1)
      (abs_nonneg (u (k + 1)))

private theorem barrier_weighted_abs_summable_of_decay (u : ℕ → ℝ)
    (hu : ∀ k, |u k| ≤ 15 * (99 / 100 : ℝ) ^ k) :
    Summable (fun k : ℕ => (k : ℝ) * |u k|) := by
  have hg : Summable (fun k : ℕ => (15 : ℝ) * ((k : ℝ) * (99 / 100 : ℝ) ^ k)) := by
    simpa only [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one 1
        (by norm_num : ‖(99 / 100 : ℝ)‖ < 1)).mul_left (15 : ℝ)
  apply hg.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) * |u k|)]
  calc
    (k : ℝ) * |u k| ≤ (k : ℝ) * (15 * (99 / 100 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left (hu k) (Nat.cast_nonneg k)
    _ = 15 * ((k : ℝ) * (99 / 100 : ℝ) ^ k) := by ring

theorem barrier_trials_weighted_abs_summable :
    Summable (fun k : ℕ => (k : ℝ) * |barrierP2 k|) ∧
    Summable (fun k : ℕ => (k : ℝ) * |barrierV2 k|) ∧
    Summable (fun k : ℕ => (k : ℝ) * |barrierP1 k|) ∧
    Summable (fun k : ℕ => (k : ℝ) * |barrierV1 k|) := by
  exact ⟨barrier_weighted_abs_summable_of_decay _ (fun k => (barrier_trials_abs_le k).1),
    barrier_weighted_abs_summable_of_decay _ (fun k => (barrier_trials_abs_le k).2.1),
    barrier_weighted_abs_summable_of_decay _ (fun k => (barrier_trials_abs_le k).2.2.1),
    barrier_weighted_abs_summable_of_decay _ (fun k => (barrier_trials_abs_le k).2.2.2)⟩

open Polynomial
open scoped BigOperators

def barrierFiniteTRat (cs : List ℤ) (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℚ) / 100000000) *
    (Chebyshev.T ℚ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℚ)

def barrierFiniteSRat (cs : List ℤ) (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range cs.length,
    ((cs.getD k 0 : ℚ) / 100000000) * x ^ (k + 1) / ((k + 1 : ℕ) : ℚ)

theorem barrierTrialT_nil_eval_rat (cs : List ℤ) (x : ℚ) :
    barrierTrialT (barrierTrial cs []) (x : ℝ) = ((barrierFiniteTRat cs x : ℚ) : ℝ) := by
  have heval (n : ℤ) : (Chebyshev.T ℝ n).eval (x : ℝ) =
      (((Chebyshev.T ℚ n).eval x : ℚ) : ℝ) := by
    rw [← Chebyshev.map_T (Rat.castHom ℝ)]
    change ((Chebyshev.T ℚ n).map (Rat.castHom ℝ)).eval ((Rat.castHom ℝ) x) =
      (Rat.castHom ℝ) ((Chebyshev.T ℚ n).eval x)
    exact Polynomial.eval_map_apply (Rat.castHom ℝ) x
  rw [barrierTrialT_nil_eq_sum]
  unfold barrierFiniteTRat
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [heval]

theorem barrierTrialS_nil_eval_rat (cs : List ℤ) (x : ℚ) :
    barrierTrialS (barrierTrial cs []) (x : ℝ) = ((barrierFiniteSRat cs x : ℚ) : ℝ) := by
  rw [barrierTrialS_nil_eq_sum]
  unfold barrierFiniteSRat
  push_cast
  rfl

end InternalCatalan

end

end OAI
