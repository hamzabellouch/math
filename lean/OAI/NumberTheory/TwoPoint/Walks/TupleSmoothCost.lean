import OAI.NumberTheory.TwoPoint.Bounds.SmoothProductBounds
import OAI.NumberTheory.TwoPoint.Walks.CanonicalRoughScale

namespace OAI

/-! The retained tuple introduces at most a factor two into the smooth
Euler cost, because all its primes lie above the canonical lower endpoint. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Topology

lemma smooth_half_cost_of_large_factors (P : Finset ℕ) (L : ℝ)
    (hL : 2 ≤ L) (hcard : (P.card : ℝ) ≤ L)
    (hlarge : ∀ p ∈ P, L ^ (4 : ℕ) ≤ (p : ℝ))
    (hlog : 2 / L ≤ Real.log 2) :
    smoothReciprocalProduct P (1 / 2 : ℝ) ≤ 2 := by
  have hLp : 0 < L := by linarith
  have hterm : ∀ p ∈ P, (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ L ^ (-2 : ℝ) := by
    intro p hp
    have hh := Real.rpow_le_rpow_of_nonpos (pow_pos hLp 4) (hlarge p hp)
      (show (-(1 / 2) : ℝ) ≤ 0 by norm_num)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLp.le] at hh
    norm_num at hh ⊢
    exact hh
  have hs : L ^ (-2 : ℝ) ≤ 1 / 2 := by
    rw [Real.rpow_neg hLp.le, Real.rpow_two]
    apply (inv_le_comm₀ (sq_pos_of_pos hLp) (by norm_num)).mpr
    nlinarith
  apply smooth_half_product_le_two P (fun p hp => (hterm p hp).trans hs)
  calc
    2 * ∑ p ∈ P, (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ 2 * ((P.card : ℝ) * L ^ (-2 : ℝ)) := by
      gcongr
      exact (sum_le_sum hterm).trans_eq (by simp)
    _ ≤ 2 * (L * L ^ (-2 : ℝ)) := by gcongr
    _ = 2 / L := by rw [Real.rpow_neg hLp.le, Real.rpow_two]; field_simp
    _ ≤ Real.log 2 := hlog

lemma eventually_canonical_smooth_half_cost :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, (P.card : ℝ) ≤ L →
      (∀ p ∈ P, Real.exp (L ^ (199 / 200 : ℝ)) ≤ (p : ℝ)) →
      smoothReciprocalProduct P (1 / 2 : ℝ) ≤ 2 := by
  have hs := (isLittleO_log_rpow_atTop (show 0 < (199 / 200 : ℝ) by norm_num)).bound
    (show 0 < (1 / 4 : ℝ) by norm_num)
  have hl : Tendsto (fun L : ℝ => 2 / L) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop 2
  filter_upwards [hs, hl.eventually (gt_mem_nhds (Real.log_pos (by norm_num : (1 : ℝ) < 2))),
    eventually_ge_atTop 2] with L hs hl hL
  intro P hcard hlarge
  have hLp : 0 < L := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith)),
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hLp _)] at hs
  apply smooth_half_cost_of_large_factors P L hL hcard _ hl.le
  intro p hp
  calc
    L ^ (4 : ℕ) = Real.exp (4 * Real.log L) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hLp]
      congr 1
      ring
    _ ≤ Real.exp (L ^ (199 / 200 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ (p : ℝ) := hlarge p hp

lemma dilated_tuple_smooth_cost (q t : ℕ) (hq : 0 < q) (ht : 0 < t)
    (htcost : smoothReciprocalProduct t.primeFactors (1 / 2 : ℝ) ≤ 2) :
    smoothReciprocalProduct (q * t).primeFactors (1 / 2 : ℝ) ≤
      2 * smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) := by
  calc
    _ ≤ smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) *
        smoothReciprocalProduct t.primeFactors (1 / 2 : ℝ) :=
      smoothReciprocalProduct_mul_le q t hq ht _ (by norm_num)
    _ ≤ smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left htcost (smoothReciprocalProduct_nonneg _
        (fun _ hp => Nat.prime_of_mem_primeFactors hp) _ (by norm_num))
    _ = _ := mul_comm _ _

end TwoPointCorrelations

end OAI
