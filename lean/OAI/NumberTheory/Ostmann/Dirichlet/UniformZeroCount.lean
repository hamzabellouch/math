import OAI.NumberTheory.Jacobsthal.Primes.DirichletZeroPenalty
import OAI.NumberTheory.Ostmann.Dirichlet.GrowthIntegral
import OAI.NumberTheory.Ostmann.Dirichlet.LocalZeroCount

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

open Set MeasureTheory
open scoped Topology

namespace Ostmann.Dirichlet

lemma local_strip_mem_disk (t : ℝ) {ρ : ℂ} (hlo : 1 / 2 ≤ ρ.re)
    (hhi : ρ.re ≤ 1) (him : |ρ.im - t| ≤ 1 / 2) :
    ρ ∈ Metric.closedBall (dirichletCenter t) (13 / 5) := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have he : ‖ρ - dirichletCenter t‖ ^ 2 = (ρ.re - 3) ^ 2 + (ρ.im - t) ^ 2 := by
    simp [Complex.sq_norm, Complex.normSq_apply, dirichletCenter]
    ring
  obtain ⟨himlo, himhi⟩ := abs_le.mp him
  have hre : (ρ.re - 3) ^ 2 ≤ (5 / 2 : ℝ) ^ 2 := by nlinarith
  have hi : (ρ.im - t) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
  nlinarith [norm_nonneg (ρ - dirichletCenter t)]

lemma norm_LFunction_disk_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ)
    {z : ℂ} (hz : z ∈ Metric.closedBall (dirichletCenter t) (11 / 4)) :
    ‖χ.LFunction z‖ ≤ 4 * q * (|t| + 6) := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have hre : 1 / 4 ≤ z.re := by
    have h := (abs_le.mp ((Complex.abs_re_le_norm (z - dirichletCenter t)).trans hz)).1
    simp only [Complex.sub_re, dirichletCenter_re] at h
    linarith
  have hrep : 0 < z.re := by linarith
  have hc : ‖dirichletCenter t‖ ≤ 3 + |t| := by
    simpa [dirichletCenter, norm_mul] using norm_add_le (3 : ℂ) ((t : ℂ) * Complex.I)
  have hnorm : ‖z‖ ≤ |t| + 6 := by
    have h := norm_add_le (z - dirichletCenter t) (dirichletCenter t)
    rw [sub_add_cancel] at h
    linarith
  calc
    ‖χ.LFunction z‖ ≤ q * ‖z‖ / z.re := norm_LFunction_le_partial_sum_bound χ hχ hrep
    _ ≤ 4 * q * ‖z‖ := by
      apply (div_le_iff₀ hrep).mpr
      have hn : 0 ≤ (q : ℝ) * ‖z‖ := by positivity
      nlinarith
    _ ≤ 4 * q * (|t| + 6) := mul_le_mul_of_nonneg_left hnorm (by positivity)

theorem local_zero_count_le_log {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, 1 / 2 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - t| ≤ 1 / 2) :
    (∑ ρ ∈ S, (zeroMultiplicity χ ρ : ℝ)) ≤
      Real.log (4 * absoluteZetaTwo * q * (|t| + 6)) / Real.log (55 / 52) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have ht : 0 ≤ |t| := abs_nonneg t
  have hM : 1 ≤ 4 * (q : ℝ) * (|t| + 6) := by nlinarith
  have hcp : 0 < ‖χ.LFunction (dirichletCenter t)‖ :=
    norm_pos_iff.mpr (LFunction_ne_zero_right χ (by simp))
  have hj := sum_zeroMultiplicity_le_jensen χ hχ S
    (c := dirichletCenter t) (r := 13 / 5) (R := 11 / 4)
    (M := 4 * q * (|t| + 6)) (by norm_num) (by norm_num) hM
    (LFunction_ne_zero_right χ (by simp))
    (fun ρ hρ => local_strip_mem_disk t (hS ρ hρ).1 (hS ρ hρ).2.1 (hS ρ hρ).2.2)
    (fun z hz => norm_LFunction_disk_bound χ hχ t (Metric.sphere_subset_closedBall hz))
  norm_num only [show (11 / 4 : ℝ) / (13 / 5) = 55 / 52 by norm_num] at hj
  apply hj.trans
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 55 / 52)).le
  apply Real.log_le_log (div_pos (by linarith : 0 < 4 * (q : ℝ) * (|t| + 6)) hcp)
  have hi := norm_inv_LFunction_le_absoluteZetaTwo χ (s := dirichletCenter t) (by norm_num)
  rw [norm_inv] at hi
  have hmul := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 4 * (q : ℝ) * (|t| + 6))
  simpa only [div_eq_mul_inv] using hmul.trans_eq (by ring)

end Ostmann.Dirichlet

end OAI
