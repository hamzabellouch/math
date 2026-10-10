import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI

universe uE

noncomputable section

namespace PeriodicTilingThree

open Finset Filter
open scoped Topology

def complexAverage (u : ℕ → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ range N, u n

def vectorAverage {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → E) (N : ℕ) : E :=
  (N : ℝ)⁻¹ • ∑ n ∈ range N, u n

theorem complexAverage_eq_vectorAverage (u : ℕ → ℂ) (N : ℕ) :
    complexAverage u N = vectorAverage u N := by
  simp only [complexAverage, vectorAverage, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_natCast]

@[simp] theorem complexAverage_zero (u : ℕ → ℂ) : complexAverage u 0 = 0 := by
  simp [complexAverage]

theorem complexAverage_add (u v : ℕ → ℂ) (N : ℕ) :
    complexAverage (fun n => u n + v n) N = complexAverage u N + complexAverage v N := by
  simp only [complexAverage, Finset.sum_add_distrib, mul_add]

theorem complexAverage_sub (u v : ℕ → ℂ) (N : ℕ) :
    complexAverage (fun n => u n - v n) N = complexAverage u N - complexAverage v N := by
  simp only [complexAverage, Finset.sum_sub_distrib, mul_sub]

theorem complexAverage_const (c : ℂ) {N : ℕ} (hN : N ≠ 0) :
    complexAverage (fun _ => c) N = c := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp only [complexAverage, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hNc, one_mul]

theorem complexAverage_mul_const (u : ℕ → ℂ) (c : ℂ) (N : ℕ) :
    complexAverage (fun n => u n * c) N = complexAverage u N * c := by
  simp only [complexAverage, ← Finset.sum_mul, mul_assoc]

theorem complexAverage_const_mul (u : ℕ → ℂ) (c : ℂ) (N : ℕ) :
    complexAverage (fun n => c * u n) N = c * complexAverage u N := by
  simp only [complexAverage, ← Finset.mul_sum]
  ring

theorem norm_complexAverage (u : ℕ → ℂ) (N : ℕ) :
    ‖complexAverage u N‖ = (N : ℝ)⁻¹ * ‖∑ n ∈ range N, u n‖ := by
  simp only [complexAverage, norm_mul, norm_inv, Complex.norm_natCast]

theorem norm_complexAverage_le (u : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ n, ‖u n‖ ≤ C) (N : ℕ) : ‖complexAverage u N‖ ≤ C := by
  by_cases hN : N = 0
  · simpa [hN] using hC
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hs : ‖∑ n ∈ range N, u n‖ ≤ (N : ℝ) * C := by
    calc
      _ ≤ ∑ n ∈ range N, ‖u n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ range N, C := Finset.sum_le_sum fun n _ => hu n
      _ = (N : ℝ) * C := by simp
  rw [norm_complexAverage]
  calc
    _ ≤ (N : ℝ)⁻¹ * ((N : ℝ) * C) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = C := by rw [← mul_assoc, inv_mul_cancel₀ hNr, one_mul]

theorem norm_geometric_sum_le (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (N : ℕ) :
    ‖∑ n ∈ range N, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hz1, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]

theorem complexAverage_geometric_tendsto (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (complexAverage (fun n => z ^ n)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hb : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (2 / ‖z - 1‖)) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      tendsto_inv_atTop_nhds_zero_nat.mul_const (2 / ‖z - 1‖)
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hb
  rw [norm_complexAverage]
  exact mul_le_mul_of_nonneg_left (norm_geometric_sum_le z hz hz1 N) (by positivity)

theorem complexAverage_const_mul_geometric_tendsto (c z : ℂ)
    (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    Tendsto (complexAverage (fun n => c * z ^ n)) atTop (𝓝 0) := by
  have hfun : complexAverage (fun n => c * z ^ n) =
      fun N => c * complexAverage (fun n => z ^ n) N := by
    funext N
    exact complexAverage_const_mul (fun n => z ^ n) c N
  rw [hfun]
  simpa only [mul_zero] using
    (complexAverage_geometric_tendsto z hz hz1).const_mul c

end PeriodicTilingThree

end

end OAI
