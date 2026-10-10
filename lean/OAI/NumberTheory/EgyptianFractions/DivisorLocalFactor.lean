import Mathlib

namespace OAI
namespace Problem337.DivisorMoment

/-- Polynomially weighted geometric series, with the indexing used by the
nonconstant terms of an Euler factor. -/
theorem summable_shifted_pow_geometric (r : ℕ) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Summable (fun j : ℕ => ((j : ℝ) + 2) ^ r * ρ ^ j) := by
  have hn : ‖ρ‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos hρ0] using hρ1
  have hbase := summable_pow_mul_geometric_of_norm_lt_one r hn
  have hshift := (summable_nat_add_iff 2).mpr hbase
  have hscaled := hshift.mul_left ((ρ ^ 2)⁻¹)
  apply hscaled.congr
  intro j
  simp only [Nat.cast_add, Nat.cast_ofNat, pow_add]
  field_simp

/-- All nonconstant coefficients of the Euler factor have a uniform linear
majorant on any fixed compact subinterval of the geometric convergence disk. -/
theorem local_factor_linear_bound (r : ℕ) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x → x ≤ ρ →
      Summable (fun j : ℕ => ((j : ℝ) + 2) ^ r * x ^ (j + 1)) ∧
      (∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1)) ≤ C * x ∧
      Real.log (1 + ∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1)) ≤ C * x := by
  let A : ℝ := ∑' j : ℕ, ((j : ℝ) + 2) ^ r * ρ ^ j
  have hA0 : 0 ≤ A := tsum_nonneg (fun j => by positivity)
  have hsρ := summable_shifted_pow_geometric r hρ0 hρ1
  refine ⟨A + 1, by positivity, ?_⟩
  intro x hx0 hxρ
  have hle : ∀ j : ℕ, ((j : ℝ) + 2) ^ r * x ^ j ≤
      ((j : ℝ) + 2) ^ r * ρ ^ j := by
    intro j
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hxρ j) (by positivity)
  have hsx : Summable (fun j : ℕ => ((j : ℝ) + 2) ^ r * x ^ j) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hle hsρ
  have hsum : (∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ j) ≤ A :=
    Summable.tsum_le_tsum hle hsx hsρ
  have hsnext : Summable (fun j : ℕ => ((j : ℝ) + 2) ^ r * x ^ (j + 1)) := by
    simpa only [pow_succ, mul_assoc] using hsx.mul_right x
  have heq : (∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1)) =
      (∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ j) * x := by
    simpa only [pow_succ, mul_assoc] using hsx.tsum_mul_right x
  have hbound : (∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1)) ≤ (A + 1) * x := by
    rw [heq]
    exact mul_le_mul_of_nonneg_right (hsum.trans (by linarith)) hx0
  refine ⟨hsnext, hbound, ?_⟩
  have hnonneg : 0 ≤ ∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1) :=
    tsum_nonneg (fun j => by positivity)
  have hlog := Real.log_le_sub_one_of_pos (by linarith :
    0 < 1 + ∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1))
  linarith

/-- Real moments are reduced to a larger integral moment, uniformly in x. -/
theorem local_factor_real_moment_bound (r : ℝ) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x → x ≤ ρ →
      Summable (fun j : ℕ => ((j : ℝ) + 2) ^ r * x ^ (j + 1)) ∧
      (∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1)) ≤ C * x ∧
      Real.log (1 + ∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1)) ≤ C * x := by
  obtain ⟨R, hR⟩ := exists_nat_gt r
  obtain ⟨C, hC, hbound⟩ := local_factor_linear_bound R hρ0 hρ1
  refine ⟨C, hC, ?_⟩
  intro x hx0 hxρ
  obtain ⟨hsR, hsumR, _⟩ := hbound x hx0 hxρ
  have hle : ∀ j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1) ≤
      ((j : ℝ) + 2) ^ R * x ^ (j + 1) := by
    intro j
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by have hj := Nat.cast_nonneg (α := ℝ) j; linarith) hR.le
  have hs : Summable (fun j : ℕ => ((j : ℝ) + 2) ^ r * x ^ (j + 1)) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hle hsR
  have hsum : (∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1)) ≤ C * x :=
    (Summable.tsum_le_tsum hle hs hsR).trans hsumR
  refine ⟨hs, hsum, ?_⟩
  have hnonneg : 0 ≤ ∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1) :=
    tsum_nonneg (fun j => by positivity)
  have hlog := Real.log_le_sub_one_of_pos (by linarith :
    0 < 1 + ∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1))
  linarith

/-- Uniform local Euler-factor bound. Primality is unnecessary; p≥2 is enough.
The range σ≤1 can also be omitted from this local estimate. -/
theorem divisor_local_factor_bound (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p σ : ℝ, 2 ≤ p → (3 / 4 : ℝ) ≤ σ →
      Summable (fun j : ℕ => ((j : ℝ) + 2) ^ r * (p ^ (-σ)) ^ (j + 1)) ∧
      Real.log (1 + ∑' j : ℕ, ((j : ℝ) + 2) ^ r * (p ^ (-σ)) ^ (j + 1)) ≤
        C * p ^ (-σ) := by
  let ρ : ℝ := (2 : ℝ) ^ (-(3 / 4 : ℝ))
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  obtain ⟨C, hC, hbound⟩ := local_factor_real_moment_bound r hρ0 hρ1
  refine ⟨C, hC, ?_⟩
  intro p σ hp hσ
  have hx0 : 0 ≤ p ^ (-σ) := (Real.rpow_pos_of_pos (by linarith : 0 < p) _).le
  have hxρ : p ^ (-σ) ≤ ρ := by
    calc
      p ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hp (by linarith)
      _ ≤ (2 : ℝ) ^ (-(3 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  obtain ⟨hs, _, hl⟩ := hbound (p ^ (-σ)) hx0 hxρ
  exact ⟨hs, hl⟩

/-- Convert the shifted nonconstant series to the full Euler factor and
all its finite partial sums. -/
theorem full_local_factor_bounds {r x B : ℝ} (hx : 0 ≤ x)
    (hs : Summable (fun j : ℕ => ((j : ℝ) + 2) ^ r * x ^ (j + 1)))
    (hlog : Real.log (1 + ∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1)) ≤ B) :
    Summable (fun j : ℕ => ((j : ℝ) + 1) ^ r * x ^ j) ∧
    Real.log (∑' j : ℕ, ((j : ℝ) + 1) ^ r * x ^ j) ≤ B ∧
    ∀ L : ℕ, Real.log (∑ j ∈ Finset.range (L + 1),
      ((j : ℝ) + 1) ^ r * x ^ j) ≤ B := by
  have hsfull : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ r * x ^ j) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hs
  have hfull : Real.log (∑' j : ℕ, ((j : ℝ) + 1) ^ r * x ^ j) ≤ B := by
    rw [hsfull.tsum_eq_zero_add]
    simpa only [Nat.cast_zero, zero_add, Real.one_rpow, pow_zero, one_mul,
      Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hlog
  refine ⟨hsfull, hfull, ?_⟩
  intro L
  have hpos : 0 < ∑ j ∈ Finset.range (L + 1), ((j : ℝ) + 1) ^ r * x ^ j := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, pow_zero, one_mul]
    have hn : 0 ≤ ∑ j ∈ Finset.range L, (((j + 1 : ℕ) : ℝ) + 1) ^ r * x ^ (j + 1) :=
      Finset.sum_nonneg (fun j _ => by positivity)
    linarith
  exact (Real.log_le_log hpos
    (hsfull.sum_le_tsum (Finset.range (L + 1)) (fun j _ => by positivity))).trans hfull

/-- Full and finite Euler factors, with a uniform constant for every real
moment and every σ≥3/4. This is convenient for both finite and infinite
Euler-product arguments. -/
theorem divisor_full_local_factor_bound (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p σ : ℝ, 2 ≤ p → (3 / 4 : ℝ) ≤ σ →
      Summable (fun j : ℕ => ((j : ℝ) + 1) ^ r * (p ^ (-σ)) ^ j) ∧
      Real.log (∑' j : ℕ, ((j : ℝ) + 1) ^ r * (p ^ (-σ)) ^ j) ≤ C * p ^ (-σ) ∧
      ∀ L : ℕ, Real.log (∑ j ∈ Finset.range (L + 1),
        ((j : ℝ) + 1) ^ r * (p ^ (-σ)) ^ j) ≤ C * p ^ (-σ) := by
  obtain ⟨C, hC, hfactor⟩ := divisor_local_factor_bound r
  refine ⟨C, hC, ?_⟩
  intro p σ hp hσ
  obtain ⟨hs, hl⟩ := hfactor p σ hp hσ
  exact full_local_factor_bounds (Real.rpow_nonneg (by linarith) _) hs hl

end Problem337.DivisorMoment

end OAI
