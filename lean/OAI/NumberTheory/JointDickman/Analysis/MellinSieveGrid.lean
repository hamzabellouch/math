import OAI.NumberTheory.JointDickman.Amplification.LipschitzRiemannSum
import OAI.NumberTheory.JointDickman.Analysis.MellinSieveIntegral
import OAI.NumberTheory.JointDickman.Analysis.MellinSieveRemainder

namespace OAI

/-! # Direct divisor-grid approximation for the Mellin sieve kernel -/
namespace JointDickman
open Finset MeasureTheory

lemma sum_grid_eq_filter {E : Type*} [AddCommMonoid E] (f : ℕ → E)
    (K d : ℕ) (hd : 0 < d) :
    (∑ m ∈ range (K/d), f (d*(m+1))) =
      ∑ n ∈ (Icc 1 K).filter (fun n => d ∣ n), f n := by
  rw [riemann_sum_range_succ_eq_Icc (fun m => f (d*m))]
  apply sum_bij (fun m _ => d*m)
  · intro m hm
    obtain ⟨hm1, hmK⟩ := mem_Icc.mp hm
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨by nlinarith, ?_⟩, dvd_mul_right _ _⟩
    have hh := (Nat.le_div_iff_mul_le hd).mp hmK
    simpa only [Nat.mul_comm] using hh
  · intro m hm n hn he
    exact Nat.eq_of_mul_eq_mul_left hd he
  · intro n hn
    obtain ⟨hnK, hdn⟩ := mem_filter.mp hn
    obtain ⟨hn1, hnK⟩ := mem_Icc.mp hnK
    have he : d*(n/d) = n := Nat.mul_div_cancel' hdn
    refine ⟨n/d, mem_Icc.mpr ⟨?_, Nat.div_le_div_right hnK⟩, he⟩
    have hdle := Nat.le_of_dvd (by omega : 0 < n) hdn
    exact Nat.div_pos hdle hd
  · intro m hm
    rfl

lemma mellinSieve_grid_riemann {N d : ℝ} (hN : 0 < N) (hd : 0 < d)
    (M : ℕ) (t : ℝ) :
    ‖(∑ m ∈ range M, mellinSieveFunction N t (d*(m+1))) -
      (d⁻¹ : ℂ)*(∫ x in (0:ℝ)..d*M, mellinSieveFunction N t x)‖ ≤
        (M:ℝ)*d*((3+|t|)/N) := by
  have hh := lipschitz_riemann_sum_error
    (fun x => mellinSieveFunction N t (d*x)) M
    (L := d*((3+|t|)/N)) (by positivity) (by
      intro x hx y hy
      have hb := mellinSieveFunction_sub hN (mul_nonneg hd.le hx.1)
        (mul_nonneg hd.le hy.1) t
      rw [← mul_sub, abs_mul, abs_of_pos hd] at hb
      exact hb.trans_eq (by ring))
  rw [intervalIntegral.integral_comp_mul_left (f := mellinSieveFunction N t) hd.ne', mul_zero,
    Complex.real_smul] at hh
  simpa only [mul_assoc, Complex.ofReal_inv] using hh

/-- The low-frequency kernel error, with the actual rounded divisor-grid
endpoint exposed. It is uniform in the divisor and in the frequency. -/
theorem mellinSieve_grid_error {N : ℝ} (hN : 0 < N) (K d : ℕ) (hd : 0 < d)
    (hB : N ≤ (d:ℝ)*(K/d:ℕ)) (t : ℝ) :
    ‖mellinSieveDiscreteKernel K d N t-mellinSieveMainKernel N t/(d:ℂ)‖ ≤
      (K/d:ℕ)*(d:ℝ)*((3+|t|)/N) + N^3/((d:ℝ)*2*((d:ℝ)*(K/d:ℕ))^2) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have he : mellinSieveDiscreteKernel K d N t =
      ∑ m ∈ range (K/d), mellinSieveFunction N t ((d:ℝ)*(m+1)) := by
    unfold mellinSieveDiscreteKernel mellinSampleKernel
    change (∑ n ∈ (Icc 1 K).filter (fun n => d ∣ n), mellinSieveFunction N t n) = _
    rw [← sum_grid_eq_filter (fun n => mellinSieveFunction N t n) K d hd]
    apply sum_congr rfl
    intro m hm
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [he]
  have hg := mellinSieve_grid_riemann hN hdR (K/d) t
  have ht := mellinSieveFunction_integral_error hN hB t
  let I : ℂ := ∫ x in (0:ℝ)..(d:ℝ)*(K/d:ℕ), mellinSieveFunction N t x
  calc
    _ ≤ ‖(∑ m ∈ range (K/d), mellinSieveFunction N t ((d:ℝ)*(m+1))) - (d:ℂ)⁻¹*I‖ +
        ‖(d:ℂ)⁻¹*I-mellinSieveMainKernel N t/(d:ℂ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (K/d:ℕ)*(d:ℝ)*((3+|t|)/N) + N^3/((d:ℝ)*2*((d:ℝ)*(K/d:ℕ))^2) := by
      apply add_le_add hg
      rw [div_eq_mul_inv, mul_comm (mellinSieveMainKernel N t), ← mul_sub,
        norm_mul, norm_inv, Complex.norm_natCast]
      have hh := mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr hdR.le)
      exact hh.trans_eq (by ring)

end JointDickman

end OAI
