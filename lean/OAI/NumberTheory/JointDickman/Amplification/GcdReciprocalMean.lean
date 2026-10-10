import OAI.NumberTheory.JointDickman.Arithmetic.DivisorSumReindex

namespace OAI

/-! # A logarithmic bound for a gcd-weighted reciprocal-square sum -/
namespace JointDickman
open Finset

lemma reciprocal_square_initial_sum (X : ℕ) :
    (∑ k ∈ Ioc 0 X, 1/(k:ℝ)^2) ≤ 2 := by
  have he : Ioc 0 X = Ioo 0 (X+1) := by
    ext k
    simp only [mem_Ioc,mem_Ioo]
    omega
  rw [he]
  simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (X+1))

lemma reciprocal_initial_sum (q : ℕ) :
    (∑ r ∈ Ioc 0 q, 1/(r:ℝ)) ≤ 1+Real.log q := by
  have he : Ioc 0 q = Icc 1 q := by
    ext r
    simp only [mem_Ioc,mem_Icc]
    omega
  rw [he]
  simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div] using
    harmonic_le_one_add_log q

theorem gcd_reciprocal_square_sum (q X : ℕ) (hq : 0 < q) :
    (∑ d ∈ Ioc 0 X, (Nat.gcd d q:ℝ)/(d:ℝ)^2) ≤ 2*(1+Real.log q) := by
  have hpoint (d : ℕ) (hd : d ∈ Ioc 0 X) :
      (Nat.gcd d q:ℝ)/(d:ℝ)^2 ≤
        ∑ r ∈ d.divisors, if r ≤ q then (r:ℝ)/(r*(d/r):ℕ)^2 else 0 := by
    have hd0 := (mem_Ioc.mp hd).1
    have hg : Nat.gcd d q ∈ d.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _,hd0.ne'⟩
    have hgq : Nat.gcd d q ≤ q := Nat.le_of_dvd hq (Nat.gcd_dvd_right _ _)
    have hsum : (Nat.gcd d q:ℝ) ≤ ∑ r ∈ d.divisors, if r ≤ q then (r:ℝ) else 0 := by
      have hs := single_le_sum (s := d.divisors) (f := fun r => if r ≤ q then (r:ℝ) else 0)
        (fun r hr => by split_ifs <;> positivity) hg
      simpa only [ite_eq_left hgq] using hs
    calc
      _ ≤ (∑ r ∈ d.divisors, if r ≤ q then (r:ℝ) else 0)/(d:ℝ)^2 :=
        div_le_div_of_nonneg_right hsum (sq_nonneg _)
      _ = _ := by
        rw [sum_div]
        apply sum_congr rfl
        intro r hr
        rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hr)]
        split_ifs <;> simp
  have hmain := sum_le_sum hpoint
  rw [sum_Ioc_divisors_reindex (fun r k => if r ≤ q then (r:ℝ)/(r*k:ℕ)^2 else 0)] at hmain
  have hinner (r : ℕ) (hr : r ∈ Ioc 0 X) :
      (∑ k ∈ Ioc 0 (X/r), if r ≤ q then (r:ℝ)/(r*k:ℕ)^2 else 0) ≤
        if r ≤ q then 2/(r:ℝ) else 0 := by
    by_cases hrq : r ≤ q
    · simp only [ite_eq_left hrq]
      have hr0 : (r:ℝ) ≠ 0 := by exact_mod_cast (mem_Ioc.mp hr).1.ne'
      have he (k : ℕ) : (r:ℝ)/(r*k:ℕ)^2 = (1/(r:ℝ))*(1/(k:ℝ)^2) := by
        push_cast
        field_simp
      simp_rw [he]
      rw [←mul_sum]
      have hh := mul_le_mul_of_nonneg_left (reciprocal_square_initial_sum (X/r))
        (show 0 ≤ 1/(r:ℝ) by positivity)
      convert hh using 1
      ring
    · simp [hrq]
  have hsum : (∑ r ∈ Ioc 0 X, if r ≤ q then 2/(r:ℝ) else 0) ≤
      2*(1+Real.log q) := by
    rw [←sum_filter]
    have hsub : (Ioc 0 X).filter (fun r => r ≤ q) ⊆ Ioc 0 q := by
      intro r hr
      exact mem_Ioc.mpr ⟨(mem_Ioc.mp (mem_filter.mp hr).1).1,(mem_filter.mp hr).2⟩
    calc
      _ ≤ ∑ r ∈ Ioc 0 q, 2/(r:ℝ) := sum_le_sum_of_subset_of_nonneg hsub
        (fun r _ _ => by positivity)
      _ = 2*(∑ r ∈ Ioc 0 q, 1/(r:ℝ)) := by simp only [mul_sum,mul_one_div]
      _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_initial_sum q) (by norm_num)
  exact hmain.trans ((sum_le_sum hinner).trans hsum)

end JointDickman

end OAI
