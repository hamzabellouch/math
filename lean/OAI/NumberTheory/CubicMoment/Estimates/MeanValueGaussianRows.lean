import OAI.NumberTheory.CubicMoment.Estimates.MeanValueGaussianKernel
import Mathlib.Algebra.Order.Field.GeomSum

namespace OAI

/-! Uniform row sums for the Gaussian matrix on logarithmic frequencies. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma nat_dist_cast_eq_abs (m n : ℕ) : (Nat.dist m n:ℝ) = |(m:ℝ)-(n:ℝ)| := by
  by_cases h : m ≤ n
  · rw [Nat.dist_eq_sub_of_le h,Nat.cast_sub h,abs_of_nonpos (sub_nonpos.mpr (show (m:ℝ) ≤ n by exact_mod_cast h))]
    ring
  · have h' := le_of_not_ge h
    rw [Nat.dist_eq_sub_of_le_right h',Nat.cast_sub h',abs_of_nonneg (sub_nonneg.mpr (show (n:ℝ) ≤ m by exact_mod_cast h'))]

lemma geometric_nat_distance_sum {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (Z n : ℕ) (hn : n ≤ Z) :
    (∑ m ∈ Finset.Icc 1 Z, q^(Nat.dist n m)) ≤ 2/(1-q) := by
  let S := Finset.Icc 1 Z
  let A := S.filter (fun m => m ≤ n)
  let B := S.filter (fun m => ¬m ≤ n)
  have hgeom : (∑ d ∈ Finset.range (Z+1), q^d) ≤ 1/(1-q) := by
    simpa only [Nat.Ico_zero_eq_range,pow_zero] using
      (geom_sum_Ico_le_of_lt_one (m := 0) (n := Z+1) hq hq1)
  have hA : (∑ m ∈ A, q^(Nat.dist n m)) ≤ 1/(1-q) := by
    calc
      _ = ∑ m ∈ A, q^(n-m) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Nat.dist_eq_sub_of_le_right (Finset.mem_filter.mp hm).2]
      _ = ∑ d ∈ A.image (fun m => n-m), q^d := by
        symm
        apply Finset.sum_image
        intro m hm k hk he
        have hm' := (Finset.mem_filter.mp hm).2
        have hk' := (Finset.mem_filter.mp hk).2
        change n-m = n-k at he
        omega
      _ ≤ ∑ d ∈ Finset.range (Z+1), q^d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hd
          exact Finset.mem_range.mpr (by omega)
        · intro d _ _
          exact pow_nonneg hq _
      _ ≤ _ := hgeom
  have hB : (∑ m ∈ B, q^(Nat.dist n m)) ≤ 1/(1-q) := by
    calc
      _ = ∑ m ∈ B, q^(m-n) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Nat.dist_eq_sub_of_le (by have := (Finset.mem_filter.mp hm).2; omega)]
      _ = ∑ d ∈ B.image (fun m => m-n), q^d := by
        symm
        apply Finset.sum_image
        intro m hm k hk he
        have hm' := (Finset.mem_filter.mp hm).2
        have hk' := (Finset.mem_filter.mp hk).2
        change m-n = k-n at he
        omega
      _ ≤ ∑ d ∈ Finset.range (Z+1), q^d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hd
          have hmZ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
          exact Finset.mem_range.mpr (by omega)
        · intro d _ _
          exact pow_nonneg hq _
      _ ≤ _ := hgeom
  have he : (∑ m ∈ S, q^(Nat.dist n m)) =
      (∑ m ∈ A, q^(Nat.dist n m))+(∑ m ∈ B, q^(Nat.dist n m)) := by
    exact (Finset.sum_filter_add_sum_filter_not S (fun m => m ≤ n) _).symm
  change (∑ m ∈ S, q^(Nat.dist n m)) ≤ _
  rw [he]
  calc
    _ ≤ 1/(1-q)+1/(1-q) := add_le_add hA hB
    _ = _ := by ring

lemma gaussian_log_frequency_decay {Z n m : ℕ} (hn : n ∈ Finset.Icc 1 Z)
    (hm : m ∈ Finset.Icc 1 Z) {L : ℝ} (hL : (Z:ℝ) ≤ L) :
    Real.exp (-(L*(Real.log (n:ℝ)-Real.log (m:ℝ)))^2/4) ≤
      (Real.exp (-(1/4:ℝ)))^(Nat.dist n m) := by
  have hdist : 0 ≤ (Nat.dist n m:ℝ) := by positivity
  have hsep : (Nat.dist n m:ℝ) ≤ L*|Real.log (n:ℝ)-Real.log (m:ℝ)| := by
    rw [nat_dist_cast_eq_abs]
    exact (integer_log_frequency_spacing hn hm).trans
      (mul_le_mul_of_nonneg_right hL (abs_nonneg _))
  have hnat : (Nat.dist n m:ℝ) ≤ (Nat.dist n m:ℝ)^2 := by
    have hn' : Nat.dist n m ≤ Nat.dist n m*Nat.dist n m := by
      generalize Nat.dist n m = d
      by_cases hd : d = 0
      · simp [hd]
      · have : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
        nlinarith
    simpa only [pow_two] using (show (Nat.dist n m:ℝ) ≤ (Nat.dist n m:ℝ)*(Nat.dist n m:ℝ) by exact_mod_cast hn')
  have hL0 : 0 ≤ L := le_trans (Nat.cast_nonneg Z) hL
  have hsquare : (Nat.dist n m:ℝ)^2 ≤ (L*(Real.log (n:ℝ)-Real.log (m:ℝ)))^2 := by
    have h := sq_le_sq₀ hdist (mul_nonneg hL0 (abs_nonneg _)) |>.mpr hsep
    simpa only [mul_pow,sq_abs] using h
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  nlinarith

lemma gaussian_log_frequency_row_bound {Z n : ℕ} (hn : n ∈ Finset.Icc 1 Z)
    {L : ℝ} (hL : (Z:ℝ) ≤ L) :
    (∑ m ∈ Finset.Icc 1 Z,
      Real.exp (-(L*(Real.log (n:ℝ)-Real.log (m:ℝ)))^2/4)) ≤
      2/(1-Real.exp (-(1/4:ℝ))) := by
  apply (Finset.sum_le_sum (fun m hm => gaussian_log_frequency_decay hn hm hL)).trans
  exact geometric_nat_distance_sum (Real.exp_pos _).le
    (by rw [Real.exp_lt_one_iff]; norm_num) Z n (Finset.mem_Icc.mp hn).2

end CubicFirstMoment

end

end OAI
