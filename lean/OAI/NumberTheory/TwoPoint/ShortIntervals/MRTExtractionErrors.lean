import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogClassData

namespace OAI

/-! The prime-square and coarse-bin errors sum independently of the
number of MRT bands. The only input is their actual lower endpoints. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_finite_reciprocal_square_tail (S : Finset ℕ) {y : ℝ} (hy : 1 ≤ y)
    (hS : ∀ n ∈ S, y ≤ (n:ℝ)) : (∑ n ∈ S, 1/(n:ℝ)^2) ≤ 2/y := by
  let k := ⌈y⌉₊-1
  have hc : 1 ≤ ⌈y⌉₊ := by
    exact_mod_cast hy.trans (Nat.le_ceil y)
  have hk : k+1 = ⌈y⌉₊ := by dsimp [k]; omega
  have hsub : S ⊆ Ioo k (S.sup id+1) := by
    intro n hn
    have hcn : ⌈y⌉₊ ≤ n := Nat.ceil_le.mpr (hS n hn)
    exact mem_Ioo.mpr ⟨by dsimp [k]; omega, Nat.lt_succ_of_le (le_sup (f := id) hn)⟩
  calc
    _ ≤ ∑ n ∈ Ioo k (S.sup id+1), ((n:ℝ)^2)⁻¹ := by
      simp only [one_div]
      exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 2/((k:ℝ)+1) := sum_Ioo_inv_sq_le (α := ℝ) k (S.sup id+1)
    _ = 2/(⌈y⌉₊:ℝ) := by
      have hkr : (k:ℝ)+1 = (⌈y⌉₊:ℝ) := by exact_mod_cast hk
      rw [hkr]
    _ ≤ 2/y := div_le_div_of_nonneg_left (by norm_num) (by linarith) (Nat.le_ceil y)

lemma mrt_resolution_le_band_lower {P Q η : ℝ} (hP0 : 0 < P)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q) (hη : 0 ≤ η)
    (j : ℕ) (hj : 1 ≤ j) : mrtResolution P Q η j ≤ mrtBandLower P Q j := by
  have hj1 : (1:ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0:ℝ) < j := by linarith
  have hp1 : 1 ≤ P := by
    rw [← Real.exp_log hP0]
    exact Real.one_le_exp (by linarith)
  have hr := mrt_resolution_log_le hp1 hQ hη j hj
  have hl := mrt_log_band_lower_fourth P Q j hj (by linarith) hQ
  have hlogj := Real.log_le_sub_one_of_pos hj0
  have hj2 : 1 ≤ (j:ℝ)^2 := one_le_pow₀ hj1
  have hp := mul_nonneg (sub_nonneg.mpr hj2) (by linarith : 0 ≤ Real.log P-1)
  have hsq := sq_nonneg ((j:ℝ)-1)
  have hpow : (j:ℝ)^2 ≤ (j:ℝ)^4 := pow_le_pow_right₀ hj1 (by norm_num)
  have hprod := mul_le_mul_of_nonneg_right hpow (by linarith : 0 ≤ Real.log P)
  have hlogs : Real.log (mrtResolution P Q η j) ≤ Real.log (mrtBandLower P Q j) := by
    nlinarith
  calc
    _ = Real.exp (Real.log (mrtResolution P Q η j)) :=
      (Real.exp_log (mrtResolution_pos P Q η hj)).symm
    _ ≤ Real.exp (Real.log (mrtBandLower P Q j)) := Real.exp_le_exp.mpr hlogs
    _ = _ := Real.exp_log (Real.exp_pos _)

lemma mrt_prime_extraction_error (S : Finset ℕ) {y H : ℝ} (hH : 2 ≤ H)
    (hHy : H ≤ y) (hS : ∀ n ∈ S, y ≤ (n:ℝ)) :
    (∑ n ∈ S, 1/(n:ℝ)^2)+(∑ n ∈ S, 1/(n:ℝ)^2)^2+2/H ≤ 6/H := by
  let A := ∑ n ∈ S, 1/(n:ℝ)^2
  have hA0 : 0 ≤ A := sum_nonneg (fun _ _ => by positivity)
  have hA : A ≤ 2/H := (mrt_finite_reciprocal_square_tail S (by linarith) hS).trans
    (div_le_div_of_nonneg_left (by norm_num) (by linarith) hHy)
  have hA1 : A ≤ 1 := hA.trans ((div_le_one (by linarith : 0 < H)).mpr hH)
  have hs : A^2 ≤ A := by nlinarith
  change A+A^2+2/H ≤ 6/H
  have he : 6/H = 3*(2/H) := by ring
  rw [he]
  linarith

theorem mrt_prime_extraction_error_sum (V : ℕ → Finset ℕ) (J : ℕ)
    {P Q η : ℝ} (hP0 : 0 < P) (hP : 2 ≤ Real.log P)
    (hQ : 1 ≤ Real.log Q) (hη : 0 ≤ η) (hH : 2 ≤ mrtBaseResolution P Q η)
    (hrange : ∀ j ∈ Icc 1 J, ∀ p ∈ V j, mrtBandLower P Q j ≤ (p:ℝ)) :
    (∑ j ∈ Icc 1 J,
      ((∑ p ∈ V j, 1/(p:ℝ)^2)+(∑ p ∈ V j, 1/(p:ℝ)^2)^2+
        2/mrtResolution P Q η j)) ≤ 12*(mrtBaseResolution P Q η)⁻¹ := by
  have hres (j : ℕ) (hj : j ∈ Icc 1 J) : 2 ≤ mrtResolution P Q η j := by
    have hj1 : (1:ℝ) ≤ j := by exact_mod_cast (mem_Icc.mp hj).1
    have hs : 1 ≤ (j:ℝ)^2 := one_le_pow₀ hj1
    unfold mrtResolution
    nlinarith [mrtBaseResolution_pos P Q η]
  calc
    _ ≤ ∑ j ∈ Icc 1 J, 6/mrtResolution P Q η j := by
      apply sum_le_sum
      intro j hj
      exact mrt_prime_extraction_error (V j) (hres j hj)
        (mrt_resolution_le_band_lower hP0 hP hQ hη j (mem_Icc.mp hj).1) (hrange j hj)
    _ = 6*(∑ j ∈ Icc 1 J, (mrtResolution P Q η j)⁻¹) := by
      rw [mul_sum]
      simp only [div_eq_mul_inv]
    _ ≤ 6*(2*(mrtBaseResolution P Q η)⁻¹) :=
      mul_le_mul_of_nonneg_left (mrt_resolution_inverse_sum P Q η J) (by norm_num)
    _ = _ := by ring

end TwoPointCorrelations

end OAI
