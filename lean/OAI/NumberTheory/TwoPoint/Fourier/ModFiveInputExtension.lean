import OAI.NumberTheory.TwoPoint.Fourier.ModFiveMangoldt

namespace OAI

/-! Finite-cutoff completion of the fixed modulus-five prime input.
An eventual quantitative Mangoldt estimate suffices, since the remaining
bounded cutoffs are controlled by one finite nonnegative Mangoldt sum. -/

namespace TwoPointCorrelations

open Finset Filter

lemma modFivePsi_nonneg (one : Bool) (x : ℝ) : 0 ≤ modFivePsi one x := by
  apply sum_nonneg
  intro n hn
  unfold modFiveMangoldtWeight
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · rfl

lemma modFivePsi_le_psi (one : Bool) {x y : ℝ} (hxy : x ≤ y) :
    modFivePsi one x ≤ Chebyshev.psi y := by
  rw [modFivePsi, Chebyshev.psi_eq_sum_Icc]
  calc
    _ ≤ ∑ n ∈ Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := by
      apply sum_le_sum
      intro n hn
      unfold modFiveMangoldtWeight
      split_ifs
      · rfl
      · exact ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
      (Icc_subset_Icc_right (Nat.floor_le_floor hxy))
      (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg)

lemma modFiveDensity_bounds (one : Bool) : 0 ≤ modFiveDensity one ∧ modFiveDensity one ≤ 1 := by
  cases one <;> norm_num [modFiveDensity]

lemma modFivePsi_bounded_cutoffs (one : Bool) {x Y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ Y) :
    |modFivePsi one x - modFiveDensity one * x| ≤ Chebyshev.psi Y + Y := by
  have hd := modFiveDensity_bounds one
  have hm : 0 ≤ modFiveDensity one * x := mul_nonneg hd.1 hx
  calc
    _ ≤ |modFivePsi one x| + |modFiveDensity one * x| := abs_sub _ _
    _ = modFivePsi one x + modFiveDensity one * x := by
      rw [abs_of_nonneg (modFivePsi_nonneg one x), abs_of_nonneg hm]
    _ ≤ _ := add_le_add (modFivePsi_le_psi one hxy)
      ((mul_le_mul_of_nonneg_right hd.2 hx).trans_eq (one_mul x) |>.trans hxy)

theorem modFiveThetaInput_of_eventual_psi (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hbound : ∀ᶠ x : ℝ in atTop, ∀ one : Bool,
      |modFivePsi one x - modFiveDensity one * x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x))) :
    ModFiveThetaInput := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp hbound
  let Y := max 2 X
  let M := Chebyshev.psi Y + Y
  let K := M * Real.exp (c * Real.sqrt (Real.log Y))
  have hY2 : 2 ≤ Y := le_max_left _ _
  have hM : 0 ≤ M := add_nonneg (Chebyshev.psi_nonneg _) (by dsimp [Y]; positivity)
  have hK : 0 ≤ K := mul_nonneg hM (Real.exp_pos _).le
  apply modFiveThetaInput_of_psi c (max C K) hc (hC.trans (le_max_left _ _))
  intro one x hx
  by_cases hlarge : Y ≤ x
  · exact (hX x ((le_max_right _ _).trans hlarge) one).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C K)
        (by linarith)) (Real.exp_pos _).le)
  · have hxy : x ≤ Y := (lt_of_not_ge hlarge).le
    have hnorm := modFivePsi_bounded_cutoffs one (by linarith) hxy
    have hroot : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log Y) :=
      Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hxy)
    have hexp : Real.exp (-c * Real.sqrt (Real.log Y)) ≤
        Real.exp (-c * Real.sqrt (Real.log x)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hroot (neg_nonpos.mpr hc.le))
    have hprod : 1 ≤ Real.exp (c * Real.sqrt (Real.log Y)) *
        Real.exp (-c * Real.sqrt (Real.log x)) := by
      calc
        1 = Real.exp (c * Real.sqrt (Real.log Y)) *
            Real.exp (-c * Real.sqrt (Real.log Y)) := by rw [← Real.exp_add]; simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
    have hm : M ≤ K * Real.exp (-c * Real.sqrt (Real.log x)) := by
      have hh := mul_le_mul_of_nonneg_left hprod hM
      simpa only [mul_one, K, mul_assoc] using hh
    apply hnorm.trans (hm.trans ?_)
    calc
      K * Real.exp (-c * Real.sqrt (Real.log x)) ≤
          (K * x) * Real.exp (-c * Real.sqrt (Real.log x)) :=
        mul_le_mul_of_nonneg_right
          (by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (by linarith : 1 ≤ x) hK)
          (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right C K) (by linarith)) (Real.exp_pos _).le

end TwoPointCorrelations

end OAI
