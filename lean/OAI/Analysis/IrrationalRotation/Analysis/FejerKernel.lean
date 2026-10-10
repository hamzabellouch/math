import OAI.Analysis.IrrationalRotation.Model.Fejer
import OAI.Analysis.IrrationalRotation.Analysis.GeometricAverage
import Mathlib

namespace OAI

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace Invariant233.Fejer

 theorem kernel_nonneg (H : ℕ) (x : Circle) : 0 ≤ kernel H x :=
  div_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

 theorem continuous_geometricPolynomial (H : ℕ) : Continuous (geometricPolynomial H) := by
  unfold geometricPolynomial
  exact continuous_finsetSum _ (fun _ _ => (fourier _).continuous)

 theorem continuous_kernel (H : ℕ) : Continuous (kernel H) := by
  unfold kernel
  simpa only [Complex.normSq_eq_norm_sq, Pi.pow_apply] using
    ((continuous_geometricPolynomial H).norm.pow 2).div_const (H : ℝ)

 theorem geometricPolynomial_eq_sum_pow (H : ℕ) (x : Circle) :
    geometricPolynomial H x = ∑ k ∈ Finset.range H, (fourier 1 x) ^ k := by
  apply Finset.sum_congr rfl
  intro k hk
  simp only [fourier_apply, one_zsmul]
  rw [natCast_zsmul, AddCircle.toCircle_nsmul, Circle.coe_pow]

 theorem kernel_complex_expansion (H : ℕ) (x : Circle) :
    (kernel H x : ℂ) = (H : ℂ)⁻¹ *
      ∑ k ∈ Finset.range H, ∑ l ∈ Finset.range H,
        fourier ((k : ℤ) - (l : ℤ)) x := by
  rw [kernel, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.normSq_eq_conj_mul_self]
  unfold geometricPolynomial
  rw [map_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, div_eq_inv_mul]
  simp_rw [sub_eq_add_neg, fourier_add, fourier_neg]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

 theorem integral_fourier (n : ℤ) :
    (∫ x : Circle, fourier n x ∂AddCircle.haarAddCircle) = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) n) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using h

 theorem integral_kernel_complex (H : ℕ) (hH : H ≠ 0) :
    (∫ x : Circle, (kernel H x : ℂ) ∂AddCircle.haarAddCircle) = 1 := by
  simp_rw [kernel_complex_expansion]
  rw [integral_const_mul]
  rw [integral_finsetSum]
  · simp_rw [integral_finsetSum _ (fun l hl => (fourier _).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      integral_fourier]
    have hsum : (∑ k ∈ Finset.range H, ∑ l ∈ Finset.range H,
        (if (k : ℤ) - (l : ℤ) = 0 then (1 : ℂ) else 0)) = H := by
      simp only [sub_eq_zero, Nat.cast_inj]
      calc
        _ = ∑ k ∈ Finset.range H, (1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [Finset.sum_ite_eq, hk, ite_true]
        _ = H := by simp
    rw [hsum, inv_mul_cancel₀ (by exact_mod_cast hH)]
  · intro k hk
    exact integrable_finsetSum _ (fun l hl => (fourier _).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

 theorem integral_kernel (H : ℕ) (hH : H ≠ 0) :
    (∫ x : Circle, kernel H x ∂AddCircle.haarAddCircle) = 1 := by
  have h := integral_kernel_complex H hH
  have hcast := integral_ofReal (f := kernel H) (𝕜 := ℂ)
    (μ := (AddCircle.haarAddCircle : Measure Circle))
  have hcast2 : (∫ x : Circle, (kernel H x : ℂ) ∂AddCircle.haarAddCircle) =
      Complex.ofReal (∫ x : Circle, kernel H x ∂AddCircle.haarAddCircle) := hcast
  rw [hcast2] at h
  exact_mod_cast h

 theorem integrable_fourier (n : ℤ) :
    Integrable (fun x : Circle => fourier n x) AddCircle.haarAddCircle :=
  (fourier n).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

 theorem integrable_kernel (H : ℕ) :
    Integrable (kernel H) AddCircle.haarAddCircle :=
  (continuous_kernel H).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

 theorem coefficient_norm_le_one (H : ℕ) (hH : H ≠ 0) (n : ℤ) :
    ‖coefficient H n‖ ≤ 1 := by
  unfold coefficient fourierCoeff
  calc
    _ ≤ ∫ x : Circle, ‖fourier (-n) x • (kernel H x : ℂ)‖
        ∂AddCircle.haarAddCircle := norm_integral_le_integral_norm _
    _ = ∫ x : Circle, kernel H x ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [smul_eq_mul, norm_mul, fourier_apply, Circle.norm_coe,
        one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (kernel_nonneg H x)]
    _ = 1 := integral_kernel H hH

 theorem difference_mem_frequencies {H k l : ℕ}
    (hk : k ∈ Finset.range H) (hl : l ∈ Finset.range H) :
    (k : ℤ) - (l : ℤ) ∈ frequencies H := by
  simp only [frequencies, Finset.mem_Ioo]
  simp only [Finset.mem_range] at hk hl
  omega

 theorem coefficient_expansion (H : ℕ) (n : ℤ) :
    coefficient H n = (H : ℂ)⁻¹ *
      ∑ k ∈ Finset.range H, ∑ l ∈ Finset.range H,
        if (k : ℤ) - (l : ℤ) = n then (1 : ℂ) else 0 := by
  unfold coefficient
  have heq : (fun x : Circle => (kernel H x : ℂ)) = fun x =>
      (H : ℂ)⁻¹ * ∑ k ∈ Finset.range H, ∑ l ∈ Finset.range H,
        fourier ((k : ℤ) - (l : ℤ)) x := funext (kernel_complex_expansion H)
  rw [heq, fourierCoeff.const_mul]
  congr 1
  have houter : (fun x : Circle => ∑ k ∈ Finset.range H, ∑ l ∈ Finset.range H,
        fourier ((k : ℤ) - (l : ℤ)) x) =
      ∑ k ∈ Finset.range H, ∑ l ∈ Finset.range H,
        (fun x : Circle => fourier ((k : ℤ) - (l : ℤ)) x) := by
    ext x
    simp
  rw [houter, fourierCoeff.sum]
  · simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [fourierCoeff.sum]
    · simp only [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro l hl
      simp only [fourierCoeff_fourier, Pi.single_apply, eq_comm]
    · intro l hl
      exact integrable_fourier _
  · intro k hk
    exact integrable_finsetSum' _ (fun l hl => integrable_fourier _)

 theorem kernel_eq_finite_fourier_sum (H : ℕ) (x : Circle) :
    (kernel H x : ℂ) = ∑ n ∈ frequencies H, coefficient H n * fourier n x := by
  rw [kernel_complex_expansion]
  symm
  simp_rw [coefficient_expansion, mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    difference_mem_frequencies hk hl, ite_true]

 theorem coefficient_eq_zero_outside {H : ℕ} {n : ℤ}
    (hn : n ∉ frequencies H) : coefficient H n = 0 := by
  rw [coefficient_expansion]
  have hzero : (∑ k ∈ Finset.range H, ∑ l ∈ Finset.range H,
      if (k : ℤ) - (l : ℤ) = n then (1 : ℂ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    apply Finset.sum_eq_zero
    intro l hl
    have hne : (k : ℤ) - (l : ℤ) ≠ n := by
      intro heq
      apply hn
      rw [← heq]
      exact difference_mem_frequencies hk hl
    simp only [hne, ite_false]
  rw [hzero, mul_zero]

 theorem kernel_le_chord_bound (H : ℕ) (x : Circle) (hx : fourier 1 x ≠ 1) :
    kernel H x ≤ 4 / ((H : ℝ) * ‖fourier 1 x - 1‖ ^ 2) := by
  have hb := Invariant233.norm_geometric_sum_le (fourier 1 x) hx
    (Circle.norm_coe _) H
  rw [← geometricPolynomial_eq_sum_pow] at hb
  rw [kernel, Complex.normSq_eq_norm_sq]
  have hs : ‖geometricPolynomial H x‖ ^ 2 ≤ (2 / ‖fourier 1 x - 1‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 2
  calc
    _ ≤ (2 / ‖fourier 1 x - 1‖) ^ 2 / H :=
      div_le_div_of_nonneg_right hs (Nat.cast_nonneg H)
    _ = 4 / ((H : ℝ) * ‖fourier 1 x - 1‖ ^ 2) := by
      rw [div_pow, div_div]
      congr 1 <;> ring

 theorem chord_lower_bound_coe {t : ℝ} (ht : |t| ≤ 1 / 2) :
    4 * |t| ≤ ‖fourier 1 (t : Circle) - 1‖ := by
  have hangle : |Real.pi * t| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin hangle
  rw [abs_mul, abs_of_pos Real.pi_pos] at hsin
  have hc : 2 * (Real.pi : ℂ) * Complex.I * (1 : ℂ) * (t : ℂ) / (1 : ℂ) =
      Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [fourier_coe_apply]
  norm_num only [Complex.ofReal_one, Int.cast_one] at *
  rw [hc, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hhalf : 2 * Real.pi * t / 2 = Real.pi * t := by ring
  rw [hhalf, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hcanc : 2 / Real.pi * (Real.pi * |t|) = 2 * |t| := by
    field_simp
  rw [hcanc] at hsin
  linarith

 theorem chord_lower_bound (x : Circle) :
    4 * dist x 0 ≤ ‖fourier 1 x - 1‖ := by
  induction x using QuotientAddGroup.induction_on with
  | H t =>
    have hround : (((round t : ℤ) : ℝ) : Circle) = 0 := by
      have hc := AddCircle.coe_zsmul (p := (1 : ℝ)) (n := round t) (x := (1 : ℝ))
      simpa only [zsmul_eq_mul, mul_one, AddCircle.coe_period, smul_zero] using hc
    have hcoe : ((t - round t : ℝ) : Circle) = (t : Circle) := by
      rw [QuotientAddGroup.mk_sub, hround, sub_zero]
    have h := chord_lower_bound_coe (abs_sub_round t)
    rw [hcoe] at h
    simpa only [dist_zero_right, UnitAddCircle.norm_eq] using h

 theorem volume_eq_haar : (volume : Measure Circle) = AddCircle.haarAddCircle := by
  simp only [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

 theorem integral_kernel_volume (H : ℕ) (hH : H ≠ 0) :
    (∫ x : Circle, kernel H x) = 1 := by
  rw [volume_eq_haar]
  exact integral_kernel H hH

 theorem kernel_le_distance_bound (H : ℕ) (hH : H ≠ 0)
    (x : Circle) (hx : x ≠ 0) :
    kernel H x ≤ 1 / (4 * (H : ℝ) * (dist x 0) ^ 2) := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hH
  have hd : 0 < dist x 0 := dist_pos.mpr hx
  have hc := chord_lower_bound x
  have hcpos : 0 < ‖fourier 1 x - 1‖ := lt_of_lt_of_le (by positivity) hc
  have hxchar : fourier 1 x ≠ 1 := by
    intro heq
    simp only [heq, sub_self, norm_zero, lt_self_iff_false] at hcpos
  calc
    kernel H x ≤ 4 / ((H : ℝ) * ‖fourier 1 x - 1‖ ^ 2) :=
      kernel_le_chord_bound H x hxchar
    _ ≤ 4 / ((H : ℝ) * (4 * dist x 0) ^ 2) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hc 2) hHpos.le
    _ = 1 / (4 * (H : ℝ) * (dist x 0) ^ 2) := by
      field_simp

 theorem kernel_le_of_distance_ge (H : ℕ) (hH : H ≠ 0)
    {η : ℝ} (hη : 0 < η) (x : Circle) (hx : η ≤ dist x 0) :
    kernel H x ≤ 1 / (4 * (H : ℝ) * η ^ 2) := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hH
  have hx0 : x ≠ 0 := by
    intro heq
    subst x
    simp only [dist_self] at hx
    linarith
  apply (kernel_le_distance_bound H hH x hx0).trans
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hη.le hx 2) (by positivity)

 theorem card_frequencies_le (H : ℕ) : (frequencies H).card ≤ 2 * H := by
  simp only [frequencies, Int.card_Ioo]
  omega

 theorem coefficient_zero (H : ℕ) (hH : H ≠ 0) : coefficient H 0 = 1 := by
  simpa only [coefficient, fourierCoeff, neg_zero, fourier_zero, one_smul]
    using integral_kernel_complex H hH

 theorem norm_fourier_sub_one_coe (n : ℤ) (t : ℝ) :
    ‖fourier n (t : Circle) - 1‖ = 2 * |Real.sin (Real.pi * n * t)| := by
  rw [fourier_coe_apply]
  have hc : 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ) / (1 : ℂ) =
      Complex.I * ((2 * Real.pi * n * t : ℝ) : ℂ) := by
    push_cast
    ring
  norm_num only [Complex.ofReal_one]
  rw [hc, Complex.norm_exp_I_mul_ofReal_sub_one]
  have heq : 2 * Real.pi * n * t / 2 = Real.pi * n * t := by ring
  rw [heq, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

 theorem kernel_eq_sine_formula (H : ℕ) (t : ℝ)
    (ht : Real.sin (Real.pi * t) ≠ 0) :
    kernel H (t : Circle) = (1 / (H : ℝ)) *
      (Real.sin (Real.pi * H * t) / Real.sin (Real.pi * t)) ^ 2 := by
  have hnorm : ‖fourier 1 (t : Circle) - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
    simpa only [Int.cast_one, mul_one] using norm_fourier_sub_one_coe 1 t
  have hx : fourier 1 (t : Circle) ≠ 1 := by
    intro heq
    rw [heq, sub_self, norm_zero] at hnorm
    have hp := abs_pos.mpr ht
    linarith
  have hpow : (fourier 1 (t : Circle)) ^ H = fourier (H : ℤ) (t : Circle) := by
    simp only [fourier_apply, one_zsmul, natCast_zsmul,
      AddCircle.toCircle_nsmul, Circle.coe_pow]
  rw [kernel, Complex.normSq_eq_norm_sq, geometricPolynomial_eq_sum_pow,
    geom_sum_eq hx, norm_div, hpow, norm_fourier_sub_one_coe, hnorm]
  simp only [Int.cast_natCast, div_pow, mul_pow, sq_abs]
  ring

 theorem kernel_zero (H : ℕ) : kernel H 0 = H := by
  simp only [kernel, geometricPolynomial, fourier_eval_zero, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one, Complex.normSq_eq_norm_sq, norm_natCast]
  by_cases hH : H = 0
  · simp [hH]
  · have hHr : (H : ℝ) ≠ 0 := by exact_mod_cast hH
    field_simp

end Invariant233.Fejer

end

end OAI
