import OAI.MathematicalPhysics.DefocusingNLS.Linear.FourierConvolution
import OAI.MathematicalPhysics.DefocusingNLS.Linear.FourierAbsolute
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevProductWeights

namespace OAI

/-!
# Weighted convolution for Sobolev multiplication

The frequency weight inequality and Young's inequality give an explicit ℓ²
majorant for the Fourier coefficients of a product.
-/

open scoped ENNReal

namespace DefocusingNLS

theorem weight_mul_sobolevFourierCoefficient (k : ℝ) (f : FourierL2)
    (n : frequencyLattice) :
    (sobolevProductWeight k n : ℂ) * sobolevFourierCoefficient k f n = f n := by
  unfold sobolevProductWeight sobolevFourierCoefficient
  change (((1 + ‖n‖ ^ 2) ^ (k / 2) : ℝ) : ℂ) *
    ((((1 + ‖n‖ ^ 2) ^ (-k / 2) : ℝ) : ℂ) * f n) = f n
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]
  have he : k / 2 + -k / 2 = 0 := by ring
  simp [he]

theorem weight_mul_norm_sobolevFourierCoefficient (k : ℝ) (f : FourierL2)
    (n : frequencyLattice) :
    sobolevProductWeight k n * ‖sobolevFourierCoefficient k f n‖ = ‖f n‖ := by
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sobolevProductWeight_pos k n)] using
      congrArg norm (weight_mul_sobolevFourierCoefficient k f n)

theorem norm_sobolevFourierCoefficient_le (k : ℝ) (hk : 0 ≤ k) (f : FourierL2)
    (n : frequencyLattice) : ‖sobolevFourierCoefficient k f n‖ ≤ ‖f‖ := by
  have hw : 1 ≤ sobolevProductWeight k n := by
    unfold sobolevProductWeight
    exact Real.one_le_rpow (le_add_of_nonneg_right (sq_nonneg _)) (by positivity)
  calc
    _ ≤ sobolevProductWeight k n * ‖sobolevFourierCoefficient k f n‖ :=
      le_mul_of_one_le_left (norm_nonneg _) hw
    _ = ‖f n‖ := weight_mul_norm_sobolevFourierCoefficient k f n
    _ ≤ ‖f‖ := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) f n

/-- The physical coefficients of the product are the discrete convolution. -/
noncomputable def sobolevProductCoefficient (k : ℝ) (f g : FourierL2)
    (n : frequencyLattice) : ℂ :=
  ∑' m, sobolevFourierCoefficient k f m * sobolevFourierCoefficient k g (n - m)

theorem summable_norm_sobolevProductTerms (k : ℝ) (hk : 6 < k) (f g : FourierL2)
    (n : frequencyLattice) :
    Summable (fun m => ‖sobolevFourierCoefficient k f m‖ *
      ‖sobolevFourierCoefficient k g (n - m)‖) := by
  apply Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun m => mul_le_mul_of_nonneg_left (norm_sobolevFourierCoefficient_le k (by linarith) g _)
      (norm_nonneg _))
  exact (summable_norm_sobolevFourierCoefficient k hk f).mul_right ‖g‖

theorem absolute_convolution_apply (a : frequencyLattice → ℂ)
    (ha : Summable (fun m => ‖a m‖)) (f : FourierL2) (n : frequencyLattice) :
    fourierConvolution (fun m => (‖a m‖ : ℂ)) (fourierAbsolute f) n =
      Complex.ofReal (∑' m, ‖a m‖ * ‖f (n - m)‖) := by
  rw [fourierConvolution_apply _ (by simpa using ha)]
  simp only [fourierAbsolute_apply, ← Complex.ofReal_mul, ← Complex.ofReal_tsum]

/-- The two unweighted Young convolutions which dominate the weighted product. -/
noncomputable def sobolevProductMajorant (k : ℝ) (f g : FourierL2) : FourierL2 :=
  Complex.ofReal ((4 : ℝ) ^ (k / 2)) •
    (fourierConvolution (fun m => (‖sobolevFourierCoefficient k f m‖ : ℂ)) (fourierAbsolute g) +
      fourierConvolution (fun m => (‖sobolevFourierCoefficient k g m‖ : ℂ)) (fourierAbsolute f))

theorem sobolevProductMajorant_norm_apply (k : ℝ) (hk : 6 < k) (f g : FourierL2)
    (n : frequencyLattice) :
    ‖sobolevProductMajorant k f g n‖ = 4 ^ (k / 2) *
      ((∑' m, ‖sobolevFourierCoefficient k f m‖ * ‖g (n - m)‖) +
        ∑' m, ‖sobolevFourierCoefficient k g m‖ * ‖f (n - m)‖) := by
  simp only [sobolevProductMajorant, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_add,
    Pi.add_apply, smul_eq_mul]
  rw [absolute_convolution_apply _ (summable_norm_sobolevFourierCoefficient k hk f),
    absolute_convolution_apply _ (summable_norm_sobolevFourierCoefficient k hk g),
    ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
  apply abs_of_nonneg
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (add_nonneg (tsum_nonneg (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      (tsum_nonneg (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))))

lemma weighted_product_term_bound (k : ℝ) (hk : 0 ≤ k) (f g : FourierL2)
    (n m : frequencyLattice) :
    sobolevProductWeight k n *
        (‖sobolevFourierCoefficient k f m‖ * ‖sobolevFourierCoefficient k g (n - m)‖) ≤
      4 ^ (k / 2) * (‖f m‖ * ‖sobolevFourierCoefficient k g (n - m)‖ +
        ‖sobolevFourierCoefficient k f m‖ * ‖g (n - m)‖) := by
  have hw := sobolevProductWeight_add_le k hk m (n - m)
  have hn : m + (n - m) = n := by abel
  rw [hn] at hw
  calc
    _ ≤ (4 ^ (k / 2) * (sobolevProductWeight k m + sobolevProductWeight k (n - m))) *
        (‖sobolevFourierCoefficient k f m‖ * ‖sobolevFourierCoefficient k g (n - m)‖) :=
      mul_le_mul_of_nonneg_right hw (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      rw [← weight_mul_norm_sobolevFourierCoefficient k f m,
        ← weight_mul_norm_sobolevFourierCoefficient k g (n - m)]
      ring

/-- The weighted convolution is bounded pointwise by an ℓ² vector. -/
theorem weighted_sobolevProduct_le_majorant (k : ℝ) (hk : 6 < k) (f g : FourierL2)
    (n : frequencyLattice) :
    ‖(sobolevProductWeight k n : ℂ) * sobolevProductCoefficient k f g n‖ ≤
      ‖sobolevProductMajorant k f g n‖ := by
  let A := fun m : frequencyLattice => ‖f m‖ * ‖sobolevFourierCoefficient k g (n - m)‖
  let B := fun m : frequencyLattice => ‖sobolevFourierCoefficient k f m‖ * ‖g (n - m)‖
  have hA : Summable A := by
    apply Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun m => mul_le_mul_of_nonneg_right
        (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) f m) (norm_nonneg _))
    exact ((Equiv.subLeft n).summable_iff.mpr
      (summable_norm_sobolevFourierCoefficient k hk g)).mul_left ‖f‖
  have hB : Summable B := by
    apply Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun m => mul_le_mul_of_nonneg_left
        (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) g (n - m)) (norm_nonneg _))
    exact (summable_norm_sobolevFourierCoefficient k hk f).mul_right ‖g‖
  have hp := summable_norm_sobolevProductTerms k hk f g n
  have hswap : (∑' m, A m) =
      ∑' m, ‖sobolevFourierCoefficient k g m‖ * ‖f (n - m)‖ := by
    rw [← (Equiv.subLeft n).tsum_eq A]
    simp only [A, Equiv.subLeft_apply, sub_sub_cancel, mul_comm]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sobolevProductWeight_pos k n), sobolevProductMajorant_norm_apply k hk]
  calc
    _ ≤ sobolevProductWeight k n *
        ∑' m, ‖sobolevFourierCoefficient k f m‖ * ‖sobolevFourierCoefficient k g (n - m)‖ := by
      apply mul_le_mul_of_nonneg_left _ (sobolevProductWeight_pos k n).le
      simpa only [sobolevProductCoefficient, norm_mul] using
        (norm_tsum_le_tsum_norm
          (f := fun m => sobolevFourierCoefficient k f m * sobolevFourierCoefficient k g (n - m))
          (by simpa only [norm_mul] using hp))
    _ = ∑' m, sobolevProductWeight k n *
        (‖sobolevFourierCoefficient k f m‖ * ‖sobolevFourierCoefficient k g (n - m)‖) :=
      by rw [tsum_mul_left]
    _ ≤ ∑' m, 4 ^ (k / 2) * (A m + B m) :=
      (hp.mul_left _).tsum_le_tsum (fun m => weighted_product_term_bound k (by linarith) f g n m)
        ((hA.add hB).mul_left _)
    _ = _ := by rw [tsum_mul_left, hA.tsum_add hB, hswap]; ring

/-- Multiplication closes in the original Sobolev Fourier space. -/
noncomputable def sobolevProduct (k : ℝ) (hk : 6 < k) (f g : FourierL2) : FourierL2 :=
  ⟨fun n => (sobolevProductWeight k n : ℂ) * sobolevProductCoefficient k f g n,
    (lp.memℓp (sobolevProductMajorant k f g)).mono'
      (weighted_sobolevProduct_le_majorant k hk f g)⟩

theorem sobolevProduct_coefficient (k : ℝ) (hk : 6 < k) (f g : FourierL2)
    (n : frequencyLattice) :
    sobolevFourierCoefficient k (sobolevProduct k hk f g) n =
      sobolevProductCoefficient k f g n := by
  apply mul_left_cancel₀ (show (sobolevProductWeight k n : ℂ) ≠ 0 from
    Complex.ofReal_ne_zero.mpr (sobolevProductWeight_pos k n).ne')
  exact weight_mul_sobolevFourierCoefficient k (sobolevProduct k hk f g) n

/-- A quantitative norm bound for the two-Young-convolution majorant. -/
theorem sobolevProductMajorant_norm_le (k : ℝ) (hk : 6 < k) (f g : FourierL2) :
    ‖sobolevProductMajorant k f g‖ ≤
      2 * 4 ^ (k / 2) * ‖sobolevObservationVector k hk‖ * ‖f‖ * ‖g‖ := by
  have hf := summable_norm_sobolevFourierCoefficient k hk f
  have hg := summable_norm_sobolevFourierCoefficient k hk g
  have hcf := fourierConvolution_norm_le (fun m => (‖sobolevFourierCoefficient k f m‖ : ℂ))
    (by simpa using hf) (fourierAbsolute g)
  have hcg := fourierConvolution_norm_le (fun m => (‖sobolevFourierCoefficient k g m‖ : ℂ))
    (by simpa using hg) (fourierAbsolute f)
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm, fourierAbsolute_norm] at hcf hcg
  have hC : 0 ≤ (4 : ℝ) ^ (k / 2) := Real.rpow_nonneg (by norm_num) _
  calc
    _ = 4 ^ (k / 2) * ‖fourierConvolution
        (fun m => (‖sobolevFourierCoefficient k f m‖ : ℂ)) (fourierAbsolute g) +
        fourierConvolution (fun m => (‖sobolevFourierCoefficient k g m‖ : ℂ))
          (fourierAbsolute f)‖ := by
      rw [sobolevProductMajorant, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hC]
    _ ≤ 4 ^ (k / 2) *
        (‖fourierConvolution (fun m => (‖sobolevFourierCoefficient k f m‖ : ℂ))
          (fourierAbsolute g)‖ +
        ‖fourierConvolution (fun m => (‖sobolevFourierCoefficient k g m‖ : ℂ))
          (fourierAbsolute f)‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) hC
    _ ≤ 4 ^ (k / 2) * ((∑' m, ‖sobolevFourierCoefficient k f m‖) * ‖g‖ +
        (∑' m, ‖sobolevFourierCoefficient k g m‖) * ‖f‖) :=
      mul_le_mul_of_nonneg_left (add_le_add hcf hcg) hC
    _ ≤ 4 ^ (k / 2) * ((‖sobolevObservationVector k hk‖ * ‖f‖) * ‖g‖ +
        (‖sobolevObservationVector k hk‖ * ‖g‖) * ‖f‖) := by
      gcongr
      · exact tsum_norm_sobolevFourierCoefficient_le k hk f
      · exact tsum_norm_sobolevFourierCoefficient_le k hk g
    _ = _ := by ring

/-- Multiplication is bounded bilinearly in the twelve-dimensional Sobolev norm. -/
theorem sobolevProduct_norm_le (k : ℝ) (hk : 6 < k) (f g : FourierL2) :
    ‖sobolevProduct k hk f g‖ ≤
      2 * 4 ^ (k / 2) * ‖sobolevObservationVector k hk‖ * ‖f‖ * ‖g‖ := by
  exact (lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (weighted_sobolevProduct_le_majorant k hk f g)).trans
      (sobolevProductMajorant_norm_le k hk f g)

end DefocusingNLS

end OAI
