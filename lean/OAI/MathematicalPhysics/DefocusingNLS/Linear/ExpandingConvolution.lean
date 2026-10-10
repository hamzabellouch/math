import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFourier
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevConvolution

namespace OAI

/-! # Multiplication with the exact expanding-torus Fourier weight

The constants below are independent of the expanding radius `L`.
-/

open scoped ENNReal

namespace DefocusingNLS

theorem weight_mul_norm_expandingFourierCoefficient (a k L : ℝ) (hL : 1 ≤ L) (f : FourierL2)
    (n : frequencyLattice) :
    expandingSobolevWeight a k L n * ‖expandingFourierCoefficient a k L f n‖ = ‖f n‖ := by
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (expandingSobolevWeight_pos a k L hL n)] using
      congrArg norm (weight_mul_expandingFourierCoefficient a k L hL f n)

theorem norm_expandingFourierCoefficient_le (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (f : FourierL2) (n : frequencyLattice) :
    ‖expandingFourierCoefficient a k L f n‖ ≤ expandingEmbeddingBound a k * ‖f‖ := by
  have hs := summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL f
  have hn := hs.sum_le_tsum {n} (fun j _ => norm_nonneg (expandingFourierCoefficient a k L f j))
  have hn' : ‖expandingFourierCoefficient a k L f n‖ ≤
      ∑' j, ‖expandingFourierCoefficient a k L f j‖ := by simpa using hn
  exact hn'.trans
    (tsum_norm_expandingFourierCoefficient_le a k L ha ha1 hk hL f)

/-- The physical coefficients of the product are the discrete convolution. -/
noncomputable def expandingProductCoefficient (a k L : ℝ) (f g : FourierL2)
    (n : frequencyLattice) : ℂ :=
  ∑' m, expandingFourierCoefficient a k L f m * expandingFourierCoefficient a k L g (n - m)

theorem summable_norm_expandingProductTerms (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f g : FourierL2)
    (n : frequencyLattice) :
    Summable (fun m => ‖expandingFourierCoefficient a k L f m‖ *
      ‖expandingFourierCoefficient a k L g (n - m)‖) := by
  apply Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun m => mul_le_mul_of_nonneg_left (norm_expandingFourierCoefficient_le a k L ha ha1 hk hL g _)
      (norm_nonneg _))
  exact (summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL f).mul_right (expandingEmbeddingBound a k * ‖g‖)

/-- The two unweighted Young convolutions which dominate the weighted product. -/
noncomputable def expandingProductMajorant (a k L : ℝ) (f g : FourierL2) : FourierL2 :=
  Complex.ofReal (Real.sqrt ((4 : ℝ) ^ k)) •
    (fourierConvolution (fun m => (‖expandingFourierCoefficient a k L f m‖ : ℂ)) (fourierAbsolute g) +
      fourierConvolution (fun m => (‖expandingFourierCoefficient a k L g m‖ : ℂ)) (fourierAbsolute f))

theorem expandingProductMajorant_norm_apply (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f g : FourierL2)
    (n : frequencyLattice) :
    ‖expandingProductMajorant a k L f g n‖ = Real.sqrt (4 ^ k) *
      ((∑' m, ‖expandingFourierCoefficient a k L f m‖ * ‖g (n - m)‖) +
        ∑' m, ‖expandingFourierCoefficient a k L g m‖ * ‖f (n - m)‖) := by
  simp only [expandingProductMajorant, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_add,
    Pi.add_apply, smul_eq_mul]
  rw [absolute_convolution_apply _ (summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL f),
    absolute_convolution_apply _ (summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL g),
    ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
  apply abs_of_nonneg
  exact mul_nonneg (Real.sqrt_nonneg _)
    (add_nonneg (tsum_nonneg (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      (tsum_nonneg (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))))

lemma expanding_weighted_product_term_bound (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f g : FourierL2)
    (n m : frequencyLattice) :
    expandingSobolevWeight a k L n *
        (‖expandingFourierCoefficient a k L f m‖ * ‖expandingFourierCoefficient a k L g (n - m)‖) ≤
      Real.sqrt (4 ^ k) * (‖f m‖ * ‖expandingFourierCoefficient a k L g (n - m)‖ +
        ‖expandingFourierCoefficient a k L f m‖ * ‖g (n - m)‖) := by
  have hw := expandingSobolevWeight_add_le a k L ha ha1 hk hL m (n - m)
  have hn : m + (n - m) = n := by abel
  rw [hn] at hw
  calc
    _ ≤ (Real.sqrt (4 ^ k) * (expandingSobolevWeight a k L m + expandingSobolevWeight a k L (n - m))) *
        (‖expandingFourierCoefficient a k L f m‖ * ‖expandingFourierCoefficient a k L g (n - m)‖) :=
      mul_le_mul_of_nonneg_right hw (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      rw [← weight_mul_norm_expandingFourierCoefficient a k L hL f m,
        ← weight_mul_norm_expandingFourierCoefficient a k L hL g (n - m)]
      ring

/-- The weighted convolution is bounded pointwise by an ℓ² vector. -/
theorem weighted_expandingProduct_le_majorant (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f g : FourierL2)
    (n : frequencyLattice) :
    ‖(expandingSobolevWeight a k L n : ℂ) * expandingProductCoefficient a k L f g n‖ ≤
      ‖expandingProductMajorant a k L f g n‖ := by
  let A := fun m : frequencyLattice => ‖f m‖ * ‖expandingFourierCoefficient a k L g (n - m)‖
  let B := fun m : frequencyLattice => ‖expandingFourierCoefficient a k L f m‖ * ‖g (n - m)‖
  have hA : Summable A := by
    apply Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun m => mul_le_mul_of_nonneg_right
        (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) f m) (norm_nonneg _))
    exact ((Equiv.subLeft n).summable_iff.mpr
      (summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL g)).mul_left ‖f‖
  have hB : Summable B := by
    apply Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun m => mul_le_mul_of_nonneg_left
        (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) g (n - m)) (norm_nonneg _))
    exact (summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL f).mul_right ‖g‖
  have hp := summable_norm_expandingProductTerms a k L ha ha1 hk hL f g n
  have hswap : (∑' m, A m) =
      ∑' m, ‖expandingFourierCoefficient a k L g m‖ * ‖f (n - m)‖ := by
    rw [← (Equiv.subLeft n).tsum_eq A]
    simp only [A, Equiv.subLeft_apply, sub_sub_cancel, mul_comm]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (expandingSobolevWeight_pos a k L hL n), expandingProductMajorant_norm_apply a k L ha ha1 hk hL]
  calc
    _ ≤ expandingSobolevWeight a k L n *
        ∑' m, ‖expandingFourierCoefficient a k L f m‖ * ‖expandingFourierCoefficient a k L g (n - m)‖ := by
      apply mul_le_mul_of_nonneg_left _ (expandingSobolevWeight_pos a k L hL n).le
      simpa only [expandingProductCoefficient, norm_mul] using
        (norm_tsum_le_tsum_norm
          (f := fun m => expandingFourierCoefficient a k L f m * expandingFourierCoefficient a k L g (n - m))
          (by simpa only [norm_mul] using hp))
    _ = ∑' m, expandingSobolevWeight a k L n *
        (‖expandingFourierCoefficient a k L f m‖ * ‖expandingFourierCoefficient a k L g (n - m)‖) :=
      by rw [tsum_mul_left]
    _ ≤ ∑' m, Real.sqrt (4 ^ k) * (A m + B m) :=
      (hp.mul_left _).tsum_le_tsum (fun m => expanding_weighted_product_term_bound a k L ha ha1 hk hL f g n m)
        ((hA.add hB).mul_left _)
    _ = _ := by rw [tsum_mul_left, hA.tsum_add hB, hswap]; ring

/-- Multiplication closes with the exact expanding-torus Fourier weight. -/
noncomputable def expandingProduct (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f g : FourierL2) : FourierL2 :=
  ⟨fun n => (expandingSobolevWeight a k L n : ℂ) * expandingProductCoefficient a k L f g n,
    (lp.memℓp (expandingProductMajorant a k L f g)).mono'
      (weighted_expandingProduct_le_majorant a k L ha ha1 hk hL f g)⟩

theorem expandingProduct_coefficient (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f g : FourierL2)
    (n : frequencyLattice) :
    expandingFourierCoefficient a k L (expandingProduct a k L ha ha1 hk hL f g) n =
      expandingProductCoefficient a k L f g n := by
  apply mul_left_cancel₀ (show (expandingSobolevWeight a k L n : ℂ) ≠ 0 from
    Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a k L hL n).ne')
  exact weight_mul_expandingFourierCoefficient a k L hL (expandingProduct a k L ha ha1 hk hL f g) n

/-- A quantitative norm bound for the two-Young-convolution majorant. -/
theorem expandingProductMajorant_norm_le (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f g : FourierL2) :
    ‖expandingProductMajorant a k L f g‖ ≤
      2 * Real.sqrt (4 ^ k) * expandingEmbeddingBound a k * ‖f‖ * ‖g‖ := by
  have hf := summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL f
  have hg := summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL g
  have hcf := fourierConvolution_norm_le (fun m => (‖expandingFourierCoefficient a k L f m‖ : ℂ))
    (by simpa using hf) (fourierAbsolute g)
  have hcg := fourierConvolution_norm_le (fun m => (‖expandingFourierCoefficient a k L g m‖ : ℂ))
    (by simpa using hg) (fourierAbsolute f)
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm, fourierAbsolute_norm] at hcf hcg
  have hC : 0 ≤ Real.sqrt ((4 : ℝ) ^ k) := Real.sqrt_nonneg _
  calc
    _ = Real.sqrt (4 ^ k) * ‖fourierConvolution
        (fun m => (‖expandingFourierCoefficient a k L f m‖ : ℂ)) (fourierAbsolute g) +
        fourierConvolution (fun m => (‖expandingFourierCoefficient a k L g m‖ : ℂ))
          (fourierAbsolute f)‖ := by
      rw [expandingProductMajorant, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hC]
    _ ≤ Real.sqrt (4 ^ k) *
        (‖fourierConvolution (fun m => (‖expandingFourierCoefficient a k L f m‖ : ℂ))
          (fourierAbsolute g)‖ +
        ‖fourierConvolution (fun m => (‖expandingFourierCoefficient a k L g m‖ : ℂ))
          (fourierAbsolute f)‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) hC
    _ ≤ Real.sqrt (4 ^ k) * ((∑' m, ‖expandingFourierCoefficient a k L f m‖) * ‖g‖ +
        (∑' m, ‖expandingFourierCoefficient a k L g m‖) * ‖f‖) :=
      mul_le_mul_of_nonneg_left (add_le_add hcf hcg) hC
    _ ≤ Real.sqrt (4 ^ k) * ((expandingEmbeddingBound a k * ‖f‖) * ‖g‖ +
        (expandingEmbeddingBound a k * ‖g‖) * ‖f‖) := by
      gcongr
      · exact tsum_norm_expandingFourierCoefficient_le a k L ha ha1 hk hL f
      · exact tsum_norm_expandingFourierCoefficient_le a k L ha ha1 hk hL g
    _ = _ := by ring

/-- The `Y_L` multiplication constant is independent of `L ≥ 1`. -/
theorem expandingProduct_norm_le (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f g : FourierL2) :
    ‖expandingProduct a k L ha ha1 hk hL f g‖ ≤
      2 * Real.sqrt (4 ^ k) * expandingEmbeddingBound a k * ‖f‖ * ‖g‖ := by
  exact (lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (weighted_expandingProduct_le_majorant a k L ha ha1 hk hL f g)).trans
      (expandingProductMajorant_norm_le a k L ha ha1 hk hL f g)

end DefocusingNLS

end OAI
