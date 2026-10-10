import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProductCommutator

namespace OAI

/-! # A uniform high-frequency estimate for the actual product commutator -/

open scoped ENNReal

namespace DefocusingNLS

noncomputable def expandingCommutatorMoment (L : ℝ) (N : ℕ)
    (c : frequencyLattice → ℂ) (m : frequencyLattice) : ℝ :=
  ‖c m‖ * (‖m‖ / L) * (2 + ‖m‖ / L) ^ N

theorem expandingCommutatorMoment_nonneg (L : ℝ) (hL : 1 ≤ L) (N : ℕ)
    (c : frequencyLattice → ℂ) (m : frequencyLattice) :
    0 ≤ expandingCommutatorMoment L N c m := by
  unfold expandingCommutatorMoment
  positivity

theorem expandingProductCommutator_high_norm_le (a L R : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < ((N + 1 : ℕ) : ℝ))
    (hL : 1 ≤ L) (hR : 1 ≤ R) (j : Fin (N + 1) → Fin 12) (q f : FourierL2)
    (hM : Summable (expandingCommutatorMoment L N (expandingFourierCoefficient a ((N + 1 : ℕ) : ℝ) L q)))
    (hf : ∀ n : frequencyLattice, ‖n‖ < R * L → f n = 0) :
    ‖expandingProductCommutator a L (N + 1) ha ha1 hN hL j q f‖ ≤
      ((N + 1 : ℕ) / R) *
        (∑' m, expandingCommutatorMoment L N (expandingFourierCoefficient a ((N + 1 : ℕ) : ℝ) L q) m) * ‖f‖ := by
  let K := expandingCommutatorMoment L N (expandingFourierCoefficient a ((N + 1 : ℕ) : ℝ) L q)
  let c : ℝ := (N + 1 : ℕ) / R
  let g := fourierConvolution (fun m => (K m : ℂ)) (fourierAbsolute f)
  have hK (m : frequencyLattice) : 0 ≤ K m := expandingCommutatorMoment_nonneg L hL N _ m
  have hc : 0 ≤ c := div_nonneg (by positivity) (by linarith)
  have hKsum : Summable (fun m => ‖(K m : ℂ)‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK _)] using hM
  have hgn (n : frequencyLattice) : ‖g n‖ = ∑' m, K m * ‖f (n - m)‖ := by
    dsimp only [g]
    rw [fourierConvolution_apply _ hKsum]
    simp only [fourierAbsolute_apply, ← Complex.ofReal_mul, ← Complex.ofReal_tsum,
      Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (tsum_nonneg (fun m => mul_nonneg (hK m) (norm_nonneg _)))
  have hpoint (n : frequencyLattice) :
      ‖expandingProductCommutator a L (N + 1) ha ha1 hN hL j q f n‖ ≤ c * ‖g n‖ := by
    let F := fun m => expandingFourierCoefficient a ((N + 1 : ℕ) : ℝ) L q m *
      expandingOrderedDifference a L (N + 1) j m (n - m) * f (n - m)
    have hterm (m : frequencyLattice) : ‖F m‖ ≤ c * (K m * ‖f (n - m)‖) := by
      by_cases h : ‖n - m‖ < R * L
      · simp only [F, hf _ h, mul_zero, norm_zero]
        exact le_rfl
      · have hd := expandingOrderedDifference_high a L R N hL hR j m (n - m) (le_of_not_gt h)
        have hb := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hd (norm_nonneg (expandingFourierCoefficient a ((N + 1 : ℕ) : ℝ) L q m)))
          (norm_nonneg (f (n - m)))
        dsimp only [F, K, c, expandingCommutatorMoment]
        rw [norm_mul, norm_mul]
        convert hb using 1; ring
    have hs : Summable (fun m => K m * ‖f (n - m)‖) :=
      Summable.of_nonneg_of_le (fun m => mul_nonneg (hK m) (norm_nonneg _))
        (fun m => mul_le_mul_of_nonneg_left
          (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) f (n - m)) (hK m))
        (hM.mul_right ‖f‖)
    have hF : Summable (fun m => ‖F m‖) :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _) hterm (hs.mul_left c)
    rw [expandingProductCommutator_kernel]
    change ‖∑' m, F m‖ ≤ c * ‖g n‖
    calc
      _ ≤ ∑' m, ‖F m‖ := norm_tsum_le_tsum_norm hF
      _ ≤ ∑' m, c * (K m * ‖f (n - m)‖) := hF.tsum_le_tsum hterm (hs.mul_left c)
      _ = c * ‖g n‖ := by rw [tsum_mul_left, hgn]
  have hnorm : ‖expandingProductCommutator a L (N + 1) ha ha1 hN hL j q f‖ ≤ ‖(c : ℂ) • g‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro n
    simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hc] using hpoint n
  have hg := fourierConvolution_norm_le (fun m => (K m : ℂ)) hKsum (fourierAbsolute f)
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK _), fourierAbsolute_norm] at hg
  calc
    _ ≤ c * ‖g‖ := by simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc] using hnorm
    _ ≤ c * ((∑' m, K m) * ‖f‖) := mul_le_mul_of_nonneg_left hg hc
    _ = _ := by dsimp only [c, K]; ring

end DefocusingNLS

end OAI
