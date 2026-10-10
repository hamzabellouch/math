import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingEvaluation

namespace OAI

/-! # Canonical transfer between expanding-torus norms

The transfer keeps the physical Fourier coefficients in normalized coordinates
and has the exact growth bound `(M / L)^a` when `1 ≤ L ≤ M`.
-/

open scoped ENNReal

namespace DefocusingNLS

theorem expandingSobolevWeightSq_scale_le (a k L M : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hLM : L ≤ M) (n : frequencyLattice) :
    expandingSobolevWeightSq a k M n ≤
      (M / L) ^ (2 * a) * expandingSobolevWeightSq a k L n := by
  have hLp : 0 < L := by linarith
  have hMp : 0 < M := by linarith
  have hR : 1 ≤ M / L := (le_div_iff₀ hLp).mpr (by simpa using hLM)
  have hRpow : 1 ≤ (M / L) ^ (2 * a) := Real.one_le_rpow hR (by positivity)
  have hlo : M ^ (2 * a) = (M / L) ^ (2 * a) * L ^ (2 * a) := by
    rw [Real.div_rpow hMp.le hLp.le]
    exact (div_mul_cancel₀ _ (Real.rpow_pos_of_pos hLp _).ne').symm
  have hhi : M ^ (12 - 2 * k) ≤ L ^ (12 - 2 * k) :=
    Real.rpow_le_rpow_of_nonpos hLp hLM (by linarith)
  unfold expandingSobolevWeightSq
  rw [hlo, mul_add]
  apply add_le_add
  · exact le_of_eq (mul_assoc _ _ _)
  · calc
      _ ≤ L ^ (12 - 2 * k) * ‖n‖ ^ (2 * k) :=
        mul_le_mul_of_nonneg_right hhi (by positivity)
      _ ≤ (M / L) ^ (2 * a) * (L ^ (12 - 2 * k) * ‖n‖ ^ (2 * k)) :=
        le_mul_of_one_le_left (by positivity) hRpow

theorem expandingSobolevWeight_scale_le (a k L M : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hLM : L ≤ M) (n : frequencyLattice) :
    expandingSobolevWeight a k M n ≤ (M / L) ^ a * expandingSobolevWeight a k L n := by
  have hLp : 0 < L := by linarith
  have hMp : 0 < M := by linarith
  have hQp : 0 < M / L := div_pos hMp hLp
  have hQ : ((M / L) ^ a) ^ 2 = (M / L) ^ (2 * a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQp.le]
    congr 1
    ring
  have h := Real.sqrt_le_sqrt (expandingSobolevWeightSq_scale_le a k L M ha hk hL hLM n)
  rw [← hQ, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.rpow_nonneg hQp.le _)] at h
  unfold expandingSobolevWeight
  calc
    _ ≤ (2 * Real.pi) ^ 6 * ((M / L) ^ a * Real.sqrt (expandingSobolevWeightSq a k L n)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

noncomputable def expandingScaleRatio (a k L M : ℝ) (n : frequencyLattice) : ℝ :=
  expandingSobolevWeight a k M n / expandingSobolevWeight a k L n

theorem expandingScaleRatio_nonneg (a k L M : ℝ)
    (hL : 1 ≤ L) (hLM : L ≤ M) (n : frequencyLattice) :
    0 ≤ expandingScaleRatio a k L M n :=
  (div_pos (expandingSobolevWeight_pos a k M (hL.trans hLM) n)
    (expandingSobolevWeight_pos a k L hL n)).le

theorem expandingScaleRatio_le (a k L M : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hLM : L ≤ M) (n : frequencyLattice) :
    expandingScaleRatio a k L M n ≤ (M / L) ^ a := by
  apply (div_le_iff₀ (expandingSobolevWeight_pos a k L hL n)).mpr
  exact expandingSobolevWeight_scale_le a k L M ha hk hL hLM n

noncomputable def expandingTransferVector (a k L M : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hLM : L ≤ M) (f : FourierL2) : FourierL2 :=
  ⟨fun n => (expandingScaleRatio a k L M n : ℂ) * f n, by
    apply (lp.memℓp (((M / L) ^ a : ℝ) • f)).mono'
    intro n
    simp only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs, norm_mul,
      Complex.norm_real, abs_of_nonneg (expandingScaleRatio_nonneg a k L M hL hLM n)]
    exact mul_le_mul_of_nonneg_right ((expandingScaleRatio_le a k L M ha hk hL hLM n).trans
      (le_abs_self _))
      (norm_nonneg _)⟩

@[simp] theorem expandingTransferVector_apply (a k L M : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hLM : L ≤ M)
    (f : FourierL2) (n : frequencyLattice) :
    expandingTransferVector a k L M ha hk hL hLM f n =
      (expandingScaleRatio a k L M n : ℂ) * f n := rfl

theorem expandingTransferVector_norm_le (a k L M : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hLM : L ≤ M) (f : FourierL2) :
    ‖expandingTransferVector a k L M ha hk hL hLM f‖ ≤ (M / L) ^ a * ‖f‖ := by
  calc
    _ ≤ ‖((M / L) ^ a : ℝ) • f‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      simp only [expandingTransferVector_apply, lp.coeFn_smul, Pi.smul_apply,
        norm_smul, Real.norm_eq_abs, norm_mul, Complex.norm_real,
        abs_of_nonneg (expandingScaleRatio_nonneg a k L M hL hLM n)]
      exact mul_le_mul_of_nonneg_right ((expandingScaleRatio_le a k L M ha hk hL hLM n).trans
      (le_abs_self _))
        (norm_nonneg _)
    _ = _ := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (div_nonneg (by linarith) (by linarith)) a)]

/-- Continuous complex-linear transfer with the physical coefficients fixed. -/
noncomputable def expandingScaleTransfer (a k L M : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hLM : L ≤ M) : FourierL2 →L[ℂ] FourierL2 :=
  LinearMap.mkContinuous
    { toFun := expandingTransferVector a k L M ha hk hL hLM
      map_add' := by
        intro f g
        ext n
        simp only [expandingTransferVector_apply, lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := by
        intro c f
        ext n
        simp only [expandingTransferVector_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
    ((M / L) ^ a) (expandingTransferVector_norm_le a k L M ha hk hL hLM)

theorem expandingScaleTransfer_norm_le (a k L M : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hLM : L ≤ M) :
    ‖expandingScaleTransfer a k L M ha hk hL hLM‖ ≤ (M / L) ^ a := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (Real.rpow_nonneg (div_nonneg (by linarith) (by linarith)) a)
  exact expandingTransferVector_norm_le a k L M ha hk hL hLM

theorem expandingScaleTransfer_coefficient (a k L M : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hLM : L ≤ M)
    (f : FourierL2) (n : frequencyLattice) :
    expandingFourierCoefficient a k M (expandingScaleTransfer a k L M ha hk hL hLM f) n =
      expandingFourierCoefficient a k L f n := by
  change (((expandingSobolevWeight a k M n)⁻¹ : ℝ) : ℂ) *
      ((expandingScaleRatio a k L M n : ℂ) * f n) = _
  unfold expandingScaleRatio expandingFourierCoefficient
  rw [Complex.ofReal_div, Complex.ofReal_inv, Complex.ofReal_inv]
  have hM : (expandingSobolevWeight a k M n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a k M (hL.trans hLM) n).ne'
  have hLn : (expandingSobolevWeight a k L n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a k L hL n).ne'
  field_simp [hM, hLn]

/-- Transfer represents the same function in normalized torus coordinates. -/
theorem expandingScaleTransfer_function (a k L M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hLM : L ≤ M)
    (f : FourierL2) :
    expandingTorusFunction a k M (expandingScaleTransfer a k L M ha hk hL hLM f) =
      expandingTorusFunction a k L f := by
  ext x
  simp only [expandingTorusFunction_apply a k M ha ha1 hk (hL.trans hLM),
    expandingTorusFunction_apply a k L ha ha1 hk hL, expandingScaleTransfer_coefficient]

private theorem expandingCoefficient_injective (a k L : ℝ) (hL : 1 ≤ L) :
    Function.Injective (expandingFourierCoefficient a k L) := by
  intro f g h
  ext n
  have hn := congrFun h n
  have he := congrArg (fun z : ℂ => (expandingSobolevWeight a k L n : ℂ) * z) hn
  simpa only [weight_mul_expandingFourierCoefficient a k L hL] using he

@[simp] theorem expandingScaleTransfer_self (a k L : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) :
    expandingScaleTransfer a k L L ha hk hL le_rfl = ContinuousLinearMap.id ℂ FourierL2 := by
  apply ContinuousLinearMap.ext
  intro f
  apply expandingCoefficient_injective a k L hL
  funext n
  exact expandingScaleTransfer_coefficient a k L L ha hk hL le_rfl f n

/-- Canonical scale changes compose without an additional normalization. -/
theorem expandingScaleTransfer_comp (a k L M N : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hLM : L ≤ M) (hMN : M ≤ N) :
    (expandingScaleTransfer a k M N ha hk (hL.trans hLM) hMN).comp
        (expandingScaleTransfer a k L M ha hk hL hLM) =
      expandingScaleTransfer a k L N ha hk hL (hLM.trans hMN) := by
  apply ContinuousLinearMap.ext
  intro f
  apply expandingCoefficient_injective a k N ((hL.trans hLM).trans hMN)
  funext n
  simp only [ContinuousLinearMap.comp_apply, expandingScaleTransfer_coefficient]

end DefocusingNLS

end OAI
