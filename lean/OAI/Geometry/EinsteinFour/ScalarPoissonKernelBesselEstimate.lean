import OAI.Geometry.EinsteinFour.ScalarPoissonKernelDerivative

namespace OAI

/-! Quantitative L2 realization of the normalized Helmholtz inverse and its
first two coordinate derivatives. The constants retain Mathlib's `2π`
Fourier normalization. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "Linf" => Lp ℂ ∞ (volume : Measure V)

private theorem scalar_norm_fourierInv (f : L2) : ‖𝓕⁻ f‖ = ‖f‖ := by
  rw [← Lp.norm_fourier_eq (𝓕⁻ f), fourier_fourierInv_eq]

/-- A bounded Fourier symbol acts continuously on the actual L2 space. -/
def scalarL2FourierMultiplier (a : Linf) : L2 →L[ℂ] L2 :=
  LinearMap.mkContinuous
    { toFun := fun f => 𝓕⁻ (a • 𝓕 f : L2)
      map_add' := by
        intro f g
        rw [FourierTransform.fourier_add, Lp.add_smul, FourierTransform.fourierInv_add]
      map_smul' := by
        intro c f
        rw [FourierTransform.fourier_smul, ← Lp.smul_comm, FourierTransform.fourierInv_smul]
        rfl }
    ‖a‖ (fun f => by
      change ‖𝓕⁻ (a • 𝓕 f : L2)‖ ≤ _
      rw [scalar_norm_fourierInv]
      exact (Lp.norm_smul_le a (𝓕 f)).trans_eq (by rw [Lp.norm_fourier_eq]))

theorem scalarL2FourierMultiplier_norm (a : Linf) (f : L2) :
    ‖scalarL2FourierMultiplier a f‖ ≤ ‖a‖ * ‖f‖ := by
  change ‖𝓕⁻ (a • 𝓕 f : L2)‖ ≤ _
  rw [scalar_norm_fourierInv]
  exact (Lp.norm_smul_le a (𝓕 f)).trans_eq (by rw [Lp.norm_fourier_eq])

theorem scalarL2FourierMultiplier_distribution (a : V → ℂ)
    (ha : a.HasTemperateGrowth) (haLp : MemLp a ∞ (volume : Measure V)) (f : L2) :
    (scalarL2FourierMultiplier (haLp.toLp a) f : 𝓢'(V, ℂ)) =
      fourierMultiplierCLM ℂ a (f : 𝓢'(V, ℂ)) := by
  change ((𝓕⁻ (haLp.toLp a • 𝓕 f : L2) : L2) : 𝓢'(V, ℂ)) = _
  rw [← Lp.fourierInv_toTemperedDistribution_eq,
    Lp.toTemperedDistribution_smul_eq ha haLp,
    ← Lp.fourier_toTemperedDistribution_eq, fourierMultiplierCLM_apply]

private def besselInverseSymbol (x : V) : ℂ :=
  Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-1 : ℝ))

private def besselFirstSymbol (i : Fin 4) (x : V) : ℂ :=
  Complex.ofReal (x i * (1 + ‖x‖ ^ 2) ^ (-1 : ℝ))

private def besselSecondSymbol (i j : Fin 4) (x : V) : ℂ :=
  Complex.ofReal (x i * x j * (1 + ‖x‖ ^ 2) ^ (-1 : ℝ))

private theorem besselInverseSymbol_temperate : besselInverseSymbol.HasTemperateGrowth := by
  unfold besselInverseSymbol
  fun_prop

private theorem besselFirstSymbol_temperate (i : Fin 4) :
    (besselFirstSymbol i).HasTemperateGrowth := by
  unfold besselFirstSymbol
  simp_rw [← EuclideanSpace.inner_basisFun_real]
  fun_prop

private theorem besselSecondSymbol_temperate (i j : Fin 4) :
    (besselSecondSymbol i j).HasTemperateGrowth := by
  unfold besselSecondSymbol
  simp_rw [← EuclideanSpace.inner_basisFun_real]
  fun_prop

private theorem scalar_coordinate_abs_le (i : Fin 4) (x : V) : |x i| ≤ ‖x‖ := by
  simpa only [EuclideanSpace.inner_basisFun_real,
    (EuclideanSpace.basisFun (Fin 4) ℝ).norm_eq_one, mul_one] using
    abs_real_inner_le_norm x (EuclideanSpace.basisFun (Fin 4) ℝ i)

private theorem besselInverseSymbol_bound (x : V) : ‖besselInverseSymbol x‖ ≤ 1 := by
  simp only [besselInverseSymbol, Real.rpow_neg_one, Complex.norm_real, Real.norm_eq_abs,
    abs_inv, abs_of_pos (show 0 < 1 + ‖x‖ ^ 2 by positivity)]
  exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ‖x‖])

private theorem besselFirstSymbol_bound (i : Fin 4) (x : V) :
    ‖besselFirstSymbol i x‖ ≤ 1 := by
  have hx : 0 < 1 + ‖x‖ ^ 2 := by positivity
  simp only [besselFirstSymbol, Real.rpow_neg_one, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_inv, abs_of_pos hx]
  apply (mul_inv_le_iff₀ hx).mpr
  nlinarith [scalar_coordinate_abs_le i x, sq_nonneg (‖x‖ - 1)]

private theorem besselSecondSymbol_bound (i j : Fin 4) (x : V) :
    ‖besselSecondSymbol i j x‖ ≤ 1 := by
  have hx : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hij : |x i| * |x j| ≤ ‖x‖ ^ 2 := by
    calc
      |x i| * |x j| ≤ ‖x‖ * ‖x‖ :=
        mul_le_mul (scalar_coordinate_abs_le i x) (scalar_coordinate_abs_le j x)
          (abs_nonneg _) (norm_nonneg _)
      _ = _ := (pow_two _).symm
  simp only [besselSecondSymbol, Real.rpow_neg_one, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_inv, abs_of_pos hx]
  apply (mul_inv_le_iff₀ hx).mpr
  linarith

private theorem scalar_symbol_memLp {a : V → ℂ} (ha : a.HasTemperateGrowth)
    (hb : ∀ x, ‖a x‖ ≤ 1) : MemLp a ∞ (volume : Measure V) :=
  memLp_top_of_bound ha.1.continuous.aestronglyMeasurable 1 (.of_forall hb)

private theorem scalar_symbol_Linf_norm {a : V → ℂ} (ha : MemLp a ∞ (volume : Measure V))
    (hb : ∀ x, ‖a x‖ ≤ 1) : ‖ha.toLp a‖ ≤ 1 := by
  rw [Lp.norm_toLp, eLpNorm_exponent_top ha.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one
    (eLpNormEssSup_le_of_ae_bound (.of_forall hb))

/-- The actual L2 inverse of `1 - (2π)⁻² Δ`. -/
def scalarBesselInverseL2 : L2 →L[ℂ] L2 :=
  scalarL2FourierMultiplier
    ((scalar_symbol_memLp besselInverseSymbol_temperate besselInverseSymbol_bound).toLp _)

/-- First distributional derivative of the normalized inverse, realized in L2. -/
def scalarBesselFirstL2 (i : Fin 4) : L2 →L[ℂ] L2 :=
  (2 * Real.pi * Complex.I) • scalarL2FourierMultiplier
    ((scalar_symbol_memLp (besselFirstSymbol_temperate i) (besselFirstSymbol_bound i)).toLp _)

/-- Second distributional derivative of the normalized inverse, realized in L2. -/
def scalarBesselSecondL2 (i j : Fin 4) : L2 →L[ℂ] L2 :=
  (2 * Real.pi * Complex.I) ^ 2 • scalarL2FourierMultiplier
    ((scalar_symbol_memLp (besselSecondSymbol_temperate i j)
      (besselSecondSymbol_bound i j)).toLp _)

theorem scalarBesselInverseL2_norm (f : L2) : ‖scalarBesselInverseL2 f‖ ≤ ‖f‖ := by
  exact (scalarL2FourierMultiplier_norm _ f).trans
    (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
      (scalar_symbol_Linf_norm _ besselInverseSymbol_bound) (norm_nonneg f)))

private theorem scalar_fourier_constant_norm :
    ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
  simp [abs_of_pos Real.pi_pos]

private theorem scalar_L2_multiplier_contraction {a : V → ℂ}
    (ha : MemLp a ∞ (volume : Measure V)) (hb : ∀ x, ‖a x‖ ≤ 1) (f : L2) :
    ‖scalarL2FourierMultiplier (ha.toLp a) f‖ ≤ ‖f‖ := by
  exact (scalarL2FourierMultiplier_norm _ f).trans (by
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right (scalar_symbol_Linf_norm ha hb) (norm_nonneg f)))

theorem scalarBesselFirstL2_norm (i : Fin 4) (f : L2) :
    ‖scalarBesselFirstL2 i f‖ ≤ (2 * Real.pi) * ‖f‖ := by
  rw [scalarBesselFirstL2, _root_.smul_apply, norm_smul,
    scalar_fourier_constant_norm]
  exact mul_le_mul_of_nonneg_left
    (scalar_L2_multiplier_contraction _ (besselFirstSymbol_bound i) f) (by positivity)

theorem scalarBesselSecondL2_norm (i j : Fin 4) (f : L2) :
    ‖scalarBesselSecondL2 i j f‖ ≤ (2 * Real.pi) ^ 2 * ‖f‖ := by
  rw [scalarBesselSecondL2, _root_.smul_apply, norm_smul,
    norm_pow, scalar_fourier_constant_norm]
  exact mul_le_mul_of_nonneg_left
    (scalar_L2_multiplier_contraction _ (besselSecondSymbol_bound i j) f) (by positivity)

theorem scalarBesselInverseL2_distribution (f : L2) :
    (scalarBesselInverseL2 f : 𝓢'(V, ℂ)) = besselPotential V ℂ (-2) f := by
  rw [scalarBesselInverseL2, scalarL2FourierMultiplier_distribution]
  unfold besselPotential besselInverseSymbol
  norm_num only [show (-2 : ℝ) / 2 = -1 by norm_num]
  exact besselInverseSymbol_temperate

private theorem scalar_derivative_multiplier (i : Fin 4) (a : V → ℂ)
    (ha : a.HasTemperateGrowth) (u : 𝓢'(V, ℂ)) :
    scalarCoordinateDerivative i (fourierMultiplierCLM ℂ a u) =
      (2 * Real.pi * Complex.I) •
        fourierMultiplierCLM ℂ (fun x => a x * (x i : ℂ)) u := by
  rw [scalarCoordinateDerivative, lineDeriv_eq_fourierMultiplierCLM,
    fourierMultiplierCLM_fourierMultiplierCLM_apply ha (by fun_prop)]
  apply congrArg (fun b : V → ℂ =>
    (2 * Real.pi * Complex.I) • fourierMultiplierCLM ℂ b u)
  funext x
  simp only [Pi.mul_apply, EuclideanSpace.inner_basisFun_real]

private theorem scalarBesselInverseL2_symbol (f : L2) :
    (scalarBesselInverseL2 f : 𝓢'(V, ℂ)) =
      fourierMultiplierCLM ℂ besselInverseSymbol (f : 𝓢'(V, ℂ)) := by
  exact scalarL2FourierMultiplier_distribution _ besselInverseSymbol_temperate _ f

private theorem scalar_L2_smul_distribution (c : ℂ) (f : L2) :
    ((c • f : L2) : 𝓢'(V, ℂ)) = c • (f : 𝓢'(V, ℂ)) :=
  (Lp.toTemperedDistributionCLM ℂ volume 2).map_smul c f

private theorem scalarBesselFirstL2_symbol (i : Fin 4) (f : L2) :
    (scalarBesselFirstL2 i f : 𝓢'(V, ℂ)) =
      (2 * Real.pi * Complex.I) •
        fourierMultiplierCLM ℂ (besselFirstSymbol i) (f : 𝓢'(V, ℂ)) := by
  rw [scalarBesselFirstL2, _root_.smul_apply, scalar_L2_smul_distribution,
    scalarL2FourierMultiplier_distribution _ (besselFirstSymbol_temperate i)]

private theorem scalarBesselSecondL2_symbol (i j : Fin 4) (f : L2) :
    (scalarBesselSecondL2 i j f : 𝓢'(V, ℂ)) =
      (2 * Real.pi * Complex.I) ^ 2 •
        fourierMultiplierCLM ℂ (besselSecondSymbol i j) (f : 𝓢'(V, ℂ)) := by
  rw [scalarBesselSecondL2, _root_.smul_apply, scalar_L2_smul_distribution,
    scalarL2FourierMultiplier_distribution _ (besselSecondSymbol_temperate i j)]

theorem scalarBesselFirstL2_distribution (i : Fin 4) (f : L2) :
    (scalarBesselFirstL2 i f : 𝓢'(V, ℂ)) =
      scalarCoordinateDerivative i (scalarBesselInverseL2 f : 𝓢'(V, ℂ)) := by
  rw [scalarBesselFirstL2_symbol, scalarBesselInverseL2_symbol,
    scalar_derivative_multiplier _ _ besselInverseSymbol_temperate]
  apply congrArg (fun a : V → ℂ =>
    (2 * Real.pi * Complex.I) • fourierMultiplierCLM ℂ a (f : 𝓢'(V, ℂ)))
  funext x
  simp only [besselFirstSymbol, besselInverseSymbol, ← Complex.ofReal_mul]
  congr 1
  ring

theorem scalarBesselSecondL2_distribution (i j : Fin 4) (f : L2) :
    (scalarBesselSecondL2 i j f : 𝓢'(V, ℂ)) =
      scalarCoordinateDerivative i
        (scalarCoordinateDerivative j (scalarBesselInverseL2 f : 𝓢'(V, ℂ))) := by
  rw [← scalarBesselFirstL2_distribution, scalarBesselFirstL2_symbol,
    scalarBesselSecondL2_symbol, scalarCoordinateDerivative, LineDeriv.lineDerivOp_smul]
  change _ = (2 * Real.pi * Complex.I) • scalarCoordinateDerivative i _
  rw [scalar_derivative_multiplier _ _ (besselFirstSymbol_temperate j),
    smul_smul, ← pow_two]
  apply congrArg (fun a : V → ℂ =>
    (2 * Real.pi * Complex.I) ^ 2 • fourierMultiplierCLM ℂ a (f : 𝓢'(V, ℂ)))
  funext x
  simp only [besselSecondSymbol, besselFirstSymbol, ← Complex.ofReal_mul]
  congr 1
  ring

/-- The L2 construction solves the actual normalized distributional equation. -/
theorem scalarBesselInverseL2_helmholtz (f : L2) :
    normalizedScalarHelmholtz (scalarBesselInverseL2 f : 𝓢'(V, ℂ)) = (f : 𝓢'(V, ℂ)) := by
  rw [scalarBesselInverseL2_distribution, normalizedScalarHelmholtz_eq_bessel,
    besselPotential_besselPotential_apply]
  norm_num

/-- The constructed inverse has two Sobolev derivatives. -/
theorem scalarBesselInverseL2_memSobolev (f : L2) :
    MemSobolev 2 2 (scalarBesselInverseL2 f : 𝓢'(V, ℂ)) := by
  have hf : MemSobolev 0 2 (f : 𝓢'(V, ℂ)) :=
    memSobolev_zero_iff.mpr ⟨f, rfl⟩
  simpa only [zero_add] using
    normalizedScalarHelmholtz_gain_two (scalarBesselInverseL2_helmholtz f) hf

end
end PositiveEinsteinFour.Geometry

end OAI
