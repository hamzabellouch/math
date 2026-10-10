import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevMultiplication

namespace OAI

/-! # Complex conjugation in the Fourier Sobolev model -/

open scoped ENNReal ComplexConjugate

namespace DefocusingNLS

/-- Conjugating a torus function conjugates its coefficients and reverses frequency. -/
noncomputable def fourierConjugate (f : FourierL2) : FourierL2 :=
  ⟨fun n => conj (f (-n)), by
    apply memℓp_gen
    simpa only [Complex.norm_conj, Function.comp_def, Equiv.neg_apply] using
      (Equiv.neg frequencyLattice).summable_iff.mpr
        ((lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩

@[simp] theorem fourierConjugate_apply (f : FourierL2) (n : frequencyLattice) :
    fourierConjugate f n = conj (f (-n)) := rfl

@[simp] theorem fourierConjugate_involutive (f : FourierL2) :
    fourierConjugate (fourierConjugate f) = f := by
  ext n
  simp

@[simp] theorem fourierConjugate_norm (f : FourierL2) : ‖fourierConjugate f‖ = ‖f‖ := by
  have h1 := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (fourierConjugate f)
  have h2 := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) f
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, fourierConjugate_apply, Complex.norm_conj] at h1 h2
  have heq : ‖fourierConjugate f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [h1, h2]
    exact (Equiv.neg frequencyLattice).tsum_eq (fun n => ‖f n‖ ^ 2)
  nlinarith [norm_nonneg f, norm_nonneg (fourierConjugate f)]

/-- Conjugation of torus functions is a continuous real-linear map on `H^k`. -/
noncomputable def sobolevConjugation : FourierL2 →L[ℝ] FourierL2 :=
  LinearIsometry.toContinuousLinearMap
    { toFun := fourierConjugate
      map_add' := by intro f g; ext n; simp
      map_smul' := by intro c f; ext n; simp [Algebra.smul_def]
      norm_map' := fourierConjugate_norm }

@[simp] theorem sobolevConjugation_apply (f : FourierL2) :
    sobolevConjugation f = fourierConjugate f := rfl

theorem sobolevFourierCoefficient_conjugate (k : ℝ) (f : FourierL2)
    (n : frequencyLattice) :
    sobolevFourierCoefficient k (fourierConjugate f) n =
      conj (sobolevFourierCoefficient k f (-n)) := by
  simp [sobolevFourierCoefficient, Algebra.smul_def]

theorem frequencyCoordinates_neg (n : frequencyLattice) (j : Fin 12) :
    frequencyCoordinates (-n) j = -frequencyCoordinates n j := by
  apply Int.cast_injective (α := ℝ)
  simp only [Int.cast_neg, frequencyCoordinates_coe]
  rfl

theorem torusCharacter_neg (n : frequencyLattice) (x : SchrodingerTorus) :
    torusCharacter (-n) x = conj (torusCharacter n x) := by
  change (∏ j, fourier (frequencyCoordinates (-n) j) (x j)) =
    conj (∏ j, fourier (frequencyCoordinates n j) (x j))
  simp only [frequencyCoordinates_neg, fourier_neg, map_prod]

theorem sobolevTorusFunction_conjugate (k : ℝ) (hk : 6 < k) (f : FourierL2)
    (x : SchrodingerTorus) :
    sobolevTorusFunction k (fourierConjugate f) x = conj (sobolevTorusFunction k f x) := by
  rw [sobolevTorusFunction_eq_tsum k hk, sobolevTorusFunction_eq_tsum k hk, Complex.conj_tsum,
    ← (Equiv.neg frequencyLattice).tsum_eq
      (fun n => sobolevFourierCoefficient k (fourierConjugate f) n * torusCharacter n x)]
  simp only [Equiv.neg_apply, sobolevFourierCoefficient_conjugate, neg_neg,
    torusCharacter_neg, map_mul]

end DefocusingNLS

end OAI
