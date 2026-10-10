import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevTranslationEquation

namespace OAI

/-! # Unit-phase covariance of the Sobolev Schrödinger equation -/

open scoped ComplexConjugate

namespace DefocusingNLS

/-- Multiplication by a constant unit complex phase is an isometry. -/
noncomputable def sobolevPhase (c : Circle) : FourierL2 →ₗᵢ[ℂ] FourierL2 where
  toFun f := (c : ℂ) • f
  map_add' f g := smul_add _ _ _
  map_smul' d f := by
    change (c : ℂ) • (d • f) = d • ((c : ℂ) • f)
    exact smul_comm _ _ _
  norm_map' f := by simp [norm_smul]

@[simp] theorem sobolevPhase_apply (c : Circle) (f : FourierL2) :
    sobolevPhase c f = (c : ℂ) • f := rfl

theorem continuous_sobolevPhase_uncurry :
    Continuous (fun p : Circle × FourierL2 => sobolevPhase p.1 p.2) :=
  (continuous_subtype_val.comp continuous_fst).smul continuous_snd

theorem fourierConjugate_smul (c : ℂ) (f : FourierL2) :
    fourierConjugate (c • f) = conj c • fourierConjugate f := by
  ext n
  simp

/-- Odd powers commute with every constant phase of modulus one. -/
theorem sobolevOddPower_phase (k : ℝ) (hk : 6 < k) (m : ℕ) (c : Circle) (f : FourierL2) :
    sobolevOddPower k hk m (sobolevPhase c f) =
      sobolevPhase c (sobolevOddPower k hk m f) := by
  have hc : (c : ℂ) * conj (c : ℂ) = 1 := by
    rw [Complex.mul_conj, ← Complex.sq_norm]
    simp
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [sobolevOddPower, sobolevPhase_apply] at ih ⊢
    rw [ih, fourierConjugate_smul]
    simp only [sobolevProduct_smul_left, sobolevProduct_smul_right, smul_smul]
    congr 1
    calc
      _ = ((c : ℂ) * conj (c : ℂ)) * (c : ℂ) := by ring
      _ = (c : ℂ) := by rw [hc, one_mul]

theorem sobolevTorusFunction_phase (k : ℝ) (hk : 6 < k) (c : Circle)
    (f : FourierL2) (x : SchrodingerTorus) :
    sobolevTorusFunction k (sobolevPhase c f) x = (c : ℂ) * sobolevTorusFunction k f x := by
  simp only [sobolevTorusFunction_apply k hk, sobolevPhase_apply, map_smul, smul_eq_mul]

/-- The actual strong equation is invariant under unit phase. -/
theorem hasDerivAt_sobolevSchrodinger_phase
    (k : ℝ) (hk : 6 < k) (m : ℕ) (c : Circle) (u : ℝ → FourierL2) (t : ℝ)
    (hu : HasDerivAt (fun s => lowerSobolevInclusion (u s))
      (lowerSobolevGenerator (u t) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u t))) t) :
    HasDerivAt (fun s => lowerSobolevInclusion (sobolevPhase c (u s)))
      (lowerSobolevGenerator (sobolevPhase c (u t)) -
        Complex.I • lowerSobolevInclusion
          (sobolevOddPower k hk m (sobolevPhase c (u t)))) t := by
  have h := hu.const_smul (c : ℂ)
  rw [sobolevOddPower_phase]
  simp only [sobolevPhase_apply, map_smul]
  convert h using 1
  simp only [smul_sub, smul_smul]
  congr 1
  ring_nf

end DefocusingNLS

end OAI
