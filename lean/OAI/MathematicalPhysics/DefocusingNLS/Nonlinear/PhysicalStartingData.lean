import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevTranslation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSobolevEquiv
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingBlowupObservation
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffFamilyContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffGlobalOrbit

namespace OAI

/-! # Physical initial data in the moving similarity coordinates -/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

noncomputable def physicalStartingAmplitude (a : ℝ) (L : Radius) (θ : ℝ) : ℂ :=
  Complex.exp ((-θ : ℝ) * Complex.I) * (L.1 ^ (-2 * a) : ℝ)

@[simp] theorem physicalStartingAmplitude_norm (a : ℝ) (L : Radius) (θ : ℝ) :
    ‖physicalStartingAmplitude a L θ‖ = L.1 ^ (-2 * a) := by
  rw [physicalStartingAmplitude, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [L.2]) _)]

noncomputable def physicalStartingOperator (a k : ℝ) (ha : 0 < a) (hk : 8 < k)
    (L : Radius) (θ : ℝ) (x : SchrodingerTorus) : FourierL2 →L[ℂ] FourierL2 :=
  physicalStartingAmplitude a L θ •
    (expandingScaleTransfer a k 1 L.1 ha hk le_rfl L.2).comp
      ((sobolevToExpanding a k ha hk).comp (sobolevTranslation x).toContinuousLinearMap)

theorem physicalStartingOperator_norm_le (a k : ℝ) (ha : 0 < a) (hk : 8 < k)
    (L : Radius) (θ : ℝ) (x : SchrodingerTorus) :
    ‖physicalStartingOperator a k ha hk L θ x‖ ≤ ‖sobolevToExpanding a k ha hk‖ := by
  have hp : L.1 ^ (-2 * a) * L.1 ^ a ≤ 1 := by
    rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one L.2)]
    exact Real.rpow_le_one_of_one_le_of_nonpos L.2 (by linarith)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  change ‖physicalStartingAmplitude a L θ •
    expandingScaleTransfer a k 1 L.1 ha hk le_rfl L.2
      (sobolevToExpanding a k ha hk (sobolevTranslation x f))‖ ≤ _
  rw [norm_smul, physicalStartingAmplitude_norm]
  calc
    _ ≤ L.1 ^ (-2 * a) * (L.1 ^ a *
        (‖sobolevToExpanding a k ha hk‖ * ‖f‖)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith [L.2]) _)
      have ht := (expandingScaleTransfer a k 1 L.1 ha hk le_rfl L.2).le_opNorm
        (sobolevToExpanding a k ha hk (sobolevTranslation x f))
      apply ht.trans
      have hb := expandingScaleTransfer_norm_le a k 1 L.1 ha hk le_rfl L.2
      simp only [div_one] at hb
      apply mul_le_mul hb _ (norm_nonneg _) (Real.rpow_nonneg (by linarith [L.2]) _)
      simpa only [(sobolevTranslation x).norm_map] using
        (sobolevToExpanding a k ha hk).le_opNorm (sobolevTranslation x f)
    _ ≤ 1 * (‖sobolevToExpanding a k ha hk‖ * ‖f‖) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := one_mul _

attribute [local irreducible] physicalStartingOperator expandingScaleTransfer sobolevToExpanding
  sobolevTranslation

theorem continuous_physicalStartingOperator_apply (a k : ℝ) (ha : 0 < a) (hk : 8 < k) :
    Continuous (fun p : (Radius × ℝ × SchrodingerTorus) × FourierL2 =>
      physicalStartingOperator a k ha hk p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  unfold physicalStartingOperator
  have hx : Continuous (fun p : (Radius × ℝ × SchrodingerTorus) × FourierL2 =>
      p.1.2.2) := continuous_snd.comp (continuous_snd.comp continuous_fst)
  have ht : Continuous (fun p : (Radius × ℝ × SchrodingerTorus) × FourierL2 =>
      sobolevTranslation p.1.2.2 p.2) :=
    continuous_sobolevTranslation_uncurry.comp (hx.prodMk continuous_snd)
  have hv := (sobolevToExpanding a k ha hk).continuous.comp ht
  have hc := ((continuous_expandingScaleTransfer_from_one a k ha hk).comp
    (continuous_fst.comp continuous_fst)).clm_apply hv
  have hA : Continuous (fun p : (Radius × ℝ × SchrodingerTorus) × FourierL2 =>
      physicalStartingAmplitude a p.1.1 p.1.2.1) := by
    unfold physicalStartingAmplitude
    have hpow : Continuous (fun p : (Radius × ℝ × SchrodingerTorus) × FourierL2 =>
        p.1.1.1 ^ (-2 * a)) :=
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).rpow_const
        (fun p => Or.inl (lt_of_lt_of_le zero_lt_one p.1.1.2).ne'))
    exact (Complex.continuous_exp.comp (by fun_prop)).mul
      (Complex.continuous_ofReal.comp hpow)
  exact hA.smul hc

noncomputable def physicalStartingPerturbation (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (L : Radius) (θ : ℝ) (x : SchrodingerTorus) (f : FourierL2) : FourierL2 :=
  physicalStartingOperator a k ha hk L θ x f -
    sampledCutoffProfileAtRadius a k ha1 hk χ hχ Q hQ L

theorem physicalStartingPerturbation_data_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (L : Radius) (θ : ℝ) (x : SchrodingerTorus) (f g : FourierL2) :
    ‖physicalStartingPerturbation a k ha ha1 hk χ hχ Q hQ L θ x f -
      physicalStartingPerturbation a k ha ha1 hk χ hχ Q hQ L θ x g‖ ≤
      ‖sobolevToExpanding a k ha hk‖ * ‖f - g‖ := by
  have he : physicalStartingPerturbation a k ha ha1 hk χ hχ Q hQ L θ x f -
      physicalStartingPerturbation a k ha ha1 hk χ hχ Q hQ L θ x g =
      physicalStartingOperator a k ha hk L θ x (f - g) := by
    simp only [physicalStartingPerturbation, map_sub]
    abel
  rw [he]
  exact ((physicalStartingOperator a k ha hk L θ x).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (physicalStartingOperator_norm_le a k ha hk L θ x) (norm_nonneg _))

theorem continuous_physicalStartingPerturbation (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    Continuous (fun p : (Radius × ℝ × SchrodingerTorus) × FourierL2 =>
      physicalStartingPerturbation a k ha ha1 hk χ hχ Q hQ p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  unfold physicalStartingPerturbation
  exact (continuous_physicalStartingOperator_apply a k ha hk).sub
    ((continuous_cutoffProfile_sample a k ha ha1 hk χ hχ Q hQ).comp
      (continuous_fst.comp continuous_fst))

end DefocusingNLS

end OAI
