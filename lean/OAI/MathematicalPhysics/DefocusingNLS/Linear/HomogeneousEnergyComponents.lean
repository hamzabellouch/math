import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreeOperator

namespace OAI

/-! # The two exact homogeneous energy components

The low and high Sobolev energies are bounded real-linear observations of
the actual weighted Fourier Hilbert space. Their squared norms add to the
full Y norm, with the manuscript's Plancherel normalization.
-/

open MeasureTheory
open scoped SchwartzMap ENNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousSobolevWeight (s : ℝ) (ξ : E) : ℝ :=
  ((2 * Real.pi) ^ (12 : ℕ))⁻¹ * ‖ξ‖ ^ (2 * s)

noncomputable def homogeneousSobolevMeasure (s : ℝ) : Measure E :=
  volume.withDensity (fun ξ => ENNReal.ofReal (homogeneousSobolevWeight s ξ))

theorem homogeneousSobolevWeight_nonneg (s : ℝ) (ξ : E) :
    0 ≤ homogeneousSobolevWeight s ξ := by
  unfold homogeneousSobolevWeight
  positivity

theorem continuous_homogeneousSobolevWeight (s : ℝ) (hs : 0 ≤ s) :
    Continuous (homogeneousSobolevWeight s) := by
  exact continuous_const.mul (continuous_norm.rpow_const (fun _ => Or.inr (by positivity)))

theorem homogeneousFourierMeasure_eq_components (a k : ℝ) (ha1 : a < 1) (_hk : 8 < k) :
    homogeneousFourierMeasure a k =
      homogeneousSobolevMeasure (6 - a) + homogeneousSobolevMeasure k := by
  unfold homogeneousFourierMeasure homogeneousSobolevMeasure
  have hw : (fun ξ => ENNReal.ofReal (homogeneousFourierWeight a k ξ)) =
      (fun ξ => ENNReal.ofReal (homogeneousSobolevWeight (6 - a) ξ)) +
        (fun ξ => ENNReal.ofReal (homogeneousSobolevWeight k ξ)) := by
    funext ξ
    rw [Pi.add_apply, ← ENNReal.ofReal_add (homogeneousSobolevWeight_nonneg _ _)
      (homogeneousSobolevWeight_nonneg _ _)]
    congr 1
    unfold homogeneousFourierWeight homogeneousSobolevWeight
    ring
  rw [hw]
  exact withDensity_add_left
    (continuous_homogeneousSobolevWeight (6 - a) (by linarith)).measurable.ennreal_ofReal _

theorem homogeneousLowMeasure_le (a k : ℝ) (ha1 : a < 1) (hk : 8 < k) :
    homogeneousSobolevMeasure (6 - a) ≤ homogeneousFourierMeasure a k := by
  rw [homogeneousFourierMeasure_eq_components a k ha1 hk]
  exact Measure.le_add_right le_rfl

theorem homogeneousHighMeasure_le (a k : ℝ) (ha1 : a < 1) (hk : 8 < k) :
    homogeneousSobolevMeasure k ≤ homogeneousFourierMeasure a k := by
  rw [homogeneousFourierMeasure_eq_components a k ha1 hk]
  exact Measure.le_add_left le_rfl

noncomputable def homogeneousLowEnergy (a k : ℝ) (ha1 : a < 1) (hk : 8 < k) :
    HomogeneousY a k →L[ℝ] Lp ℂ 2 (homogeneousSobolevMeasure (6 - a)) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa only [one_smul] using homogeneousLowMeasure_le a k ha1 hk)

noncomputable def homogeneousHighEnergy (a k : ℝ) (ha1 : a < 1) (hk : 8 < k) :
    HomogeneousY a k →L[ℝ] Lp ℂ 2 (homogeneousSobolevMeasure k) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa only [one_smul] using homogeneousHighMeasure_le a k ha1 hk)

theorem homogeneousLowEnergy_ae (a k : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (f : HomogeneousY a k) :
    homogeneousLowEnergy a k ha1 hk f =ᵐ[homogeneousSobolevMeasure (6 - a)] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _

theorem homogeneousHighEnergy_ae (a k : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (f : HomogeneousY a k) :
    homogeneousHighEnergy a k ha1 hk f =ᵐ[homogeneousSobolevMeasure k] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _

theorem homogeneousLowEnergy_norm_le (a k : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (f : HomogeneousY a k) : ‖homogeneousLowEnergy a k ha1 hk f‖ ≤ ‖f‖ := by
  have h : ‖homogeneousLowEnergy a k ha1 hk‖ ≤ 1 := by
    apply (Lp.norm_LpToLpOfMeasureLeSMul_le (c := (1 : ℝ≥0∞)) (by simp)
      (show homogeneousSobolevMeasure (6 - a) ≤ 1 • homogeneousFourierMeasure a k by
        simpa only [one_smul] using homogeneousLowMeasure_le a k ha1 hk)).trans
    simp
  calc
    _ ≤ ‖homogeneousLowEnergy a k ha1 hk‖ * ‖f‖ :=
      (homogeneousLowEnergy a k ha1 hk).le_opNorm f
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right h (norm_nonneg f)
    _ = ‖f‖ := one_mul _

theorem homogeneousHighEnergy_norm_le (a k : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (f : HomogeneousY a k) : ‖homogeneousHighEnergy a k ha1 hk f‖ ≤ ‖f‖ := by
  have h : ‖homogeneousHighEnergy a k ha1 hk‖ ≤ 1 := by
    apply (Lp.norm_LpToLpOfMeasureLeSMul_le (c := (1 : ℝ≥0∞)) (by simp)
      (show homogeneousSobolevMeasure k ≤ 1 • homogeneousFourierMeasure a k by
        simpa only [one_smul] using homogeneousHighMeasure_le a k ha1 hk)).trans
    simp
  calc
    _ ≤ ‖homogeneousHighEnergy a k ha1 hk‖ * ‖f‖ :=
      (homogeneousHighEnergy a k ha1 hk).le_opNorm f
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right h (norm_nonneg f)
    _ = ‖f‖ := one_mul _

private theorem l2_norm_sq_integral (μ : Measure E) (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ ξ, ‖f ξ‖ ^ 2 ∂μ := by
  have h := real_inner_self_eq_norm_sq f
  rw [L2.inner_def] at h
  simpa only [real_inner_self_eq_norm_sq] using h.symm

attribute [local irreducible] homogeneousLowEnergy homogeneousHighEnergy

theorem homogeneousEnergy_norm_sq (a k : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (f : HomogeneousY a k) :
    ‖f‖ ^ 2 = ‖homogeneousLowEnergy a k ha1 hk f‖ ^ 2 +
      ‖homogeneousHighEnergy a k ha1 hk f‖ ^ 2 := by
  let F : E → ℂ := f
  have hl : (fun ξ => ‖homogeneousLowEnergy a k ha1 hk f ξ‖ ^ 2) =ᵐ[
      homogeneousSobolevMeasure (6 - a)] (fun ξ => ‖F ξ‖ ^ 2) := by
    filter_upwards [homogeneousLowEnergy_ae a k ha1 hk f] with ξ hξ
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hξ
  have hh : (fun ξ => ‖homogeneousHighEnergy a k ha1 hk f ξ‖ ^ 2) =ᵐ[
      homogeneousSobolevMeasure k] (fun ξ => ‖F ξ‖ ^ 2) := by
    filter_upwards [homogeneousHighEnergy_ae a k ha1 hk f] with ξ hξ
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hξ
  have hil : Integrable (fun ξ => ‖F ξ‖ ^ 2) (homogeneousSobolevMeasure (6 - a)) :=
    ((Lp.memLp (homogeneousLowEnergy a k ha1 hk f)).integrable_norm_pow
      (p := 2) (by norm_num)).congr hl
  have hih : Integrable (fun ξ => ‖F ξ‖ ^ 2) (homogeneousSobolevMeasure k) :=
    ((Lp.memLp (homogeneousHighEnergy a k ha1 hk f)).integrable_norm_pow
      (p := 2) (by norm_num)).congr hh
  calc
    ‖f‖ ^ 2 = ∫ ξ, ‖F ξ‖ ^ 2 ∂homogeneousFourierMeasure a k :=
      l2_norm_sq_integral _ f
    _ = ∫ ξ, ‖F ξ‖ ^ 2 ∂(homogeneousSobolevMeasure (6 - a) +
        homogeneousSobolevMeasure k) := congrArg (fun μ : Measure E => ∫ ξ, ‖F ξ‖ ^ 2 ∂μ)
          (homogeneousFourierMeasure_eq_components a k ha1 hk)
    _ = (∫ ξ, ‖F ξ‖ ^ 2 ∂homogeneousSobolevMeasure (6 - a)) +
        ∫ ξ, ‖F ξ‖ ^ 2 ∂homogeneousSobolevMeasure k := integral_add_measure hil hih
    _ = _ := by rw [← integral_congr_ae hl, ← integral_congr_ae hh,
      ← l2_norm_sq_integral, ← l2_norm_sq_integral]

private theorem sobolevEnergy_norm_sq_of_ae (s : ℝ) (hs : 0 ≤ s)
    (ψ : 𝓢(E, ℂ)) (g : Lp ℂ 2 (homogeneousSobolevMeasure s))
    (hg : g =ᵐ[homogeneousSobolevMeasure s] ψ) :
    ‖g‖ ^ 2 = ((2 * Real.pi) ^ (12 : ℕ))⁻¹ * homogeneousFrequencyEnergy s ψ := by
  have he : (fun ξ => ‖g ξ‖ ^ 2) =ᵐ[homogeneousSobolevMeasure s]
      (fun ξ => ‖ψ ξ‖ ^ 2) := by
    filter_upwards [hg] with ξ hξ
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hξ
  rw [l2_norm_sq_integral, integral_congr_ae he]
  unfold homogeneousSobolevMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuous_homogeneousSobolevWeight s hs).measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (homogeneousSobolevWeight_nonneg s _), smul_eq_mul]
  simp only [homogeneousSobolevWeight, mul_assoc, integral_const_mul, homogeneousFrequencyEnergy]

theorem homogeneousLowEnergy_Schwartz_norm_sq (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ψ : 𝓢(E, ℂ)) :
    ‖homogeneousLowEnergy a k ha1 hk (homogeneousFrequencyEmbedding a k ha ha1 hk ψ)‖ ^ 2 =
      ((2 * Real.pi) ^ (12 : ℕ))⁻¹ * homogeneousFrequencyEnergy (6 - a) ψ := by
  let := homogeneousFourierMeasure_temperate a k ha ha1 hk
  apply sobolevEnergy_norm_sq_of_ae (6 - a) (by linarith)
  exact (homogeneousLowEnergy_ae a k ha1 hk _).trans
    ((SchwartzMap.coeFn_toLp ψ 2 (homogeneousFourierMeasure a k)).filter_mono
      (Measure.absolutelyContinuous_of_le (homogeneousLowMeasure_le a k ha1 hk)).ae_le)

theorem homogeneousHighEnergy_Schwartz_norm_sq (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ψ : 𝓢(E, ℂ)) :
    ‖homogeneousHighEnergy a k ha1 hk (homogeneousFrequencyEmbedding a k ha ha1 hk ψ)‖ ^ 2 =
      ((2 * Real.pi) ^ (12 : ℕ))⁻¹ * homogeneousFrequencyEnergy k ψ := by
  let := homogeneousFourierMeasure_temperate a k ha ha1 hk
  apply sobolevEnergy_norm_sq_of_ae k (by linarith)
  exact (homogeneousHighEnergy_ae a k ha1 hk _).trans
    ((SchwartzMap.coeFn_toLp ψ 2 (homogeneousFourierMeasure a k)).filter_mono
      (Measure.absolutelyContinuous_of_le (homogeneousHighMeasure_le a k ha1 hk)).ae_le)

end DefocusingNLS

end OAI
