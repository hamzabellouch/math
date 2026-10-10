import OAI.Analysis.OperatorAlgebra.ScalarLpIntervalCommutant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

namespace OAI

/-! A bounded spectral chart on each interval [-n,n]. This gives the
localized continuous multipliers needed to test the modular weight, using
only commutation with the actual character group. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped CStarAlgebra

namespace WeakPureInfiniteness

def scalarPhaseCosine (r c : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t : ℝ => (Real.cos (r * t + c) : ℂ)) (by fun_prop) 1 (by
      intro t
      simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one (r * t + c))

@[simp] lemma scalarPhaseCosine_apply (r c t : ℝ) :
    scalarPhaseCosine r c t = (Real.cos (r * t + c) : ℂ) := rfl

lemma scalarPhaseCosine_selfAdjoint (r c : ℝ) : IsSelfAdjoint (scalarPhaseCosine r c) := by
  change star (scalarPhaseCosine r c) = scalarPhaseCosine r c
  ext t
  simp only [BoundedContinuousFunction.coe_star, Pi.star_apply, scalarPhaseCosine_apply,
    Complex.star_def, Complex.conj_ofReal]

lemma scalarPhaseCosine_character (r c : ℝ) :
    scalarPhaseCosine r c = (2 : ℂ)⁻¹ •
      ((BoundedRecovery.spectralCharacter c 1) • BoundedRecovery.spectralCharacter r +
        star ((BoundedRecovery.spectralCharacter c 1) • BoundedRecovery.spectralCharacter r)) := by
  ext t
  simp only [scalarPhaseCosine_apply, BoundedContinuousFunction.coe_smul,
    BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_star,
    Pi.add_apply, Pi.star_apply, smul_eq_mul,
    BoundedRecovery.spectralCharacter_apply, mul_one, Complex.exp_ofReal_mul_I,
    star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
    Real.cos_add, Complex.ofReal_sub]
  simp only [Complex.ofReal_mul]
  ring_nf
  simp [Complex.I_sq]
  ring

lemma scalarLp_commute_phaseCosine
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hc : ∀ s, Commute T
      (modularDualUnitary (H := ℂ) volume s : Lp ℂ 2 volume →L[ℂ] Lp ℂ 2 volume))
    (r c : ℝ) : Commute T (scalarLpRepresentation volume (scalarPhaseCosine r c)) := by
  rw [scalarPhaseCosine_character, map_smul, map_add, map_star, map_smul]
  have h₁ : Commute T (scalarLpRepresentation volume (BoundedRecovery.spectralCharacter r)) := by
    simpa only [scalarLpRepresentation_character] using hc r
  have h₂ : Commute T (star (scalarLpRepresentation volume (BoundedRecovery.spectralCharacter r))) := by
    rw [← map_star, BoundedRecovery.spectralCharacter_star]
    simpa only [scalarLpRepresentation_character] using hc (-r)
  rw [star_smul]
  exact ((h₁.smul_right _).add_right (h₂.smul_right _)).smul_right _

lemma scalarPhaseCosine_cfc_apply (r c t : ℝ) (f : ℂ → ℂ) (hf : Continuous f) :
    cfc f (scalarPhaseCosine r c) t = f (Real.cos (r * t + c)) := by
  have h := (boundedFunctionEval t).map_cfc f (scalarPhaseCosine r c) hf.continuousOn
    (ha := (scalarPhaseCosine_selfAdjoint r c).isStarNormal)
    (hφa := ((scalarPhaseCosine_selfAdjoint r c).map (boundedFunctionEval t)).isStarNormal)
  change (cfc f (scalarPhaseCosine r c)) t =
    cfc f (algebraMap ℂ ℂ (Real.cos (r * t + c) : ℂ)) at h
  rw [cfc_algebraMap] at h
  exact h

lemma scalarLp_commute_phaseCosine_cfc
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hc : ∀ s, Commute T
      (modularDualUnitary (H := ℂ) volume s : Lp ℂ 2 volume →L[ℂ] Lp ℂ 2 volume))
    (r c : ℝ) (f : ℂ → ℂ) (hf : Continuous f) :
    Commute T (scalarLpRepresentation volume (cfc f (scalarPhaseCosine r c))) := by
  have : ContinuousFunctionalCalculus ℂ
      (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
      (A := Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
  rw [(scalarLpRepresentation volume).map_cfc f (scalarPhaseCosine r c) hf.continuousOn
    (ha := (scalarPhaseCosine_selfAdjoint r c).isStarNormal)
    (hφa := ((scalarPhaseCosine_selfAdjoint r c).map (scalarLpRepresentation volume)).isStarNormal)]
  exact ((scalarPhaseCosine_selfAdjoint r c).map (scalarLpRepresentation volume)).commute_cfc
    (scalarLp_commute_phaseCosine T hc r c).symm f |>.symm

def intervalChartRate (n : ℕ) : ℝ := Real.pi / (2 * n + 1)

lemma intervalChartRate_pos (n : ℕ) : 0 < intervalChartRate n := by
  unfold intervalChartRate
  positivity

lemma intervalChart_inverse (n : ℕ) {t : ℝ} (ht : t ∈ Icc (-(n : ℝ)) n) :
    Real.arccos (Real.cos (intervalChartRate n * t + intervalChartRate n * n)) /
      intervalChartRate n - n = t := by
  have hr := intervalChartRate_pos n
  have he : intervalChartRate n * (2 * (n : ℝ) + 1) = Real.pi := by
    unfold intervalChartRate
    field_simp
  have h₀ : 0 ≤ intervalChartRate n * t + intervalChartRate n * n := by nlinarith [ht.1]
  have hπ : intervalChartRate n * t + intervalChartRate n * n ≤ Real.pi := by
    nlinarith [ht.2]
  rw [Real.arccos_cos h₀ hπ]
  field_simp
  ring

def intervalChartFunction (n : ℕ) (f : BoundedContinuousFunction ℝ ℂ) :
    BoundedContinuousFunction ℝ ℂ :=
  cfc (fun z : ℂ => f (Real.arccos z.re / intervalChartRate n - n))
    (scalarPhaseCosine (intervalChartRate n) (intervalChartRate n * n))

lemma intervalChartFunction_apply (n : ℕ) (f : BoundedContinuousFunction ℝ ℂ)
    {t : ℝ} (ht : t ∈ Icc (-(n : ℝ)) n) : intervalChartFunction n f t = f t := by
  rw [intervalChartFunction, scalarPhaseCosine_cfc_apply]
  · simp only [Complex.ofReal_re, intervalChart_inverse n ht]
  · exact f.continuous.comp ((Real.continuous_arccos.comp Complex.continuous_re).div_const
      (intervalChartRate n) |>.sub continuous_const)

lemma scalarLp_commute_intervalChart
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hc : ∀ s, Commute T
      (modularDualUnitary (H := ℂ) volume s : Lp ℂ 2 volume →L[ℂ] Lp ℂ 2 volume))
    (n : ℕ) (f : BoundedContinuousFunction ℝ ℂ) :
    Commute T (scalarLpRepresentation volume (intervalChartFunction n f)) := by
  apply scalarLp_commute_phaseCosine_cfc T hc
  exact f.continuous.comp ((Real.continuous_arccos.comp Complex.continuous_re).div_const
    (intervalChartRate n) |>.sub continuous_const)

lemma intervalChartFunction_localized (n : ℕ) (f : BoundedContinuousFunction ℝ ℂ) :
    scalarIntervalProjection n * scalarLpRepresentation volume (intervalChartFunction n f) =
      scalarIntervalProjection n * scalarLpRepresentation volume f := by
  apply ContinuousLinearMap.ext
  intro g
  apply Lp.ext
  filter_upwards [scalarIntervalProjection_ae n
      (scalarLpRepresentation volume (intervalChartFunction n f) g),
    scalarIntervalProjection_ae n (scalarLpRepresentation volume f g),
    scalarLpMultiplier_ae volume (intervalChartFunction n f) g,
    scalarLpMultiplier_ae volume f g] with t h₁ h₂ h₃ h₄
  change (scalarIntervalProjection n (scalarLpRepresentation volume
      (intervalChartFunction n f) g)) t =
    (scalarIntervalProjection n (scalarLpRepresentation volume f g)) t
  change (scalarLpRepresentation volume (intervalChartFunction n f) g) t =
    intervalChartFunction n f t * g t at h₃
  change (scalarLpRepresentation volume f g) t = f t * g t at h₄
  rw [h₁, h₂]
  by_cases ht : t ∈ Icc (-(n : ℝ)) n
  · rw [indicator_of_mem ht, indicator_of_mem ht, h₃, h₄,
      intervalChartFunction_apply n f ht]
  · rw [indicator_of_notMem ht, indicator_of_notMem ht]

/-- Every continuous scalar multiplier commutes with the Fourier compression
of a core element. The proof uses bounded spectral charts and interval
exhaustion, so it imposes no global uniform approximation premise. -/
theorem scalarLp_commute_continuousMultiplier
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hc : ∀ s, Commute T
      (modularDualUnitary (H := ℂ) volume s : Lp ℂ 2 volume →L[ℂ] Lp ℂ 2 volume))
    (f : BoundedContinuousFunction ℝ ℂ) :
    Commute T (scalarLpRepresentation volume f) := by
  apply commute_of_strong_limit T (scalarLpRepresentation volume f)
    (fun n => scalarIntervalProjection n * scalarLpRepresentation volume f)
  · intro n
    rw [← intervalChartFunction_localized n f]
    exact (scalarLp_commute_intervalProjection T hc n).mul_right
      (scalarLp_commute_intervalChart T hc n f)
  · intro g
    exact scalarIntervalProjection_strong (scalarLpRepresentation volume f g)

end WeakPureInfiniteness

end

end OAI
