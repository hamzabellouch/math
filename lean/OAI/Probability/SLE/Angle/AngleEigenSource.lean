import OAI.Probability.SLE.Angle.AngleEigenStopped
import OAI.Probability.SLE.KernelExpectation

namespace OAI

/-! Identification of the localized harmonic eigenfunctions with the
actual stopped Green weight and angle, including paths missing the level. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Polynomial
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma logPolynomialDensity_green_factor (κ c η₀ : ℝ) (P : ℝ[X])
    (q : ℂ × ℝ) (x : ℝ) :
    logPolynomialDensity κ (codimension κ+c) (greenExponent κ) P q x =
      Real.exp (c*(logRadiusClock η₀ q-Real.log 2-η₀))*greenLogDensity κ q x*
        P.eval (logCosine κ q x) := by
  unfold logPolynomialDensity powerLogDensity greenLogDensity
  rw [← Real.exp_add]
  congr 2
  unfold logRadiusClock
  ring

lemma logCosine_logCoordinates (κ b : ℝ) (G : ℝ≥0 → ℂ → ℂ) (z : ℂ)
    (t : ℝ≥0) (hy : 0<(G t z).im) :
    logCosine κ (logLoewnerCoordinates G z t) b=
      Real.cos ((G t z-(Real.sqrt κ*b:ℝ)).arg) := by
  rw [logCosine_eq_angle,Multipoint.logAngle]
  congr 2
  apply Complex.ext
  · simp only [Multipoint.logPoint_re,logCoordinates_re,Complex.sub_re,Complex.ofReal_re]
  · simp only [Multipoint.logPoint_im,logCoordinates_im,Real.exp_log hy,
      Complex.sub_im,Complex.ofReal_im,sub_zero]

lemma logCosine_initial (κ : ℝ) (z : ℂ) (hz : z∈upperHalfPlane) :
    logCosine κ (initialLogCoordinates z) 0=Real.cos z.arg := by
  rw [logCosine_eq_angle,Multipoint.logAngle]
  congr 2
  apply Complex.ext
  · simp [Multipoint.logPoint_re,initialLogCoordinates]
  · simpa [Multipoint.logPoint_im,initialLogCoordinates] using Real.exp_log hz

lemma logPolynomialDensity_initial (κ c : ℝ) (P : ℝ[X])
    (z : ℂ) (hz : z∈upperHalfPlane) :
    logPolynomialDensity κ (codimension κ+c) (greenExponent κ) P (initialLogCoordinates z) 0=
      Real.exp (-c*(Real.log 2+Real.log z.im))*initialGreen κ z*P.eval (Real.cos z.arg) := by
  rw [logPolynomialDensity_green_factor κ c (Real.log z.im),greenLogDensity_initial κ z hz,
    logCosine_initial κ z hz]
  simp only [logRadiusClock,initialLogCoordinates,Complex.add_im,Complex.ofReal_im,
    Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,
    add_zero,zero_add]
  congr 2
  congr 1
  ring

namespace AngularLocalization
variable {Ω : Type*} [MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ}

lemma eigen_eq_source_of_hit (a : AngularLocalization B hm κ z u ε)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z∈upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) γ G F)
    (hh : ω∈a.hit) (n : ℕ) :
    logPolynomialDensity κ (codimension κ+anglePolynomialEigenvalue κ n)
      (greenExponent κ) (angleEigenPolynomial κ n) (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω)=
    Real.exp (anglePolynomialEigenvalue κ n*(u-Real.log 2-Real.log z.im))*
      stoppedGreen κ (fun t => Real.sqrt κ*B t ω) γ G z u*
      (angleEigenPolynomial κ n).eval (Real.cos ((G (radiusLevelTime γ G z u).toNNReal z-
        (Real.sqrt κ*B (radiusLevelTime γ G z u).toNNReal ω:ℝ)).arg)) := by
  have hU := (hBc ω).const_mul (Real.sqrt κ)
  obtain ⟨hl, hR⟩ := a.radius_at_hit hBc hz ω γ G F hw hh
  have ht := radiusLevelTime_eq_of_live_level hU hw z u (a.τ ω) hl hR
  have hq := (a.chart_identification hBc hz ω γ G F hw).2 (a.τ ω) le_rfl
  rw [logPolynomialDensity_green_factor κ _ (Real.log z.im),
    (show logRadiusClock (Real.log z.im) (a.solution.Q (a.τ ω) ω)=u from hh)]
  change Real.exp _*a.weight ω*_=_
  rw [a.weight_eq_stoppedGreen_of_hit hBc hz ω γ G F hw hh,hq,
    logCosine_logCoordinates κ _ G z _ (hw.imag_positive _ z hl),ht,ENNReal.toNNReal_coe]

lemma eigen_small_of_not_hit (a : AngularLocalization B hm κ z u ε)
    (hκ : 0<κ) (hκ8 : κ<8) (n : ℕ) (ω : Ω) (hh : ω∉a.hit) :
    |logPolynomialDensity κ (codimension κ+anglePolynomialEigenvalue κ n)
      (greenExponent κ) (angleEigenPolynomial κ n) (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω)| ≤
    Real.exp ((codimension κ+anglePolynomialEigenvalue κ n)*(u-Real.log 2-Real.log z.im))*
      ε^(greenExponent κ/2)*((n:ℝ)+1)^(n+1) := by
  have hp : 0≤codimension κ+anglePolynomialEigenvalue κ n := by
    apply add_nonneg (codimension_pos κ hκ8).le
    unfold anglePolynomialEigenvalue
    positivity
  have ha := (a.boundary ω).resolve_left hh
  have hε : 0<ε := ha ▸ logAngleSq_pos κ (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω)
  rw [logPolynomialDensity,abs_mul,abs_of_pos (powerLogDensity_pos _ _ _ _ _)]
  apply mul_le_mul _ (angleEigenPolynomial_eval_abs_le hκ n (logCosine_abs_le_one _ _ _))
    (abs_nonneg _) (by positivity)
  rw [powerLogDensity_radius_angle κ _ _ (Real.log z.im),ha]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hε.le _)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (by linarith [(a.inside ω (a.τ ω) le_rfl).1]) hp

end AngularLocalization

lemma localization_eigen_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}
    (a : ∀ j, AngularLocalization B hm κ z u (ε j))
    (hε : Tendsto ε atTop (𝓝 0)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0<κ) (hκ8 : κ<8) (hz : z∈upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) γ G F) (n : ℕ) :
    Tendsto (fun j => logPolynomialDensity κ (codimension κ+anglePolynomialEigenvalue κ n)
      (greenExponent κ) (angleEigenPolynomial κ n) ((a j).solution.Q ((a j).τ ω) ω) (B ((a j).τ ω) ω)) atTop
      (𝓝 (Real.exp (anglePolynomialEigenvalue κ n*(u-Real.log 2-Real.log z.im))*
        stoppedGreen κ (fun t => Real.sqrt κ*B t ω) γ G z u*
        (angleEigenPolynomial κ n).eval (Real.cos ((G (radiusLevelTime γ G z u).toNNReal z-
          (Real.sqrt κ*B (radiusLevelTime γ G z u).toNNReal ω:ℝ)).arg)))) := by
  by_cases hh : ∃ T : ℝ≥0, z∈survivingDomain γ T ∧ fullRadius G T z=(2*z.im)*Real.exp (-u)
  · obtain ⟨T,hT,hR⟩ := hh
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_hit_of_live_level a hε hBc hz ω γ G F hw T hT hR] with j hj
    exact ((a j).eigen_eq_source_of_hit hBc hz ω γ G F hw hj.1 n).symm
  · rw [stoppedGreen_eq_zero_of_no_level κ _ _ _ z u hh,mul_zero,zero_mul]
    have hp : 0<greenExponent κ/2 := by positivity [greenExponent_pos κ hκ hκ8]
    have ht := (((Real.continuousAt_rpow_const 0 (greenExponent κ/2) (Or.inr hp.le)).tendsto.comp hε).const_mul
      (Real.exp ((codimension κ+anglePolynomialEigenvalue κ n)*(u-Real.log 2-Real.log z.im)))).mul_const
      (((n:ℝ)+1)^(n+1))
    simp only [Real.zero_rpow hp.ne',mul_zero,zero_mul] at ht
    apply squeeze_zero_norm _ ht
    intro j
    simpa only [Real.norm_eq_abs,Function.comp_apply] using (a j).eigen_small_of_not_hit hκ hκ8 n ω
      (fun hj => hh ⟨(a j).τ ω,(a j).radius_at_hit hBc hz ω γ G F hw hj⟩)

end SLEExactGauge

end

end OAI
