import OAI.Probability.SLE.Angle.AngleHarmonicStopped
import OAI.Probability.SLE.Angle.AngleEigenBounds
import OAI.Probability.SLE.AngularPowerDynkin

namespace OAI

/-! Exact stopped mean identities for every angular eigenpolynomial. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Polynomial
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma ClippedLogSolution.stopped_harmonic_bounded
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P) (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω=0)
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (Φ : (ℂ × ℝ) × ℝ → ℝ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hgen : ∀ q x, fderiv ℝ (fun r => Φ (r,x)) q
      (physicalLogLoewnerField (Real.sqrt κ*x) q) +
      (1/2:ℝ)*iteratedDeriv 2 (fun y => Φ (q,y)) x=0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T)
    (hin : ∀ ω t, t ≤ τ ω → (c.Q t ω).1.im ∈ Icc lo hi)
    (K : ℝ) (hval : ∀ ω t, t ≤ τ ω → |Φ (c.Q t ω,B t ω)| ≤ K) :
    Integrable (fun ω => Φ (c.Q (τ ω) ω,B (τ ω) ω)) P ∧
      (∫ ω, Φ (c.Q (τ ω) ω,B (τ ω) ω) ∂P)=Φ (q₀,0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨σn, hsn, hsle, hsB, hstable⟩ := exists_brownian_compact_stops B hm hBc hB0 τ hτ T hb
  have hmean (n : ℕ) : Integrable (fun ω => Φ (c.Q (σn n ω) ω,B (σn n ω) ω)) P ∧
      (∫ ω, Φ (c.Q (σn n ω) ω,B (σn n ω) ω) ∂P)=Φ (q₀,0) := by
    let R := max (‖q₀‖+c.L*T) ((n:ℝ)+1)
    apply c.stopped_harmonic_compact hB hBm hBc Φ hΦ hgen R
      (le_trans (by positivity : (0:ℝ)≤(n:ℝ)+1) (le_max_right _ _))
      (σn n) (hsn n) T (fun ω => (hsle n ω).trans (hb ω))
    intro ω t ht
    refine ⟨?_,hin ω t (ht.trans (hsle n ω))⟩
    rw [Prod.norm_def, max_le_iff,Real.norm_eq_abs]
    exact ⟨(c.norm_le ω t T (ht.trans ((hsle n ω).trans (hb ω)))).trans (le_max_left _ _),
      (hsB n ω t ht).trans (le_max_right _ _)⟩
  have hτm := stopping_time_measurable_nnreal hτ
  have hQm := c.measurable.comp ((measurable_coe_nnreal_real.comp hτm).prodMk measurable_id)
  have hbm := hBm.comp (hτm.prodMk measurable_id)
  have hi : Integrable (fun ω => Φ (c.Q (τ ω) ω,B (τ ω) ω)) P :=
    Integrable.of_bound (hΦ.continuous.measurable.comp (hQm.prodMk hbm)).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hval ω (τ ω) le_rfl)
  refine ⟨hi,?_⟩
  have hlim := integral_tendsto_stopped_eval (fun t ω => Φ (c.Q t ω,B t ω)) σn τ
    (fun n => (hmean n).1.aestronglyMeasurable) K
    (fun n ω => hval ω (σn n ω) (hsle n ω)) hstable
  have he : (fun n => ∫ ω, Φ (c.Q (σn n ω) ω,B (σn n ω) ω) ∂P)=fun _ => Φ (q₀,0) :=
    funext (fun n => (hmean n).2)
  rw [he] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

lemma logEigenDensity_bound {κ : ℝ} (hκ : 0<κ) (hκ8 : κ<8)
    (n : ℕ) (η₀ u : ℝ) (q : ℂ × ℝ) (x : ℝ)
    (hu : logRadiusClock η₀ q ≤ u) :
    |logPolynomialDensity κ (codimension κ+anglePolynomialEigenvalue κ n)
      (greenExponent κ) (angleEigenPolynomial κ n) q x| ≤
      Real.exp ((codimension κ+anglePolynomialEigenvalue κ n)*(u-Real.log 2-η₀))*
        ((n:ℝ)+1)^(n+1) := by
  have hn : 0≤anglePolynomialEigenvalue κ n := by
    unfold anglePolynomialEigenvalue
    positivity
  rw [logPolynomialDensity,abs_mul,abs_of_pos (powerLogDensity_pos _ _ _ _ _)]
  exact mul_le_mul
    (powerLogDensity_le_radius κ _ _ η₀ u (add_nonneg (codimension_pos κ hκ8).le hn)
      (greenExponent_pos κ hκ hκ8).le q x hu)
    (angleEigenPolynomial_eval_abs_le hκ n (logCosine_abs_le_one κ q x))
    (abs_nonneg _) (Real.exp_pos _).le

lemma AngularLocalization.mean_eigen
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P) (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω=0)
    {κ : ℝ} (hκ : 0<κ) (hκ8 : κ<8) {z : ℂ} {u ε : ℝ}
    (a : AngularLocalization B hm κ z u ε) (n : ℕ) :
    Integrable (fun ω => logPolynomialDensity κ (codimension κ+anglePolynomialEigenvalue κ n)
      (greenExponent κ) (angleEigenPolynomial κ n) (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω)) P ∧
    (∫ ω, logPolynomialDensity κ (codimension κ+anglePolynomialEigenvalue κ n)
      (greenExponent κ) (angleEigenPolynomial κ n) (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω) ∂P)=
    logPolynomialDensity κ (codimension κ+anglePolynomialEigenvalue κ n)
      (greenExponent κ) (angleEigenPolynomial κ n) (initialLogCoordinates z) 0 := by
  apply a.solution.stopped_harmonic_bounded hB hBm hBc hB0
    (fun p => logPolynomialDensity κ (codimension κ+anglePolynomialEigenvalue κ n)
      (greenExponent κ) (angleEigenPolynomial κ n) p.1 p.2)
    (logPolynomialDensity_contDiff _ _ _ _) (logEigenDensity_generator_zero hκ n)
    a.τ a.stopping a.T a.bounded (fun ω t ht => (a.inside ω t ht).2.2)
    (Real.exp ((codimension κ+anglePolynomialEigenvalue κ n)*(u-Real.log 2-Real.log z.im))*
      ((n:ℝ)+1)^(n+1))
  exact fun ω t ht => logEigenDensity_bound hκ hκ8 n _ _ _ _ (a.inside ω t ht).1

end SLEExactGauge

end

end OAI
