import OAI.Geometry.RCD.Coordinates.WeightedBilinearMeasure
import OAI.Geometry.RCD.Harmonic.HarmonicGrams
import OAI.Geometry.RCD.Sobolev.CompactLaplacian
import OAI.Geometry.RCD.Harmonic.GramDirectionalError

namespace OAI

/-! # Small Bochner mass from the centered local Gram error

The weak Bochner identity and a cutoff bound the full positive measure.
Subtracting the constant Gram field exposes the small normalized error.
-/

open Set MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [ProperSpace X] in
/-- Small normalized gradient error and small curvature force small full
mass on every set where the test cutoff equals one. -/
theorem bochner_mass_le_of_local_error (U : E →L[ℝ] SobolevSpace μ hQ)
    (M : PositiveBilinearMeasure X E) (φ : X →ᵇ ℝ)
    (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (S s : Set X) (hSfin : μ S ≠ ∞)
    (hs : MeasurableSet s) (hφone : ∀ x ∈ s, φ x = 1)
    (q : X → ℝ) {D epsilon kappa : ℝ} (hD : 0 ≤ D) (hk : 0 ≤ kappa)
    (hqmeas : AEStronglyMeasurable q (μ.restrict S))
    (hq : ∀ᵐ x ∂μ.restrict S, |q x| ≤ D)
    (hqzero : ∫ x in S, q x ∂μ = 0)
    (herror : ∀ v : E, ∫ x in S,
      |localGamma μ hQ (U v) (U v) x - ‖v‖ ^ 2| ∂μ ≤ epsilon * ‖v‖ ^ 2)
    (hsource : ∀ v : E,
      ⟪v, M.weightedOperator φ v⟫_ℝ =
        (1 / 2 : ℝ) * (∫ x in S, localGamma μ hQ (U v) (U v) x * q x ∂μ) +
        kappa * ∫ x in S, φ x * localGamma μ hQ (U v) (U v) x ∂μ)
    (v : E) :
    ⟪v, M.massOperator s v⟫_ℝ ≤
      (D * epsilon / 2 + kappa * (epsilon + μ.real S)) * ‖v‖ ^ 2 := by
  let : IsFiniteMeasure (μ.restrict S) := ⟨by simpa only [Measure.restrict_apply_univ] using hSfin.lt_top⟩
  let f := localGamma μ hQ (U v) (U v)
  let e := fun x => f x - ‖v‖ ^ 2
  have hif : IntegrableOn f S μ := (localGamma_memL1 μ hQ (U v) (U v)).integrableOn
  have hie : IntegrableOn e S μ := hif.sub (integrable_const _)
  have hqn : ∀ᵐ x ∂μ.restrict S, ‖q x‖ ≤ D := by simpa only [Real.norm_eq_abs] using hq
  have hiq : IntegrableOn q S μ := Integrable.of_bound hqmeas D hqn
  have hifq : IntegrableOn (fun x => f x * q x) S μ := by
    exact (hif.bdd_mul hqmeas hqn).congr (Filter.Eventually.of_forall fun x => mul_comm (q x) (f x))
  have hcenter : (∫ x in S, e x * q x ∂μ) = ∫ x in S, f x * q x ∂μ := by
    dsimp only [e]
    simp only [sub_mul]
    rw [integral_sub hifq (hiq.const_mul _), integral_const_mul, hqzero, mul_zero, sub_zero]
  have hcut : ⟪v, M.massOperator s v⟫_ℝ ≤ ⟪v, M.weightedOperator φ v⟫_ℝ := by
    simpa only [one_mul] using M.massOperator_le_weightedOperator φ
      (fun x => (hφ x).1) s hs 1 (fun x hx => (hφone x hx).ge) v
  have hqterm : |∫ x in S, e x * q x ∂μ| ≤ D * epsilon * ‖v‖ ^ 2 := by
    have hb := norm_integral_le_of_norm_le (hie.abs.const_mul D) (show
        ∀ᵐ x ∂μ.restrict S, ‖e x * q x‖ ≤ D * |e x| from by
      filter_upwards [hq] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [abs_nonneg (e x)])
    rw [integral_const_mul, Real.norm_eq_abs] at hb
    exact hb.trans (by simpa only [e, f, mul_assoc] using
      mul_le_mul_of_nonneg_left (herror v) hD)
  have hmass : (∫ x in S, f x ∂μ) ≤ (epsilon + μ.real S) * ‖v‖ ^ 2 := by
    have habs := (le_abs_self (∫ x in S, e x ∂μ)).trans abs_integral_le_integral_abs
    have he := herror v
    have hsplit : (∫ x in S, e x ∂μ) = (∫ x in S, f x ∂μ) - μ.real S * ‖v‖ ^ 2 := by
      rw [integral_sub hif (integrable_const _)]
      simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
    rw [hsplit] at habs
    nlinarith
  have hφint : (∫ x in S, φ x * f x ∂μ) ≤ ∫ x in S, f x ∂μ := by
    have hiφ : IntegrableOn (fun x => φ x * f x) S μ :=
      hif.bdd_mul φ.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall φ.norm_coe_le_norm)
    apply integral_mono_ae hiφ hif
    filter_upwards [ae_restrict_of_ae (localGamma_self μ hQ (U v))] with x hx
    dsimp only [f]
    rw [hx]
    exact mul_le_of_le_one_left (sq_nonneg _) (hφ x).2
  rw [hsource] at hcut
  change ⟪v, M.massOperator s v⟫_ℝ ≤
    (1 / 2 : ℝ) * (∫ x in S, f x * q x ∂μ) + kappa * (∫ x in S, φ x * f x ∂μ) at hcut
  rw [← hcenter] at hcut
  have hcurv := mul_le_mul_of_nonneg_left (hφint.trans hmass) hk
  have hlin := (le_abs_self (∫ x in S, e x * q x ∂μ)).trans hqterm
  change ⟪v, M.massOperator s v⟫_ℝ ≤ _
  nlinarith

/-- Coordinatewise Gram errors suffice for the full mass estimate. The
actual weak Laplacian of the compact cutoff supplies its zero integral,
and finite-dimensional polarization supplies every direction. -/
theorem bochner_mass_le_of_coordinate_errors [IsFiniteMeasureOnCompacts μ]
    {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (M : PositiveBilinearMeasure X (Euclidean n)) (φ : X →ᵇ ℝ)
    (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) (p : X) {R : ℝ} (hR : 0 < R)
    (hφsupp : ∀ x, R < dist p x → φ x = 0)
    (ψ : SobolevSpace μ hQ) (hψ : SobolevSpace.toLp μ hQ ψ =ᵐ[μ] φ)
    (q : Lp ℝ 2 μ) (hd : IsWeakLaplacian μ hQ ψ q)
    (hqsupp : ∀ᵐ x ∂μ, R < dist p x → q x = 0)
    (s : Set X) (hs : MeasurableSet s) (hφone : ∀ x ∈ s, φ x = 1)
    {D epsilon kappa : ℝ} (hD : 0 ≤ D) (heps : 0 ≤ epsilon) (hk : 0 ≤ kappa)
    (hq : ∀ᵐ x ∂μ, |q x| ≤ D)
    (herror : ∀ i j : Fin n, ∫ x in Metric.closedBall p R,
      |localGamma μ hQ (u i) (u j) x - (if i = j then 1 else 0)| ∂μ ≤ epsilon)
    (hsource : ∀ v : Euclidean n,
      ⟪v, M.weightedOperator φ v⟫_ℝ =
        (1 / 2 : ℝ) * (∫ x in Metric.closedBall p R,
          localGamma μ hQ (sobolevColumnMap μ hQ u v) (sobolevColumnMap μ hQ u v) x * q x ∂μ) +
        kappa * ∫ x in Metric.closedBall p R,
          φ x * localGamma μ hQ (sobolevColumnMap μ hQ u v) (sobolevColumnMap μ hQ u v) x ∂μ)
    (v : Euclidean n) :
    ⟪v, M.massOperator s v⟫_ℝ ≤
      (D * ((n : ℝ) ^ 2 * epsilon) / 2 +
        kappa * ((n : ℝ) ^ 2 * epsilon + μ.real (Metric.closedBall p R))) * ‖v‖ ^ 2 := by
  have hu : ∀ᵐ x ∂μ, R < dist p x → SobolevSpace.toLp μ hQ ψ x = 0 := by
    filter_upwards [hψ] with x hx hr
    exact hx.trans (hφsupp x hr)
  have hzero := integral_weakLaplacian_eq_zero μ hQ ψ q hd p hR hu hqsupp
  have hout : ∀ᵐ x ∂μ, x ∉ Metric.closedBall p R → q x = 0 := by
    filter_upwards [hqsupp] with x hx hr
    exact hx (by simpa only [Metric.mem_closedBall, dist_comm, not_le] using hr)
  have hzeroS : ∫ x in Metric.closedBall p R, q x ∂μ = 0 :=
    (setIntegral_eq_integral_of_ae_compl_eq_zero hout).trans hzero
  exact bochner_mass_le_of_local_error μ hQ (sobolevColumnMap μ hQ u) M φ hφ
    (Metric.closedBall p R) s (isCompact_closedBall p R).measure_lt_top.ne hs hφone q hD hk
    (Lp.aestronglyMeasurable q).restrict (ae_restrict_of_ae hq) hzeroS
    (directional_gram_error_le μ hQ u (Metric.closedBall p R)
      (isCompact_closedBall p R).measure_lt_top.ne heps herror) hsource v

end RegularPointCoordinates

end

end OAI
