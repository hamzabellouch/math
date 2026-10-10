import OAI.Geometry.RCD.Sobolev.ResidualBochnerMass
import OAI.Geometry.RCD.Harmonic.PinchingFromProjection
import OAI.Geometry.RCD.Harmonic.MeanDirectionFromPairings

namespace OAI

/-! # Directional pinching from the actual full residual mass -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X E F : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The full measure of the actual coordinate displacement is controlled
by the Poisson-difference mass, the residual gradient and the constant-direction
error. The residual mass is derived from its Bochner equation and the cutoff. -/
theorem directional_mass_from_cutoff_residual
    (U : F →L[ℝ] SobolevSpace μ hQ) (A : E →L[ℝ] F)
    (M : PositiveBilinearMeasure X F) (a : F) (b δ : E)
    {p : X} {r ρ C κ β d P K : ℝ} {L : ℝ≥0}
    (χ : GoodLaplacianCutoff μ hQ p ρ C) (hρ : 0 < ρ) (hρr : ρ < r)
    (hC : 0 ≤ C) (hκ : 0 ≤ κ) (hK : 0 ≤ K)
    (hvol : 0 < μ.real (ball p ρ))
    (hnormal : sobolevMeanGram μ hQ (U.comp A) (ball p ρ) measurableSet_ball =
      ContinuousLinearMap.id ℝ E)
    (G : LocalHarmonicEnergy μ hQ U M κ p r L (a - A b))
    (hgradient : ∀ᵐ x ∂μ.restrict (closedBall p (2 * ρ)),
      localGamma μ hQ (U (a - A b)) (U (a - A b)) x ≤ β)
    (hdirection : ‖meanGradientVector μ hQ (U.comp A) (ball p ρ)
      measurableSet_ball (U a) - δ‖ ^ 2 ≤ d)
    (hraw : ⟪a, M.massOperator (ball p ρ) a⟫_ℝ ≤ P)
    (hupper : ∀ v, ⟪A v, M.massOperator (ball p ρ) (A v)⟫_ℝ ≤ K * ‖v‖ ^ 2) :
    ⟪A δ, M.massOperator (ball p ρ) (A δ)⟫_ℝ ≤
      4 * (P + ((C / ρ ^ 2) / 2 + κ) * β * μ.real (closedBall p (2 * ρ))) +
        4 * K * (d + β) := by
  let D := M.massOperator (ball p ρ)
  let w := a - A b
  let Q := ((C / ρ ^ 2) / 2 + κ) * β * μ.real (closedBall p (2 * ρ))
  have hw : U w = U a - (U.comp A) b := by simp [w]
  have hmassw : ⟪w, D w⟫_ℝ ≤ Q :=
    χ.mass_le_of_gradient μ hQ hρ hρr hC hκ G hgradient
  have hmassb : ⟪A b, D (A b)⟫_ℝ ≤ 2 * (P + Q) := by
    have htri := M.measure_add_le a (-w) (ball p ρ) measurableSet_ball
    rw [M.measure_real _ _ measurableSet_ball, M.measure_real _ _ measurableSet_ball,
      M.measure_real _ _ measurableSet_ball] at htri
    have hab : a + -w = A b := by dsimp only [w]; abel
    rw [hab] at htri
    simp only [map_neg, inner_neg_left, inner_neg_right, neg_neg] at htri
    change ⟪A b, D (A b)⟫_ℝ ≤ _ at htri
    change ⟪a, D a⟫_ℝ ≤ P at hraw
    linarith
  have hfin : μ (ball p ρ) < ∞ :=
    (measure_mono (show ball p ρ ⊆ closedBall p ρ from ball_subset_closedBall)).trans_lt
      (isCompact_closedBall p ρ).measure_lt_top
  let : IsFiniteMeasure (μ.restrict (ball p ρ)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfin⟩
  have hgradball : ∀ᵐ x ∂μ.restrict (ball p ρ),
      localGamma μ hQ (U w) (U w) x ≤ β := by
    exact ae_restrict_of_ae_restrict_of_subset
      ((ball_subset_closedBall).trans (closedBall_subset_closedBall (by linarith))) hgradient
  have hint : (∫ x in ball p ρ, localGamma μ hQ (U w) (U w) x ∂μ) ≤ β * μ.real (ball p ρ) := by
    calc
      _ ≤ ∫ _x in ball p ρ, β ∂μ :=
        integral_mono_ae (localGamma_memL1 μ hQ (U w) (U w)).integrableOn
          (integrable_const _) hgradball
      _ = _ := by simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, mul_comm]
  have henergy : (μ.real (ball p ρ))⁻¹ * ∫ x in ball p ρ,
      (SobolevSpace.minimalSlope μ hQ (U a - (U.comp A) b) x) ^ 2 ∂μ ≤ β := by
    have heq : (∫ x in ball p ρ, (SobolevSpace.minimalSlope μ hQ (U a - (U.comp A) b) x) ^ 2 ∂μ) =
        ∫ x in ball p ρ, localGamma μ hQ (U w) (U w) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (localGamma_self μ hQ (U w))] with x hx
      rw [hw] at hx ⊢
      exact hx.symm
    rw [heq]
    have hbound := mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hvol.le)
    calc
      _ ≤ _ := hbound
      _ = β := by field_simp
  let D' : E →L[ℝ] E := A.adjoint.comp (D.comp A)
  have hD' : D'.IsPositive := (M.massOperator_isPositive _ measurableSet_ball).adjoint_conj A
  have hpair (v : E) : ⟪v, D' v⟫_ℝ = ⟪A v, D (A v)⟫_ℝ := by
    simp only [D', ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  have hpinch := directional_mass_of_projection μ hQ (U.comp A) (ball p ρ)
    measurableSet_ball hnormal (U a) b δ D' hD' (m := 2 * (P + Q)) hK henergy hdirection
    (by rw [hpair]; exact hmassb) (fun v => by rw [hpair]; exact hupper v)
  rw [hpair] at hpinch
  change ⟪A δ, D (A δ)⟫_ℝ ≤ _
  dsimp only [Q] at hpinch
  linarith

/-- A coordinate gradient bound also supplies the full mass upper bound
used in coefficient transfer, through the same local Bochner family.
No separate trace or coordinate mass estimate is assumed. -/
theorem directional_mass_from_gradient_bounds
    (U : F →L[ℝ] SobolevSpace μ hQ) (A : E →L[ℝ] F)
    (M : PositiveBilinearMeasure X F) (a : F) (b δ : E)
    {p : X} {r ρ C κ β d P H : ℝ} {L : ℝ≥0}
    (χ : GoodLaplacianCutoff μ hQ p ρ C) (hρ : 0 < ρ) (hρr : ρ < r)
    (hC : 0 ≤ C) (hκ : 0 ≤ κ) (hH : 0 ≤ H)
    (hvol : 0 < μ.real (ball p ρ))
    (hnormal : sobolevMeanGram μ hQ (U.comp A) (ball p ρ) measurableSet_ball =
      ContinuousLinearMap.id ℝ E)
    (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)
    (hgradient : ∀ᵐ x ∂μ.restrict (closedBall p (2 * ρ)),
      localGamma μ hQ (U (a - A b)) (U (a - A b)) x ≤ β)
    (hcoordinates : ∀ v, ∀ᵐ x ∂μ.restrict (closedBall p (2 * ρ)),
      localGamma μ hQ (U (A v)) (U (A v)) x ≤ H * ‖v‖ ^ 2)
    (hdirection : ‖meanGradientVector μ hQ (U.comp A) (ball p ρ)
      measurableSet_ball (U a) - δ‖ ^ 2 ≤ d)
    (hraw : ⟪a, M.massOperator (ball p ρ) a⟫_ℝ ≤ P) :
    let F := ((C / ρ ^ 2) / 2 + κ) * μ.real (closedBall p (2 * ρ))
    ⟪A δ, M.massOperator (ball p ρ) (A δ)⟫_ℝ ≤
      4 * (P + F * β) + 4 * (F * H) * (d + β) := by
  dsimp only
  let F₀ := ((C / ρ ^ 2) / 2 + κ) * μ.real (closedBall p (2 * ρ))
  have hF₀ : 0 ≤ F₀ := by dsimp only [F₀]; positivity
  have hupper (v : E) : ⟪A v, M.massOperator (ball p ρ) (A v)⟫_ℝ ≤
      (F₀ * H) * ‖v‖ ^ 2 := by
    have hm := χ.mass_le_of_gradient μ hQ hρ hρr hC hκ (G (A v)) (hcoordinates v)
    apply hm.trans_eq
    dsimp only [F₀]
    ring
  have hm := directional_mass_from_cutoff_residual μ hQ U A M a b δ χ hρ hρr
    hC hκ (mul_nonneg hF₀ hH) hvol hnormal (G (a - A b)) hgradient hdirection hraw hupper
  apply hm.trans_eq
  dsimp only [F₀]
  ring

/-- Constant-direction pairings give the displacement estimate needed in
full-mass pinching. Thus the averaged-gradient comparison is a conclusion,
not an extra hypothesis of the mass estimate. -/
theorem directional_mass_from_pairing_bounds
    (U : F →L[ℝ] SobolevSpace μ hQ) (A : E →L[ℝ] F)
    (Hpair : E →L[ℝ] SobolevSpace μ hQ)
    (M : PositiveBilinearMeasure X F) (a : F) (b δ : E)
    {p : X} {r ρ C κ β P H D : ℝ} {L : ℝ≥0}
    (χ : GoodLaplacianCutoff μ hQ p ρ C) (hρ : 0 < ρ) (hρr : ρ < r)
    (hC : 0 ≤ C) (hκ : 0 ≤ κ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hvol : 0 < μ.real (ball p ρ))
    (hfin : μ (ball p ρ) ≠ ∞) (hpos : μ (ball p ρ) ≠ 0)
    (hnormal : sobolevMeanGram μ hQ (U.comp A) (ball p ρ) measurableSet_ball =
      ContinuousLinearMap.id ℝ E)
    (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)
    (hgradient : ∀ᵐ x ∂μ.restrict (closedBall p (2 * ρ)),
      localGamma μ hQ (U (a - A b)) (U (a - A b)) x ≤ β)
    (hcoordinates : ∀ v, ∀ᵐ x ∂μ.restrict (closedBall p (2 * ρ)),
      localGamma μ hQ (U (A v)) (U (A v)) x ≤ H * ‖v‖ ^ 2)
    (hrep : ∀ v, SobolevSpace.toLp μ hQ (Hpair v) =ᵐ[μ.restrict (ball p ρ)]
      localGamma μ hQ (U a) ((U.comp A) v))
    (herror : ∀ v, ‖normalizeLocalL2 μ (ball p ρ) hfin
      (SobolevSpace.restrictLp μ hQ (ball p ρ) (Hpair v) -
        ⟪δ, v⟫_ℝ • restrictedOne μ (ball p ρ) hfin)‖ ≤ D * ‖v‖)
    (hraw : ⟪a, M.massOperator (ball p ρ) a⟫_ℝ ≤ P) :
    let F₀ := ((C / ρ ^ 2) / 2 + κ) * μ.real (closedBall p (2 * ρ))
    ⟪A δ, M.massOperator (ball p ρ) (A δ)⟫_ℝ ≤
      4 * (P + F₀ * β) + 4 * (F₀ * H) * (D ^ 2 + β) := by
  have hmean := meanGradientVector_error_of_pairings μ hQ (U.comp A) Hpair (U a)
    (ball p ρ) measurableSet_ball hfin hpos δ hD hrep herror
  have hmean2 := (sq_le_sq₀ (norm_nonneg _) hD).mpr hmean
  exact directional_mass_from_gradient_bounds μ hQ U A M a b δ χ hρ hρr hC hκ hH
    hvol hnormal G hgradient hcoordinates hmean2 hraw

end RegularPointCoordinates

end

end OAI
