import OAI.Geometry.RCD.Sobolev.MeasureProductEnergy
import OAI.Geometry.RCD.Metric.SignedSourceWeight

namespace OAI

/-!
# Cutting off a local measure Laplacian

The source is the full weighted signed measure plus the two ordinary
product-rule terms. This is an algebraic consequence of the actual Sobolev
product rule, rather than an additional analytic assumption.
-/

open Set MeasureTheory
open scoped NNReal BoundedContinuousFunction CompactlySupported InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Local distributional measure Laplacian, using continuous compactly
supported Sobolev tests inside the indicated region. -/
def IsMeasureLaplacianOn (Ω : Set X) (g : SobolevSpace μ hQ)
    (ν : SignedMeasure X) : Prop :=
  ∀ (φ : SobolevSpace μ hQ) (v : X → ℝ), Continuous v → HasCompactSupport v →
    tsupport v ⊆ Ω → SobolevSpace.toLp μ hQ φ =ᵐ[μ] v →
      energyForm μ hQ g φ = -(∫ᵛ x, v x ∂<•ν)

omit [ProperSpace X] in
/-- The absolutely continuous part introduced by the cutoff product. -/
def cutoffSourceDensity (g c : SobolevSpace μ hQ) (q : Lp ℝ 2 μ) : X → ℝ :=
  fun x => SobolevSpace.toLp μ hQ g x * q x + 2 * localGamma μ hQ g c x

omit [ProperSpace X] in
theorem cutoffSourceDensity_integrable (g c : SobolevSpace μ hQ) (q : Lp ℝ 2 μ) :
    Integrable (cutoffSourceDensity μ hQ g c q) μ :=
  ((Lp.memLp (SobolevSpace.toLp μ hQ g)).integrable_mul (Lp.memLp q)).add
    ((localGamma_memL1 μ hQ g c).const_mul 2)

/-- The full signed source of the cutoff function. -/
def cutoffMeasureSource (g c : SobolevSpace μ hQ) (q : Lp ℝ 2 μ)
    (ν : SignedMeasure X) (χ : X →ᵇ ℝ) : SignedMeasure X :=
  signedSourceWeight ν χ + μ.withDensityᵥ (cutoffSourceDensity μ hQ g c q)

/-- The local measure equation and the weak cutoff Laplacian imply the
full global product equation, with no assumption of absolute continuity
for the local source. -/
theorem IsMeasureLaplacianOn.cutoff {Ω : Set X} {g : SobolevSpace μ hQ}
    {ν : SignedMeasure X} (hν : IsMeasureLaplacianOn μ hQ Ω g ν)
    (χ : X →ᵇ ℝ) (hχs : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport (χ : X → ℝ) ⊆ Ω)
    (c : SobolevSpace μ hQ) (hc : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (q : Lp ℝ 2 μ) (hq : IsWeakLaplacian μ hQ c q)
    (D : ℝ≥0) (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x| ≤ D) :
    IsMeasureLaplacian μ hQ
      (SobolevSpace.product μ hQ g c D ‖χ‖₊)
      (cutoffMeasureSource μ hQ g c q ν χ) := by
  have hcb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ c x| ≤ (‖χ‖₊ : ℝ) := by
    filter_upwards [hc] with x hx
    simpa only [hx, Real.norm_eq_abs, coe_nnnorm] using χ.norm_coe_le_norm x
  intro φ v hv hvs hφ
  let w : X →ᵇ ℝ := (⟨⟨v, hv⟩, hvs⟩ : C_c(X, ℝ)).toBoundedContinuousFunction
  have hφb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ φ x| ≤ (‖w‖₊ : ℝ) := by
    filter_upwards [hφ] with x hx
    have hw := w.norm_coe_le_norm x
    change ‖v x‖ ≤ ‖w‖ at hw
    simpa only [hx, Real.norm_eq_abs, coe_nnnorm] using hw
  have he := energy_product_integration_by_parts μ hQ g c φ D ‖χ‖₊ ‖w‖₊ hg hcb hφb
  have hlocal := hν (SobolevSpace.product μ hQ c φ ‖χ‖₊ ‖w‖₊)
    (fun x => χ x * v x) (χ.continuous.mul hv) hχs.mul_right
    (tsupport_mul_subset_left.trans hχΩ) (by
      filter_upwards [SobolevSpace.product_coe μ hQ c φ ‖χ‖₊ ‖w‖₊ hcb hφb,
        hc, hφ] with x hx hcx hφx
      simpa only [hcx, hφx] using hx)
  have hweak := hq (SobolevSpace.product μ hQ g φ D ‖w‖₊)
  have hi : ⟪q, SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ g φ D ‖w‖₊)⟫_ℝ =
      ∫ x, v x * (SobolevSpace.toLp μ hQ g x * q x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [SobolevSpace.product_coe μ hQ g φ D ‖w‖₊ hg hφb, hφ] with x hx hvx
    simp only [RCLike.inner_apply, conj_trivial, hx, hvx]
    ring
  have hig : Integrable (fun x => v x * localGamma μ hQ g c x) μ :=
    (localGamma_memL1 μ hQ g c).bdd_mul hv.aestronglyMeasurable
      (Filter.Eventually.of_forall w.norm_coe_le_norm)
  have hip : Integrable (fun x => v x * (SobolevSpace.toLp μ hQ g x * q x)) μ :=
    ((Lp.memLp (SobolevSpace.toLp μ hQ g)).integrable_mul (Lp.memLp q)).bdd_mul
      hv.aestronglyMeasurable (Filter.Eventually.of_forall w.norm_coe_le_norm)
  have hsource : (∫ᵛ x, v x ∂<•(cutoffMeasureSource μ hQ g c q ν χ)) =
      (∫ᵛ x, χ x * v x ∂<•ν) +
      (∫ x, v x * (SobolevSpace.toLp μ hQ g x * q x) ∂μ) +
      2 * ∫ x, v x * localGamma μ hQ g c x ∂μ := by
    change (∫ᵛ x, w x ∂<•(cutoffMeasureSource μ hQ g c q ν χ)) = _
    rw [cutoffMeasureSource, VectorMeasure.integral_add_vectorMeasure
      (PositiveBilinearMeasure.integrable_weight w _)
      (PositiveBilinearMeasure.integrable_weight w _),
      integral_signedSourceWeight, integral_signedDensity _ (cutoffSourceDensity_integrable μ hQ g c q)]
    have hwν : (∫ᵛ x, (w * χ) x ∂<•ν) = ∫ᵛ x, χ x * v x ∂<•ν := by
      congr 1
      funext x
      change v x * χ x = χ x * v x
      exact mul_comm _ _
    rw [hwν]
    have hd : (∫ x, w x * cutoffSourceDensity μ hQ g c q x ∂μ) =
        (∫ x, v x * (SobolevSpace.toLp μ hQ g x * q x) ∂μ) +
        2 * ∫ x, v x * localGamma μ hQ g c x ∂μ := by
      calc
        _ = ∫ x, v x * (SobolevSpace.toLp μ hQ g x * q x) +
            2 * (v x * localGamma μ hQ g c x) ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            change v x * (_ + 2 * _) = _
            ring
        _ = _ := by rw [integral_add hip (hig.const_mul 2), integral_const_mul]
    rw [hd]
    ring
  rw [hlocal, hweak, hi] at he
  rw [hsource]
  have hcross : (∫ x, SobolevSpace.toLp μ hQ φ x * localGamma μ hQ g c x ∂μ) =
      ∫ x, v x * localGamma μ hQ g c x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hφ] with x hx
    rw [hx]
  rw [hcross] at he
  linarith

end RegularPointCoordinates

end

end OAI
