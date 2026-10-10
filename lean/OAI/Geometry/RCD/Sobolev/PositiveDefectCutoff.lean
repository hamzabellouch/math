import OAI.Geometry.RCD.Sobolev.ShiftedBochnerCutoff
import OAI.Geometry.RCD.Sobolev.DistanceLaplacianInput

namespace OAI

/-! # Testing the positive distance defect with actual Laplacian cutoffs -/

open Set Metric MeasureTheory
open scoped NNReal BoundedContinuousFunction InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] in
/-- The compact Lipschitz source identity is sufficient for the cutoff
calculation; no extension to arbitrary continuous tests is assumed. -/
theorem positive_defect_cutoff_identity {S : Set X} (Q : SobolevSpace μ hQ)
    (σ : Measure X) (a : ℝ)
    (hsource : ∀ (ψ : SobolevSpace μ hQ) (v : X → ℝ) (L : ℝ≥0),
      LipschitzWith L v → HasCompactSupport v → tsupport v ⊆ S →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] v →
      energyForm μ hQ Q ψ + a * (∫ x in S, v x ∂μ) = ∫ x, v x ∂σ)
    (χ : X →ᵇ ℝ) {L : ℝ≥0} (hχlip : LipschitzWith L (χ : X → ℝ))
    (hχs : HasCompactSupport (χ : X → ℝ)) (hχS : tsupport (χ : X → ℝ) ⊆ S)
    (c : SobolevSpace μ hQ) (hc : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (q : Lp ℝ 2 μ) (hq : IsWeakLaplacian μ hQ c q)
    (hqs : ∀ᵐ x ∂μ, x ∉ S → q x = 0) :
    (∫ x in S, SobolevSpace.toLp μ hQ Q x * q x ∂μ) =
      a * (∫ x in S, χ x ∂μ) - ∫ x, χ x ∂σ := by
  have he := hsource c χ L hχlip hχs hχS hc
  have hw := hq Q
  rw [energyForm_comm μ hQ c Q, L2.inner_def] at hw
  have hi : (∫ x, ⟪q x, SobolevSpace.toLp μ hQ Q x⟫_ℝ ∂μ) =
      ∫ x in S, SobolevSpace.toLp μ hQ Q x * q x ∂μ := by
    calc
      _ = ∫ x, SobolevSpace.toLp μ hQ Q x * q x ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          simp only [RCLike.inner_apply, conj_trivial]
      _ = _ := by
        symm
        apply setIntegral_eq_integral_of_ae_compl_eq_zero
        filter_upwards [hqs] with x hx hnot
        rw [hx hnot, mul_zero]
  rw [hi] at hw
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The full shifted Bochner mass bound uses only the actual compact
Lipschitz source identity proved for the squared-distance datum. -/
theorem shifted_poisson_mass_of_positive_defect
    {U : E →L[ℝ] SobolevSpace μ hQ} {M : PositiveBilinearMeasure X E}
    {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0} {v : E}
    [IsFiniteMeasure (μ.restrict (ball p (2 * r)))]
    (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (ell : E →ₗ[ℝ] ℝ) (n : ℝ)
    (hshift : ShiftedBochnerLowerBound M (μ.restrict (ball p (2 * r))) ell n)
    (Q : SobolevSpace μ hQ) (σ : Measure X) [IsFiniteMeasure σ]
    (hsource : ∀ (ψ : SobolevSpace μ hQ) (w : X → ℝ) (C : ℝ≥0),
      LipschitzWith C w → HasCompactSupport w → tsupport w ⊆ ball p (2 * r) →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] w →
      energyForm μ hQ Q ψ + ell v * (∫ x in ball p (2 * r), w x ∂μ) = ∫ x, w x ∂σ)
    (χ : X →ᵇ ℝ) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    {Cχ : ℝ≥0} (hχlip : LipschitzWith Cχ (χ : X → ℝ))
    (hχs : HasCompactSupport (χ : X → ℝ)) (hχS : tsupport (χ : X → ℝ) ⊆ ball p (2 * r))
    (c : SobolevSpace μ hQ) (hc : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (q : Lp ℝ 2 μ) (hq : IsWeakLaplacian μ hQ c q)
    (hqs : ∀ᵐ x ∂μ, x ∉ ball p (2 * r) → q x = 0)
    (s : Set X) (hs : MeasurableSet s) (hχone : ∀ x ∈ s, χ x = 1)
    {D error : ℝ} (hD : 0 ≤ D) (hκ : 0 ≤ κ) (hna : n ≤ ell v)
    (hdχbound : ∀ᵐ x ∂μ.restrict (ball p (2 * r)), |q x| ≤ D)
    (herror : (∫ x in ball p (2 * r),
      |(1 / 2 : ℝ) * localGamma μ hQ (U v) (U v) x - SobolevSpace.toLp μ hQ Q x| ∂μ) ≤ error) :
    ((shiftedBochnerMeasure M (μ.restrict (ball p (2 * r))) ell n hshift).measure
      (WithLp.toLp 2 (v, (1 : ℝ)))).real s ≤
        D * error + κ * ∫ x in ball p (2 * r), localGamma μ hQ (U v) (U v) x ∂μ := by
  apply poisson_bochner_mass_le μ hQ (U v) _ σ χ hχ s (ball p (2 * r)) hs hχone
    (SobolevSpace.toLp μ hQ Q) q
    (MemLp.integrable (by norm_num) ((Lp.memLp _).restrict _))
    (Lp.aestronglyMeasurable q |>.restrict) hD hκ hna hdχbound herror
  · simpa only [one_pow, mul_one, one_mul] using
      G.test_shifted_cutoff μ hQ ell n 1 hshift χ hχs hχS c hc q hq hqs
  · exact positive_defect_cutoff_identity μ hQ Q σ (ell v) hsource χ
      hχlip hχs hχS c hc q hq hqs

end RegularPointCoordinates

end

end OAI
