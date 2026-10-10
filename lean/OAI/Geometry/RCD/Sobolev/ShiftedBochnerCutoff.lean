import OAI.Geometry.RCD.Sobolev.BochnerCutoffIdentity
import OAI.Geometry.RCD.Sobolev.PoissonBochnerMass
import OAI.Geometry.RCD.Sobolev.ShiftedBochnerMeasure

namespace OAI

/-! # The shifted Poisson mass estimate from the actual local equations -/

open Set Metric MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [ProperSpace X] in
/-- The weak equation for a full signed Laplacian gives the defect
identity against an actual Sobolev cutoff. -/
theorem IsMeasureLaplacianOn.test_positive_defect
    {S : Set X} [IsFiniteMeasure (μ.restrict S)]
    (Q : SobolevSpace μ hQ) (a : ℝ) (σ : Measure X) [IsFiniteMeasure σ]
    (hQsource : IsMeasureLaplacianOn μ hQ S Q
      (a • (μ.restrict S).toSignedMeasure - σ.toSignedMeasure))
    (χ : X →ᵇ ℝ) (hχs : HasCompactSupport (χ : X → ℝ))
    (hχS : tsupport (χ : X → ℝ) ⊆ S)
    (c : SobolevSpace μ hQ) (hc : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (q : Lp ℝ 2 μ) (hq : IsWeakLaplacian μ hQ c q)
    (hqs : ∀ᵐ x ∂μ, x ∉ S → q x = 0) :
    (∫ x in S, SobolevSpace.toLp μ hQ Q x * q x ∂μ) =
      a * (∫ x in S, χ x ∂μ) - ∫ x, χ x ∂σ := by
  have he := hQsource c χ χ.continuous hχs hχS hc
  rw [VectorMeasure.integral_sub_vectorMeasure
    (PositiveBilinearMeasure.integrable_weight χ _)
    (PositiveBilinearMeasure.integrable_weight χ _),
    VectorMeasure.integral_smul_vectorMeasure,
    VectorMeasure.integral_toSignedMeasure, VectorMeasure.integral_toSignedMeasure] at he
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
  change energyForm μ hQ Q c = -(a * (∫ x in S, χ x ∂μ) - ∫ x, χ x ∂σ) at he
  linarith

omit [ProperSpace X] in
/-- The shifted measure satisfies the exact cutoff identity, including
the trace correction and its full singular mass. -/
theorem LocalHarmonicEnergy.test_shifted_cutoff
    {U : E →L[ℝ] SobolevSpace μ hQ} {M : PositiveBilinearMeasure X E}
    {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0} {v : E}
    [IsFiniteMeasure (μ.restrict (ball p (2 * r)))]
    (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (ell : E →ₗ[ℝ] ℝ) (n b : ℝ)
    (hshift : ShiftedBochnerLowerBound M (μ.restrict (ball p (2 * r))) ell n)
    (χ : X →ᵇ ℝ) (hχs : HasCompactSupport (χ : X → ℝ))
    (hχS : tsupport (χ : X → ℝ) ⊆ ball p (2 * r))
    (c : SobolevSpace μ hQ) (hc : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (q : Lp ℝ 2 μ) (hq : IsWeakLaplacian μ hQ c q)
    (hqs : ∀ᵐ x ∂μ, x ∉ ball p (2 * r) → q x = 0) :
    (∫ x, χ x ∂(shiftedBochnerMeasure M (μ.restrict (ball p (2 * r))) ell n hshift).measure (WithLp.toLp 2 (v, b))) =
      (1 / 2 : ℝ) * (∫ x in ball p (2 * r), localGamma μ hQ (U v) (U v) x * q x ∂μ) +
        κ * (∫ x in ball p (2 * r), χ x * localGamma μ hQ (U v) (U v) x ∂μ) -
        (2 * b * ell v - n * b ^ 2) * ∫ x in ball p (2 * r), χ x ∂μ := by
  have he := G.test_cutoff μ hQ χ hχs hχS c hc q hq hqs
  rw [ShiftedBochnerMeasure.integral, ← M.weightedOperator_energy χ v, he]
  have hqS : (∫ x in ball p (2 * r), localGamma μ hQ (U v) (U v) x * q x ∂μ) =
      ∫ x, localGamma μ hQ (U v) (U v) x * q x ∂μ := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hqs] with x hx hnot
    rw [hx hnot, mul_zero]
  have hχlocal : (∫ x in ball p (2 * r), χ x * localGamma μ hQ (U v) (U v) x ∂μ) =
      ∫ x, χ x * localGamma μ hQ (U v) (U v) x ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : χ x = 0 := by
      by_contra hn
      exact hx (hχS (subset_closure hn))
    rw [hz, zero_mul]
  rw [hqS, hχlocal]

omit [ProperSpace X] in
/-- Both raw source identities in the shifted Bochner estimate follow
from the local PDEs and the cutoff Laplacian. -/
theorem shifted_poisson_bochner_mass_le
    {U : E →L[ℝ] SobolevSpace μ hQ} {M : PositiveBilinearMeasure X E}
    {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0} {v : E}
    [IsFiniteMeasure (μ.restrict (ball p (2 * r)))]
    (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (ell : E →ₗ[ℝ] ℝ) (n : ℝ)
    (hshift : ShiftedBochnerLowerBound M (μ.restrict (ball p (2 * r))) ell n)
    (Q : SobolevSpace μ hQ) (σ : Measure X) [IsFiniteMeasure σ]
    (hQsource : IsMeasureLaplacianOn μ hQ (ball p (2 * r)) Q
      (ell v • (μ.restrict (ball p (2 * r))).toSignedMeasure - σ.toSignedMeasure))
    (χ : X →ᵇ ℝ) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχs : HasCompactSupport (χ : X → ℝ))
    (hχS : tsupport (χ : X → ℝ) ⊆ ball p (2 * r))
    (c : SobolevSpace μ hQ) (hc : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (q : Lp ℝ 2 μ) (hq : IsWeakLaplacian μ hQ c q)
    (hqs : ∀ᵐ x ∂μ, x ∉ ball p (2 * r) → q x = 0)
    (s : Set X) (hs : MeasurableSet s) (hχone : ∀ x ∈ s, χ x = 1)
    {D error : ℝ} (hD : 0 ≤ D) (hκ : 0 ≤ κ) (hna : n ≤ ell v)
    (hdχbound : ∀ᵐ x ∂μ.restrict (ball p (2 * r)), |q x| ≤ D)
    (herror : (∫ x in ball p (2 * r),
      |(1 / 2 : ℝ) * localGamma μ hQ (U v) (U v) x - SobolevSpace.toLp μ hQ Q x| ∂μ) ≤ error) :
    ((shiftedBochnerMeasure M (μ.restrict (ball p (2 * r))) ell n hshift).measure (WithLp.toLp 2 (v, (1 : ℝ)))).real s ≤
      D * error + κ * ∫ x in ball p (2 * r), localGamma μ hQ (U v) (U v) x ∂μ := by
  apply poisson_bochner_mass_le μ hQ (U v) _ σ χ hχ s (ball p (2 * r)) hs hχone
    (SobolevSpace.toLp μ hQ Q) q
    (MemLp.integrable (by norm_num) ((Lp.memLp _).restrict _))
    (Lp.aestronglyMeasurable q |>.restrict) hD hκ hna hdχbound herror
  · simpa only [one_pow, mul_one, one_mul] using
      G.test_shifted_cutoff μ hQ ell n 1 hshift χ hχs hχS c hc q hq hqs
  · exact hQsource.test_positive_defect μ hQ Q (ell v) σ χ hχs hχS c hc q hq hqs

end RegularPointCoordinates

end

end OAI
