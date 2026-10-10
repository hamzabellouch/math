import OAI.Geometry.RCD.Sobolev.BochnerCutoffIdentity

namespace OAI

/-! # Full Bochner mass controlled by local harmonic energy -/

open Set Metric MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- A cutoff bounds the full positive mass, including its singular part,
by the local energy. This version does not subtract a constant Gram field. -/
theorem bochner_mass_le_of_energy
    (U : E →L[ℝ] SobolevSpace μ hQ) (M : PositiveBilinearMeasure X E)
    (χ : X →ᵇ ℝ) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (S s : Set X) (hs : MeasurableSet s) (hχone : ∀ x ∈ s, χ x = 1)
    (q : X → ℝ) {D κ A : ℝ} (hD : 0 ≤ D) (hκ : 0 ≤ κ)
    (hqmeas : AEStronglyMeasurable q (μ.restrict S))
    (hq : ∀ᵐ x ∂μ.restrict S, |q x| ≤ D) (v : E)
    (henergy : (∫ x in S, localGamma μ hQ (U v) (U v) x ∂μ) ≤ A)
    (hsource : ⟪v, M.weightedOperator χ v⟫_ℝ =
      (1 / 2 : ℝ) * (∫ x in S, localGamma μ hQ (U v) (U v) x * q x ∂μ) +
        κ * ∫ x in S, χ x * localGamma μ hQ (U v) (U v) x ∂μ) :
    ⟪v, M.massOperator s v⟫_ℝ ≤ (D / 2 + κ) * A := by
  let f := localGamma μ hQ (U v) (U v)
  have hf : IntegrableOn f S μ := (localGamma_memL1 μ hQ (U v) (U v)).integrableOn
  have hfpos : ∀ᵐ x ∂μ.restrict S, 0 ≤ f x := by
    filter_upwards [ae_restrict_of_ae (localGamma_self μ hQ (U v))] with x hx
    simpa only [f, hx] using sq_nonneg (SobolevSpace.minimalSlope μ hQ (U v) x)
  have hqn : ∀ᵐ x ∂μ.restrict S, ‖q x‖ ≤ D := by
    simpa only [Real.norm_eq_abs] using hq
  have hfq : IntegrableOn (fun x => f x * q x) S μ :=
    (hf.bdd_mul hqmeas hqn).congr (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hqbound : (∫ x in S, f x * q x ∂μ) ≤ D * ∫ x in S, f x ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae hfq (hf.const_mul D)
    filter_upwards [hfpos, hq] with x hx hqx
    exact (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hqx) hx).trans_eq (mul_comm _ _)
  have hχbound : (∫ x in S, χ x * f x ∂μ) ≤ ∫ x in S, f x ∂μ := by
    apply integral_mono_ae
      (hf.bdd_mul χ.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall χ.norm_coe_le_norm)) hf
    filter_upwards [hfpos] with x hx
    exact mul_le_of_le_one_left hx (hχ x).2
  have hmass := M.massOperator_le_weightedOperator χ (fun x => (hχ x).1)
    s hs 1 (fun x hx => (hχone x hx).ge) v
  simp only [one_mul] at hmass
  rw [hsource] at hmass
  have hcurv := mul_le_mul_of_nonneg_left hχbound hκ
  change (∫ x in S, f x ∂μ) ≤ A at henergy
  calc
    ⟪v, M.massOperator s v⟫_ℝ ≤
        (1 / 2 : ℝ) * (∫ x in S, f x * q x ∂μ) +
          κ * ∫ x in S, χ x * f x ∂μ := hmass
    _ ≤ (1 / 2 : ℝ) * (D * ∫ x in S, f x ∂μ) +
        κ * ∫ x in S, f x ∂μ :=
      add_le_add (mul_le_mul_of_nonneg_left hqbound (by norm_num)) hcurv
    _ = (D / 2 + κ) * ∫ x in S, f x ∂μ := by ring
    _ ≤ (D / 2 + κ) * A :=
      mul_le_mul_of_nonneg_left henergy (by positivity)

/-- The exact local harmonic Bochner equation supplies the source identity
in the energy estimate; no mass bound is included as an input. -/
theorem LocalHarmonicEnergy.mass_le_of_energy
    {U : E →L[ℝ] SobolevSpace μ hQ} {M : PositiveBilinearMeasure X E}
    {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0} {v : E}
    (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (χ : X →ᵇ ℝ) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχs : HasCompactSupport (χ : X → ℝ))
    (hχΩ : tsupport (χ : X → ℝ) ⊆ ball p (2 * r))
    (c : SobolevSpace μ hQ) (hc : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (q : Lp ℝ 2 μ) (hq : IsWeakLaplacian μ hQ c q)
    (hqs : ∀ᵐ x ∂μ, x ∉ ball p (2 * r) → q x = 0)
    (S s : Set X) (hs : MeasurableSet s) (hχone : ∀ x ∈ s, χ x = 1)
    (hχS : ∀ x ∉ S, χ x = 0) (hqS : ∀ᵐ x ∂μ, x ∉ S → q x = 0)
    {D A : ℝ} (hD : 0 ≤ D) (hκ : 0 ≤ κ) (hqb : ∀ᵐ x ∂μ, |q x| ≤ D)
    (henergy : (∫ x in S, localGamma μ hQ (U v) (U v) x ∂μ) ≤ A) :
    ⟪v, M.massOperator s v⟫_ℝ ≤ (D / 2 + κ) * A := by
  apply bochner_mass_le_of_energy μ hQ U M χ hχ S s hs hχone q hD hκ
    (Lp.aestronglyMeasurable q).restrict (ae_restrict_of_ae hqb) v henergy
  have hi := G.test_cutoff μ hQ χ hχs hχΩ c hc q hq hqs
  have heq : (∫ x in S, localGamma μ hQ (U v) (U v) x * q x ∂μ) =
      ∫ x, localGamma μ hQ (U v) (U v) x * q x ∂μ := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hqS] with x hx hnot
    rw [hx hnot, mul_zero]
  have hχeq : (∫ x in S, χ x * localGamma μ hQ (U v) (U v) x ∂μ) =
      ∫ x, χ x * localGamma μ hQ (U v) (U v) x ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [hχS x hx, zero_mul]
  rw [heq, hχeq]
  exact hi

end RegularPointCoordinates

end

end OAI
