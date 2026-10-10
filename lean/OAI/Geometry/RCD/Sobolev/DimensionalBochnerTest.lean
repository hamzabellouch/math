import OAI.Geometry.RCD.Metric.LocalSignedMeasureOrder
import OAI.Geometry.RCD.Sobolev.FiniteDimensionalBochnerAE
import OAI.Geometry.RCD.Sobolev.BochnerMeasureIdentity
import OAI.Geometry.RCD.Coordinates.LaplacianCoordinateForm

namespace OAI

/-! # Recovering the dimensional density from the weak Bochner test inequality

The only analytic input here is the scalar finite-dimensional Bochner test
inequality, as in Han, JGA 28 (2018), Theorem 3.3. The proof identifies its
absolutely continuous density while retaining the full positive measure.
-/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

omit [SigmaFinite μ] in
/-- A nonnegative finite signed measure has nonnegative density. -/
theorem signed_rnDeriv_nonneg_of_nonneg (ν : SignedMeasure X) (hν : 0≤ν) :
    ∀ᵐ x ∂μ, 0≤ν.rnDeriv μ x := by
  have hp : 0≤[univ] ν := by simpa only [VectorMeasure.le_restrict_univ_iff_le] using hν
  let σ := ν.toMeasureOfZeroLE univ MeasurableSet.univ hp
  have hs : σ.toSignedMeasure=ν := ν.toMeasureOfZeroLE_toSignedMeasure hp
  have h := signed_rnDeriv_toSignedMeasure μ σ
  rw [hs] at h
  filter_upwards [h] with x hx
  rw [hx]
  exact ENNReal.toReal_nonneg

variable [MetricSpace X] [BorelSpace X] [ProperSpace X] [SecondCountableTopology X]

omit [SigmaFinite μ] [ProperSpace X] [SecondCountableTopology X] in
/-- The test integral of the dimensional defect has its exact scalar form. -/
theorem integral_dimensional_defect (σ : Measure X) [IsFiniteMeasure σ]
    (d : Lp ℝ 2 μ) (N : ℝ) (q : X →ᵇ ℝ) :
    (∫ᵛ x, q x ∂<•(N • σ.toSignedMeasure-μ.withDensityᵥ (fun x => (d x)^2))) =
      N*(∫ x, q x ∂σ)-(∫ x, q x*(d x)^2 ∂μ) := by
  have hd : Integrable (fun x => (d x)^2) μ := (Lp.memLp d).integrable_sq
  rw [VectorMeasure.integral_sub_vectorMeasure
    (PositiveBilinearMeasure.integrable_weight q _)
    (PositiveBilinearMeasure.integrable_weight q _),
    VectorMeasure.integral_smul_vectorMeasure,VectorMeasure.integral_toSignedMeasure,
    integral_signedDensity μ hd]
  rfl

/-- Weak tests give the scalar dimensional density inequality on a compact
interior set. No absolute continuity of the full Bochner measure is used. -/
theorem dimensional_bochner_density_of_tests (σ : Measure X) [IsFiniteMeasure σ]
    (d : Lp ℝ 2 μ) (N : ℝ) {Ω S : Set X} (hS : MeasurableSet S)
    (χ : X →ᵇ ℝ) {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : 0≤χ) (hχ1 : ∀ x∈S, χ x=1)
    (htest : ∀ q : compactLipschitzTests Ω, 0≤(q : X →ᵇ ℝ) →
      (∫ x, (q : X →ᵇ ℝ) x*(d x)^2 ∂μ)≤N*(∫ x, (q : X →ᵇ ℝ) x ∂σ)) :
    ∀ᵐ x ∂μ.restrict S, (d x)^2≤N*(σ.rnDeriv μ x).toReal := by
  have hd : Integrable (fun x => (d x)^2) μ := (Lp.memLp d).integrable_sq
  let ν : SignedMeasure X := N • σ.toSignedMeasure-μ.withDensityᵥ (fun x => (d x)^2)
  have hp : 0≤ν.restrict S := by
    apply signedMeasure_nonneg_restrict_of_tests ν hS χ hχ hχc hχΩ hχ0 hχ1
    intro q hq
    change 0≤∫ᵛ x, (q : X →ᵇ ℝ) x ∂<•(N • σ.toSignedMeasure-μ.withDensityᵥ (fun x => (d x)^2))
    rw [integral_dimensional_defect μ σ d N (q : X →ᵇ ℝ)]
    exact sub_nonneg.mpr (htest q hq)
  have hpos := signed_rnDeriv_nonneg_of_nonneg μ (ν.restrict S) hp
  have hres := signed_rnDeriv_restrict μ ν hS
  have hsub := SignedMeasure.rnDeriv_sub (N • σ.toSignedMeasure)
    (μ.withDensityᵥ (fun x => (d x)^2)) μ
  have hmul := SignedMeasure.rnDeriv_smul σ.toSignedMeasure μ N
  filter_upwards [ae_restrict_of_ae hpos,ae_restrict_of_ae hres,ae_restrict_mem hS,
    ae_restrict_of_ae hsub,ae_restrict_of_ae hmul,
    ae_restrict_of_ae (signed_rnDeriv_toSignedMeasure μ σ),
    ae_restrict_of_ae (signed_rnDeriv_density μ hd)] with x hp hr hx hs hm hσ hd
  rw [hr,indicator_of_mem hx] at hp
  change 0≤SignedMeasure.rnDeriv (N • σ.toSignedMeasure-μ.withDensityᵥ (fun x => (d x)^2)) μ x at hp
  rw [hs] at hp
  simp only [Pi.sub_apply] at hp
  rw [hm] at hp
  simp only [Pi.smul_apply,smul_eq_mul] at hp
  rw [hσ,hd] at hp
  exact sub_nonneg.mp hp

/-- The actual linear Laplacian map and common full bilinear measure
therefore satisfy the pointwise finite-dimensional input used by the
quadratic-perturbation theorem. -/
theorem dimensional_bilinear_density_of_tests {m : ℕ}
    (M : PositiveBilinearMeasure X (Euclidean m)) (D : Euclidean m →L[ℝ] Lp ℝ 2 μ)
    (N : ℝ) {Ω S : Set X} (hS : MeasurableSet S)
    (χ : X →ᵇ ℝ) {L : ℝ≥0} (hχ : LipschitzWith L χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : 0≤χ) (hχ1 : ∀ x∈S, χ x=1)
    (htest : ∀ a (q : compactLipschitzTests Ω), 0≤(q : X →ᵇ ℝ) →
      (∫ x, (q : X →ᵇ ℝ) x*(D a x)^2 ∂μ)≤N*(∫ x, (q : X →ᵇ ℝ) x ∂M.measure a)) :
    ∀ a, ∀ᵐ x ∂μ.restrict S,
      (laplacianCoordinateForm μ D x a)^2≤N*bochnerRadonDensity μ M x a a := by
  intro a
  have hb := dimensional_bochner_density_of_tests μ (M.measure a) (D a) N
    hS χ hχ hχc hχΩ hχ0 hχ1 (htest a)
  filter_upwards [hb,ae_restrict_of_ae (laplacianCoordinateForm_rep μ D a),
    ae_restrict_of_ae (bochnerRadonDensity_diagonal μ M a)] with x hx hd hm
  rwa [hd,← hm] at hx

end RegularPointCoordinates

end

end OAI
