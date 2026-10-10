import OAI.Geometry.RCD.Sobolev.NoEulerCountersequence
import OAI.Geometry.RCD.Harmonic.ReplaceHarmonicSequence
import OAI.Geometry.RCD.Coordinates.FixedResidualNormalization

namespace OAI

/-! # Excluding the actual normalized orthogonal projection sequence -/

open Set Metric MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The unnormalized projection residual cannot dominate its source error
along a geometric compactness sequence. All equations here are actual
Sobolev equations, and orthogonality follows from the actual projection.
The fixed outer constant changes the limit norm to `M⁻²`, which stays nonzero. -/
theorem no_projected_euler_sequence {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    (hcompact : LocalPoissonHarmonicCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX) (hn : 2 ≤ n)
    {S ρ M C : ℝ} (hS : 0 < S) (hρ : 0 < ρ) (hρS : ρ < S) (hM : 0 < M)
    (q : RadialCompactnessSequence hX S)
    (v w e : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (b : ℕ → Euclidean n) (k B : ℕ → ℝ)
    (hf : ∀ i, ∀ᵐ x ∂(hausdorff n X).restrict (ball (q.center i) (S * q.radius i)),
      localGamma (hausdorff n X) hX.quadratic (q.radialFunction i) (q.radialFunction i) x ≤ B i)
    (hw : ∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
      (ball (q.center i) (S * q.radius i)) (w i))
    (hproj : ∀ i, SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
      (ball (q.center i) (ρ * q.radius i)) (w i) =
      affineResidual (hausdorff n X) hX.quadratic (q.coordinates i)
        (ball (q.center i) (ρ * q.radius i)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
          (ball (q.center i) (ρ * q.radius i)) (v i)))
    (hid : ∀ i, q.radius i ^ 2 • localRadialDerivative (hausdorff n X) hX.quadratic
      (ball (q.center i) (S * q.radius i)) (q.radialFunction i) (hf i) (w i) =
      SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball (q.center i) (S * q.radius i)) (w i) +
      (∑ j, b i j • SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball (q.center i) (S * q.radius i)) (q.coordinates i j)) +
      k i • restrictedOne (hausdorff n X) (ball (q.center i) (S * q.radius i))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) +
      SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball (q.center i) (S * q.radius i)) (e i)) :
    let α := fun i => ‖normalizeLocalL2 (hausdorff n X) (ball (q.center i) (ρ * q.radius i))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball (q.center i) (ρ * q.radius i)) (w i))‖
    (∀ i, 0 < α i) →
    (∀ i, ‖normalizeLocalL2 (hausdorff n X) (ball (q.center i) (S * q.radius i))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball (q.center i) (S * q.radius i)) (w i))‖ ≤ M * α i) →
    (∀ i, ‖b i‖ + |k i| ≤ C * α i) →
    Tendsto (fun i => ‖normalizeLocalL2 (hausdorff n X) (ball (q.center i) (S * q.radius i))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball (q.center i) (S * q.radius i)) ((α i)⁻¹ • e i))‖) atTop (𝓝 0) → False := by
  dsimp only
  intro hα houter hcoeff he
  let μ := hausdorff n X
  let α := fun i => ‖normalizeLocalL2 μ (ball (q.center i) (ρ * q.radius i))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (SobolevSpace.restrictLp μ hX.quadratic (ball (q.center i) (ρ * q.radius i)) (w i))‖
  let a := fun i => (M * α i)⁻¹
  let W := fun i => a i • w i
  have hW : ∀ i, IsSobolevHarmonicOn μ hX.quadratic
      (ball (q.center i) (S * q.radius i)) (W i) :=
    fun i => (hw i).smul μ hX.quadratic (a i)
  have hWnorm (i : ℕ) : ‖normalizeLocalL2 μ (ball (q.center i) (S * q.radius i))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp μ hX.quadratic (ball (q.center i) (S * q.radius i)) (W i))‖ ≤ 1 := by
    dsimp only [W]
    rw [map_smul, normalizeLocalL2_smul]
    exact fixed_amplitude_bound _ hM (hα i) (houter i)
  let q' := q.with_harmonic hgradient hn hS W hW hWnorm
  have heq (i : ℕ) : normalizeLocalL2 μ (ball (q.center i) (S * q.radius i))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp μ hX.quadratic (ball (q.center i) (S * q.radius i)) (a i • e i)) =
      M⁻¹ • normalizeLocalL2 μ (ball (q.center i) (S * q.radius i))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hX.quadratic (ball (q.center i) (S * q.radius i)) ((α i)⁻¹ • e i)) := by
    simp only [map_smul, normalizeLocalL2_smul, smul_smul]
    congr 1
    dsimp only [a]
    rw [mul_inv_rev, mul_comm]
  have he' : Tendsto (fun i => ‖normalizeLocalL2 μ (ball (q.center i) (S * q.radius i))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp μ hX.quadratic (ball (q.center i) (S * q.radius i)) (a i • e i))‖)
      atTop (𝓝 0) := by
    simpa only [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM), mul_zero]
      using (tendsto_const_nhds (x := M⁻¹)).mul he
  apply no_euler_countersequence hcompact hn hS q' B hf
    (fun i => a i • e i) (fun i => a i • b i) (fun i => a i * k i)
    (ρ := ρ) (c := (M⁻¹) ^ 2) (C := C / M) (fun i => fixed_coefficient_bound (b i) (k i) hM (hα i) (hcoeff i)) he'
  case hid =>
    intro i
    exact amplitude_euler_identity μ hX.quadratic _ _ (q.radialFunction i) (w i) (e i)
      (q.coordinates i) (fun j => b i j) (k i) (a i) (q.radius i ^ 2) (hf i) (hid i)
  case hρ => exact hρ
  case hρS => exact hρS
  case hc => exact pow_ne_zero 2 (inv_ne_zero hM.ne')
  case hnorm =>
    have hmoment (i : ℕ) :
        ⟪localAffineMomentFamily μ hX.quadratic (q.coordinates i) (W i)
            (ball (q.center i) (ρ * q.radius i)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) none,
          localAffineMomentFamily μ hX.quadratic (q.coordinates i) (W i)
            (ball (q.center i) (ρ * q.radius i)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) none⟫_ℝ =
          (M⁻¹) ^ 2 :=
      fixed_residual_moment μ hX.quadratic _ _ (q.coordinates i) (w i) hM (hα i)
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (M⁻¹) ^ 2) atTop (𝓝 ((M⁻¹) ^ 2))).congr'
      (Filter.Eventually.of_forall fun i => (hmoment i).symm)
  case horth =>
    intro i j
    exact normalized_projection_orthogonality μ hX.quadratic _ _ (q.coordinates i)
      (v i) (w i) (hproj i) (a i) j

end RegularPointCoordinates

end

end OAI
