import OAI.Geometry.RCD.Coordinates.NormalizedCutoffDifference
import OAI.Geometry.RCD.Sobolev.PoissonCutoffErrors
import OAI.Geometry.RCD.Sobolev.EnergyGapLimit

namespace OAI

/-! # Local strong gradient comparison from the actual Poisson equation

Sharp recovery energies and the lower bound for the original function,
together with vanishing value error, force the cutoff gradient error to
vanish. The constant source and cutoff commutator are both retained.
-/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

def normalizedCutoffEnergy (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (Ω : Set X) (r : ℝ) (v : X → ℝ) (f : SobolevSpace μ hQ) : ℝ :=
  r^2*(μ.real Ω)⁻¹*∫ x in Ω, (v x)^2*localGamma μ hQ f f x ∂μ

theorem poisson_strong_cutoff_comparison (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (Ω : ℕ → Set X) [∀ k, IsFiniteMeasure (μ.restrict (Ω k))]
    (hmass : ∀ k, 0<μ.real (Ω k)) (r : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (w q η : ℕ → SobolevSpace μ hQ) (v : ℕ → X → ℝ)
    (P J : ℕ → ℝ≥0) (hv : ∀ k, LipschitzWith (P k) (v k))
    (hs : ∀ k, HasCompactSupport (v k))
    (hb : ∀ k x, |v k x|≤1) (hn : ∀ k x, 0≤v k x)
    (hrep : ∀ k, SobolevSpace.toLp μ hQ (η k)=ᵐ[μ] v k)
    (hgrad : ∀ k, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (η k) x≤J k)
    (hsupp : ∀ k, tsupport (v k)⊆Ω k) (a : ℕ → ℝ)
    (hw : ∀ k, IsConstantLaplacianOn μ hQ (Ω k) (w k) (a k/r k^2))
    {A M L E : ℝ} (hA : 0≤A) (hM : 0≤M) (hL : 0≤L)
    (ha : ∀ᶠ k in atTop, |a k|≤A)
    (hwgrad : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k),
      r k^2*localGamma μ hQ (w k) (w k) x≤M^2)
    (hηgrad : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k),
      r k^2*localGamma μ hQ (η k) (η k) x≤L^2)
    (hvalue : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k),
      |SobolevSpace.toLp μ hQ (w k-q k) x|≤δ)
    (hq : Tendsto (fun k => normalizedCutoffEnergy μ hQ (Ω k) (r k) (v k) (q k))
      atTop (𝓝 E))
    (hlower : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      E-δ≤normalizedCutoffEnergy μ hQ (Ω k) (r k) (v k) (w k)) :
    Tendsto (fun k => normalizedCutoffEnergy μ hQ (Ω k) (r k) (v k) (w k-q k))
      atTop (𝓝 0) := by
  let z : ℕ → X → ℝ := fun k x => SobolevSpace.toLp μ hQ (w k-q k) x
  let S := fun k => a k*(μ.real (Ω k))⁻¹*∫ x in Ω k, (v k x)^2*z k x ∂μ
  let T := fun k => r k^2*(μ.real (Ω k))⁻¹*
    ∫ x in Ω k, v k x*z k x*localGamma μ hQ (w k) (η k) x ∂μ
  have hvb : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k), |v k x|≤(1:ℝ) :=
    Eventually.of_forall fun k => Eventually.of_forall (hb k)
  have hmass' (k : ℕ) : 0<(μ.restrict (Ω k)).real univ := by
    simpa only [Measure.real,Measure.restrict_apply_univ] using hmass k
  have hS : Tendsto S atTop (𝓝 0) := by
    simpa only [S,Measure.real,Measure.restrict_apply_univ] using
      normalized_source_error_tendsto (fun k => μ.restrict (Ω k)) hmass' z v a hA ha hvb hvalue
  have hT : Tendsto T atTop (𝓝 0) :=
    scaled_weighted_gamma_error_tendsto μ hQ Ω hmass r (fun k => (hr k).le)
      w η z v hM hL zero_le_one hwgrad hηgrad hvb hvalue
  apply poisson_energy_gap_tendsto_zero (S := S) (T := T) _ _ hq hlower hS hT
  · intro k
    apply mul_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (hmass k).le))
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_of_ae (localGamma_self μ hQ (w k-q k))] with x hx
    exact mul_nonneg (sq_nonneg _) (hx ▸ sq_nonneg _)
  · intro k
    exact normalized_cutoff_difference_energy μ hQ (w k) (q k) (η k) (hv k) (hs k)
      (B := 1) (hb k) (hn k) (hrep k) (hgrad k) (hsupp k) (hr k) (hmass k) (hw k)

end RegularPointCoordinates

end

end OAI
