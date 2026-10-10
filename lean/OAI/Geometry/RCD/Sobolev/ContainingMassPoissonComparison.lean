import OAI.Geometry.RCD.Sobolev.ContainingMassCutoffDifference
import OAI.Geometry.RCD.Sobolev.ContainingMassCutoffErrors
import OAI.Geometry.RCD.Sobolev.PoissonStrongComparison
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

theorem poisson_strong_cutoff_comparison_containing_mass (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (Ω : ℕ → Set X) [∀ k, IsFiniteMeasure (μ.restrict (Ω k))]
    (m : ℕ → ℝ) (hmass : ∀ k, 0 < m k)
    (hmass_le : ∀ k, μ.real (Ω k) ≤ m k) (r : ℕ → ℝ) (hr : ∀ k, 0<r k)
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
    (hvalue : Tendsto (fun k => (m k)⁻¹*
      ∫ x in Ω k, (SobolevSpace.toLp μ hQ (w k-q k) x)^2 ∂μ) atTop (𝓝 0))
    (hq : Tendsto (fun k => r k^2*(m k)⁻¹*∫ x in Ω k, (v k x)^2*localGamma μ hQ (q k) (q k) x ∂μ)
      atTop (𝓝 E))
    (hlower : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      E-δ≤r k^2*(m k)⁻¹*∫ x in Ω k, (v k x)^2*localGamma μ hQ (w k) (w k) x ∂μ) :
    Tendsto (fun k => r k^2*(m k)⁻¹*∫ x in Ω k, (v k x)^2*localGamma μ hQ (w k-q k) (w k-q k) x ∂μ)
      atTop (𝓝 0) := by
  let z : ℕ → X → ℝ := fun k x => SobolevSpace.toLp μ hQ (w k-q k) x
  let S := fun k => a k*(m k)⁻¹*∫ x in Ω k, (v k x)^2*z k x ∂μ
  let T := fun k => r k^2*(m k)⁻¹*
    ∫ x in Ω k, v k x*z k x*localGamma μ hQ (w k) (η k) x ∂μ
  have hvb : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k), |v k x|≤(1:ℝ) :=
    Eventually.of_forall fun k => Eventually.of_forall (hb k)
  have hzm (k : ℕ) : MemLp (z k) 2 (μ.restrict (Ω k)) :=
    (Lp.memLp (SobolevSpace.toLp μ hQ (w k-q k))).restrict (Ω k)
  have hvm (k : ℕ) : AEStronglyMeasurable (v k) (μ.restrict (Ω k)) :=
    (hv k).continuous.aestronglyMeasurable
  have hS : Tendsto S atTop (𝓝 0) := by
    simpa only [S,Measure.real,Measure.restrict_apply_univ] using
      containing_mass_source_l2_error_tendsto (fun k => μ.restrict (Ω k)) m hmass
        (fun k => by simpa only [Measure.real,Measure.restrict_apply_univ] using hmass_le k) z v a hA ha hvb
        hzm hvm (by simpa only [z,Measure.real,Measure.restrict_apply_univ] using hvalue)
  have hT : Tendsto T atTop (𝓝 0) :=
    containing_mass_gamma_l2_error_tendsto μ hQ Ω m hmass hmass_le r (fun k => (hr k).le)
      w η z v hM hL zero_le_one hwgrad hηgrad hvb hzm hvm hvalue
  apply poisson_energy_gap_tendsto_zero (S := S) (T := T) _ _ hq hlower hS hT
  · intro k
    apply mul_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (hmass k).le))
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_of_ae (localGamma_self μ hQ (w k-q k))] with x hx
    exact mul_nonneg (sq_nonneg _) (hx ▸ sq_nonneg _)
  · intro k
    exact containing_mass_cutoff_difference_energy μ hQ (w k) (q k) (η k) (hv k) (hs k)
      (B := 1) (hb k) (hn k) (hrep k) (hgrad k) (hsupp k) (hr k) (m k) (hw k)

end RegularPointCoordinates

end

end OAI
