import OAI.Geometry.RCD.Coordinates.RegularBochnerForm
import OAI.Geometry.RCD.Sobolev.LocalMixedSourceIdentity

namespace OAI

/-! # Local Sobolev sources in the polarized Bochner identity -/

open Set MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) {m : ℕ}

theorem regularBochnerForm_local_sources (K : ℝ)
    (U : Euclidean m →L[ℝ] SobolevSpace μ hQ) (D : Euclidean m →L[ℝ] Lp ℝ 2 μ)
    (H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace μ hQ)
    (q : X →ᵇ ℝ) (ψ : SobolevSpace μ hQ) (L : Euclidean m → ℝ≥0)
    (hU : ∀ a, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (U a) x≤L a)
    {Ω : Set X} (hΩ : MeasurableSet Ω) (hq : tsupport q ⊆ Ω)
    (hψ : SobolevSpace.toLp μ hQ ψ =ᵐ[μ] q)
    (a b : Euclidean m) (da db : SobolevSpace μ hQ)
    (hda : IsWeakLaplacian μ hQ (U a) (D a))
    (hdb : IsWeakLaplacian μ hQ (U b) (D b))
    (hsa : D a =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ da)
    (hsb : D b =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ db)
    (A B : ℝ≥0)
    (ha : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ da x|≤A)
    (hb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ db x|≤B) :
    regularBochnerForm μ hQ K U D H q ψ L hU a b =
      bochnerTestForm μ hQ (-K) (H a b) ψ-
      (1/2 : ℝ)*((∫ x, q x*localGamma μ hQ (U a) db x ∂μ)+
        (∫ x, q x*localGamma μ hQ (U b) da x ∂μ)) := by
  have hψb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ ψ x|≤(‖q‖₊:ℝ) := by
    filter_upwards [hψ] with x hx
    simpa only [hx,Real.norm_eq_abs,coe_nnnorm] using q.norm_coe_le_norm x
  have h₁ := weakLaplacian_local_mixed_identity μ hQ hΩ (U a) db ψ (D a) (D b)
    hda hsb B ‖q‖₊ hb hψb q hψ hq
  have h₂ := weakLaplacian_local_mixed_identity μ hQ hΩ (U b) da ψ (D b) (D a)
    hdb hsa A ‖q‖₊ ha hψb q hψ hq
  have hc : (∫ x, q x*D b x*D a x ∂μ) = ∫ x, q x*D a x*D b x ∂μ := by
    congr 1
    funext x
    ring
  rw [hc] at h₂
  change bochnerTestForm μ hQ (-K) (H a b) ψ+weightedLaplacianPair μ q (D a) (D b)+
    (1/2 : ℝ)*(weightedGamma μ hQ (D a) (U b) ψ+weightedGamma μ hQ (D b) (U a) ψ) = _
  rw [weightedLaplacianPair_apply]
  linarith only [h₁,h₂]

end RegularPointCoordinates

end

end OAI
