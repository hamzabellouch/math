import OAI.Geometry.NodalSets.Coefficients.IntrinsicCorrectionResidual
import OAI.Geometry.NodalSets.Coefficients.RoundSupportedCorrection

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set
open scoped ContDiff Topology
noncomputable section

def intrinsicRealCorrectionResidual (A : IntrinsicTensor) (rho : Base → ℝ)
    (lam : ℝ) (u : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) : ℝ :=
  (intrinsicCorrectionResidual A rho lam u x).re

lemma intrinsicRealCorrectionResidual_divergence (A : IntrinsicTensor) (hAs : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v) (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hrp : ∀ x, 0 < rho x)
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (lam : ℝ) (x : Yau.Jets.Coord) :
    intrinsicRealCorrectionResidual A rho lam
      (fun z ↦ f ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv z))) x =
      -(roundCoordDensity x)⁻¹ *
        (∑ i, fderiv ℝ (intrinsicRoundFlux A f seedPoint i) (seedCoordEquiv x)
          (EuclideanSpace.basisFun (Fin 4) ℝ i)) -
        lam*seedCoordDensity rho x*f ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)) := by
  exact congrArg Complex.re (intrinsicCorrectionResidual_divergence A hAs hs hp rho hrp f hf lam x)

lemma intrinsicRealCorrectionResidual_support (A : IntrinsicTensor) (rho : Base → ℝ)
    (lam : ℝ) (u : Yau.Jets.Coord → ℝ) :
    tsupport (intrinsicRealCorrectionResidual A rho lam u) ⊆
      tsupport (intrinsicCorrectionResidual A rho lam u) := by
  apply closure_mono
  intro x hx hz
  apply hx
  simp only [intrinsicRealCorrectionResidual,hz,Complex.zero_re]

theorem intrinsic_real_supported_correction (A : IntrinsicTensor) (rho : Base → ℝ)
    (hrs : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (u H : Yau.Jets.Coord → ℝ)
    {Ω Q : Set Yau.Jets.Coord} (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hu : ContDiff ℝ ∞ u) {n : ℕ} (hn : 0 < n)
    (hR : ContDiff ℝ ∞ (realSourceResidual (intrinsicSeedCoordMetric A rho)
      (seedCoordWeight rho) (seedEigenvalue n) u))
    (hsupport : tsupport (realSourceResidual (intrinsicSeedCoordMetric A rho)
      (seedCoordWeight rho) (seedEigenvalue n) u) ⊆ Q)
    (hH : ∀ x ∈ Ω, 0 < H x)
    (hjet : ∀ x ∈ Ω, ((n:ℝ)^65)⁻¹*H x ≤ sourceFirstJetSize u n x) :
    ∃ f : Yau.Jets.Coord → ℝ,
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Q ∧
      (∀ x, f x = intrinsicRealCorrectionResidual A rho (seedEigenvalue n) u x /
        roundCorrectionDenominator u n x) ∧
      ∀ x, Yau.weightedDiv roundCoordDensity
          (fun y i ↦ u y * (f y * roundCoordGradient u y i)) x +
        seedEigenvalue n * (f x * u x - (seedEigenvalue n)⁻¹ *
          Yau.weightedDiv roundCoordDensity (fun y i ↦ f y * roundCoordGradient u y i) x) * u x =
        intrinsicRealCorrectionResidual A rho (seedEigenvalue n) u x := by
  obtain ⟨B,hB,hbound⟩ := intrinsicCorrectionResidual_bound A rho hrs hQ 0
  obtain ⟨hsm,hsup,_⟩ := hbound (seedEigenvalue n) u hR hsupport
  have hrsm : ContDiff ℝ ∞ (intrinsicRealCorrectionResidual A rho (seedEigenvalue n) u) :=
    Complex.reCLM.contDiff.comp hsm
  have hrsup := (intrinsicRealCorrectionResidual_support A rho (seedEigenvalue n) u).trans hsup
  obtain ⟨f,hf,hfc,hfs,hval,heq⟩ := round_supported_exact_correction u
    (intrinsicRealCorrectionResidual A rho (seedEigenvalue n) u) H hQ hQΩ hu hrsm hrsup hn hH hjet
  exact ⟨f,hf,hfc,hfs.trans hrsup,hval,heq⟩

end
end Yau.Target

end OAI
