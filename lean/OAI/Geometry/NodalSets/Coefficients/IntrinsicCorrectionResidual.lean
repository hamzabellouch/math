import OAI.Geometry.NodalSets.Coefficients.CompactResidualMultiplier
import OAI.Geometry.NodalSets.Coefficients.IntrinsicTotalResidual

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set
open scoped ContDiff Topology
noncomputable section

def seedCoordDensity (rho : Base → ℝ) (x : Coord) : ℝ :=
  rho ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x))

lemma seedCoordDensity_smooth (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) : ContDiff ℝ ∞ (seedCoordDensity rho) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact (smooth_inverse_chart_comp rho hr seedPoint
    (by rw [centeredSphereChart_target]; trivial)).comp x seedCoordEquiv.contDiff.contDiffAt

def intrinsicCorrectionResidual (A : IntrinsicTensor) (rho : Base → ℝ)
    (lam : ℝ) (u : Coord → ℝ) (x : Coord) : ℂ :=
  -(seedCoordDensity rho x:ℂ) *
    realSourceResidual (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) lam u x

lemma intrinsicCorrectionResidual_divergence (A : IntrinsicTensor) (hAs : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hrp : ∀ x, 0 < rho x)
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (lam : ℝ) (x : Coord) :
    intrinsicCorrectionResidual A rho lam
      (fun z ↦ f ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv z))) x =
      (-(roundChartDensity seedPoint (seedCoordEquiv x))⁻¹ *
        (∑ i, fderiv ℝ (intrinsicRoundFlux A f seedPoint i) (seedCoordEquiv x)
          (EuclideanSpace.basisFun (Fin 4) ℝ i)) -
        lam*seedCoordDensity rho x*f ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)):ℝ) := by
  rw [intrinsicCorrectionResidual,realSourceResidual,
    intrinsicSeedCoordOperator A hAs hs hp rho hrp f hf]
  have hn : seedCoordDensity rho x ≠ 0 := (hrp _).ne'
  simp only [intrinsicWeightedChartOperator,seedCoordDensity,
    Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_inv]
  have hn' : (rho ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)):ℂ) ≠ 0 := by
    exact_mod_cast hn
  field_simp
  ring

theorem intrinsicCorrectionResidual_bound (A : IntrinsicTensor) (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) {Q : Set Coord} (hQ : IsCompact Q) (k : ℕ) :
    ∃ B > 0, ∀ (lam : ℝ) (u : Coord → ℝ),
      let R := realSourceResidual (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) lam u
      ContDiff ℝ ∞ R → tsupport R ⊆ Q →
      ContDiff ℝ ∞ (intrinsicCorrectionResidual A rho lam u) ∧
      tsupport (intrinsicCorrectionResidual A rho lam u) ⊆ Q ∧
      ∀ (H : Coord → ℝ), (∀ x, 0 ≤ H x) →
        (∀ x, DerivativeBound k R x (H x)) → ∀ x,
          DerivativeBound k (intrinsicCorrectionResidual A rho lam u) x (B*H x) := by
  have hmul := compact_residual_multiplier (fun x ↦ -(seedCoordDensity rho x:ℂ))
    (Complex.ofRealCLM.contDiff.comp (seedCoordDensity_smooth rho hr)).neg hQ k
  obtain ⟨B,hB,h⟩ := hmul
  exact ⟨B,hB,fun lam u ↦ h _⟩

end
end Yau.Target

end OAI
