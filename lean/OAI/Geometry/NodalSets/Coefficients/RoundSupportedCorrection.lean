import OAI.Geometry.NodalSets.Coefficients.RoundCorrectionDenominator

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

def roundCoordDensity (x : Yau.Jets.Coord) : ℝ :=
  roundChartDensity seedPoint (seedCoordEquiv x)

lemma roundCoordDensity_pos (x : Yau.Jets.Coord) : 0 < roundCoordDensity x := by
  rw [roundCoordDensity,roundChartDensity_conformal]
  positivity

lemma roundCoordDensity_smooth : ContDiff ℝ ∞ roundCoordDensity := by
  have he : roundCoordDensity = fun x : Yau.Jets.Coord ↦ (4/(‖seedCoordEquiv x‖^2+4))^4 :=
    funext (fun x ↦ roundChartDensity_conformal seedPoint (seedCoordEquiv x))
  rw [he]
  exact (contDiff_const.div (((contDiff_norm_sq ℝ).comp seedCoordEquiv.contDiff).add contDiff_const)
    (fun x ↦ by change ‖seedCoordEquiv x‖^2+4 ≠ 0; positivity)).pow 4

theorem round_supported_exact_correction (u R H : Yau.Jets.Coord → ℝ)
    {Ω Q : Set Yau.Jets.Coord} (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hu : ContDiff ℝ ∞ u) (hR : ContDiff ℝ ∞ R) (hsupport : tsupport R ⊆ Q)
    {n : ℕ} (hn : 0 < n) (hH : ∀ x ∈ Ω, 0 < H x)
    (hjet : ∀ x ∈ Ω, ((n:ℝ)^65)⁻¹*H x ≤ sourceFirstJetSize u n x) :
    ∃ f : Yau.Jets.Coord → ℝ,
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ tsupport R ∧
      (∀ x, f x = R x / roundCorrectionDenominator u n x) ∧
      ∀ x, Yau.weightedDiv roundCoordDensity
          (fun y i ↦ u y * (f y * roundCoordGradient u y i)) x +
        seedEigenvalue n * (f x * u x - (seedEigenvalue n)⁻¹ *
          Yau.weightedDiv roundCoordDensity (fun y i ↦ f y * roundCoordGradient u y i) x) * u x = R x := by
  have hden : ∀ x ∈ tsupport R,
      Yau.correctionDenominator u (roundCoordGradient u) (seedEigenvalue n) x ≠ 0 := by
    intro x hx
    exact ne_of_gt (roundCorrectionDenominator_pos u hn x (hH x (hQΩ (hsupport hx)))
      (hjet x (hQΩ (hsupport hx))))
  have hlam : seedEigenvalue n ≠ 0 := by
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    unfold seedEigenvalue
    positivity
  exact Yau.global_exact_correction roundCoordDensity_smooth
    (fun x ↦ ne_of_gt (roundCoordDensity_pos x)) hu hR
    (hQ.of_isClosed_subset isClosed_closure hsupport)
    (fun i ↦ (contDiff_pi.mp (roundCoordGradient_smooth u hu)) i) hlam hden

end
end Yau.Target

end OAI
