import OAI.Analysis.CircleDomains.Transfer.FilledCoordinates

namespace OAI

/-!
# The actual differential of the cutoff staircase

This identifies the random covectors used in the wedge-cost selection
with derivatives of the modified scalar coordinates.
-/

open Set Filter
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem planarGradient_cutoffStaircase
    {u χ : (ℝ × ℝ) → ℝ} {z : ℝ × ℝ}
    (hu : DifferentiableAt ℝ u z) (hχ : DifferentiableAt ℝ χ z)
    {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (θ : ℝ) :
    planarGradient (cutoffStaircase u χ (shiftedStaircase h δ θ)) z =
      staircaseCovector h δ (χ z) θ (u z) (planarGradient u z) (planarGradient χ z) := by
  have hP := ((contDiff_shiftedStaircase hh hδ hδh θ).differentiable (by simp) (u z)).hasDerivAt
  have hd := (hasFDerivAt_cutoffStaircase hu.hasFDerivAt hχ.hasFDerivAt hP).fderiv
  ext <;> simp [planarGradient, hd, staircaseCovector, smul_eq_mul]

theorem contDiffOn_cutoff_shiftedStaircase
    {Ω : Set (ℝ × ℝ)} {u χ : (ℝ × ℝ) → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hχ : ContDiffOn ℝ ∞ χ Ω)
    {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (θ : ℝ) :
    ContDiffOn ℝ ∞ (cutoffStaircase u χ (shiftedStaircase h δ θ)) Ω := by
  exact hu.add (hχ.mul (((contDiff_shiftedStaircase hh hδ hδh θ).comp_contDiffOn hu).sub hu))

end CircleDomainRigidity.FiniteTransfer

end

end OAI
