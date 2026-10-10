import OAI.Analysis.CircleDomains.Probability.LocalHorizontalNullPair
import OAI.Analysis.CircleDomains.Selection.ControlledHeight

namespace OAI

/-! The constructed conductivity height and the ordinary horizontal
coordinate have a null-area joint trace on the omitted set. -/
open Set Function MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem ControlledHeight.horizontal_pair_null
    (hcoarea : PlanarSobolevCoarea) {R d : ℝ} (H : ControlledHeight R d)
    {F : Set ℂ} (hF : IsCompact F)
    (hz : ∀ᵐ p ∂volume.restrict (complexPlaneCoordinates ⁻¹' F),
      heightLimitGradient H.error₀ H.error₁ p = 0) :
    volume ((fun z => (H.height z, z.re)) '' F) = 0 := by
  obtain ⟨S, hS⟩ := hF.isBounded.subset_ball 0
  let T := max S 1
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hFT : F ⊆ interior (closedBall (0 : ℂ) T) := by
    rw [interior_closedBall _ hT.ne']
    exact hS.trans (ball_subset_ball (le_max_left _ _))
  let K := complexPlaneCoordinates ⁻¹' F
  have hK : IsCompact K := complexPlaneCoordinates.toHomeomorph.isCompact_preimage.mpr hF
  obtain ⟨A, hA⟩ := hK.isBounded.subset_ball 0
  have hh := local_sobolev_horizontal_pair_null_image hcoarea hF
    (isCompact_closedBall 0 T) hFT isOpen_ball hA
    (H.height.continuous.comp complexPlaneCoordinates.continuous)
    (heightLimitWitness H.error₀ H.error₁
      (H.height.continuous.comp complexPlaneCoordinates.continuous) H.weak_gradient A) hz
  simpa only [Function.comp_apply, complexPlaneCoordinates.apply_symm_apply] using hh

end CircleDomainRigidity

end

end OAI
