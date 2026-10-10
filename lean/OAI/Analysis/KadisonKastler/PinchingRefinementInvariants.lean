import OAI.Analysis.KadisonKastler.PartialPinchingRefinement
import OAI.Analysis.KadisonKastler.CornerLossBound

namespace OAI

/-! # The two inequalities preserved by projection-family refinement

The total corner loss is charged to the test-vector displacement; the
reference-vector displacement stays a prescribed small proportion of it.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)

include hJ hright in
theorem partialPinching_refinement_preserves
    (A : H →L[ℂ] H) (hA : IsStarProjection A)
    (q p : AlgebraProjection M) (hpq : p ≤ q)
    (hAq : A*modularQuadratic J q.val=0)
    (ξ η : H) (hξ : J ξ=ξ) (hη : J η=η) (C δ : ℝ)
    (hwide : ‖(1-modularQuadratic J q.val) ξ‖^2+
        ‖(1-modularQuadratic J q.val) η‖^2 ≤
      C*‖(1-(A+modularQuadratic J q.val)) η‖^2)
    (hsmall : ‖(1-(A+modularQuadratic J q.val)) ξ‖^2 ≤
      δ*‖(1-(A+modularQuadratic J q.val)) η‖^2)
    (hmass : 2*(‖p.val.val (modularQuadratic J q.val ξ)‖^2+
        ‖p.val.val (modularQuadratic J q.val η)‖^2) ≤
      C*‖(p.val.val-conjugationOperator J p.val.val) (modularQuadratic J q.val η)‖^2)
    (hdefect : ‖(p.val.val-conjugationOperator J p.val.val) (modularQuadratic J q.val ξ)‖^2 ≤
      δ*‖(p.val.val-conjugationOperator J p.val.val) (modularQuadratic J q.val η)‖^2) :
    (‖(1-modularQuadratic J (q.val-p.val)) ξ‖^2+
        ‖(1-modularQuadratic J (q.val-p.val)) η‖^2 ≤
      C*‖(1-(A+refinedCornerProjection J q p)) η‖^2) ∧
    (‖(1-(A+refinedCornerProjection J q p)) ξ‖^2 ≤
      δ*‖(1-(A+refinedCornerProjection J q p)) η‖^2) := by
  have hξloss := cornerProjection_residual_bound J hJ hright q p hpq ξ hξ
  have hηloss := cornerProjection_residual_bound J hJ hright q p hpq η hη
  have heξ := partialPinching_refinement_energy J hJ hright A hA q p hpq hAq ξ
  have heη := partialPinching_refinement_energy J hJ hright A hA q p hpq hAq η
  constructor
  · rw [heη,mul_add]
    linarith only [hξloss,hηloss,hwide,hmass]
  · rw [heξ,heη,mul_add]
    exact add_le_add hsmall hdefect

end

end KadisonKastler

end OAI
