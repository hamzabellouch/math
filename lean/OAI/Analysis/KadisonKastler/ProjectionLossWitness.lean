import OAI.Analysis.KadisonKastler.ProjectionNoLoss

namespace OAI

/-! Failure of right modularity has a positive projection-row loss witness. -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_projection_loss_of_not_right_module (M : VonNeumannAlgebra H)
    (F : Algebra M →L[ℂ] Algebra M) (hF : ¬ ∀ a b, F (a * b) = F a * b) :
    ∃ (p : Algebra M), IsStarProjection p ∧ ∃ (a : Algebra M) (ξ : H),
      ‖(star (projectionAverage p F.toLinearMap a) : H →L[ℂ] H) ξ‖ ^ 2 <
        rowEnergy F.toLinearMap (fun i => a * projectionRow p i) ξ := by
  by_contra! h
  apply hF
  apply right_module_of_projection_no_loss M F
  intro p hp a ξ
  apply le_antisymm (h p hp a ξ)
  change ‖(star (finiteRightAverage (projectionRow p) F.toLinearMap a) : H →L[ℂ] H) ξ‖ ^ 2 ≤ _
  rw [finiteRightAverage_star_apply]
  exact rowSynthesis_norm_sq_le (projectionRow p) (projectionRow_normalized hp) _

end

end KadisonKastler

end OAI
