import OAI.Combinatorics.Progressions.Estimates.StrongRefiltrationReconstruction

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

noncomputable def gradedRefiltrationInclusionHom (W : LieSubalgebra ℚ F.AssociatedGraded) :
    (F.gradedRefiltration W).Group →* F.Group :=
  mapOfSteps (F.gradedRefiltrationSubalgebra W).incl

noncomputable def gradedRefiltrationMarkedHom (W : LieSubalgebra ℚ F.AssociatedGraded) :
    (F.gradedRefiltration W).Group →*
      (G.gradedRefiltration (W.map (F.associatedGradedMap G φ hφ))).Group :=
  mapOfSteps (F.gradedRefiltrationMap G φ hφ W)

theorem gradedRefiltrationMarkedHom_inclusion (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.gradedRefiltration W).Group) :
    G.gradedRefiltrationInclusionHom (W.map (F.associatedGradedMap G φ hφ))
      (F.gradedRefiltrationMarkedHom G φ hφ W g) =
        mapOfSteps (hL := F.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
          (F.gradedRefiltrationInclusionHom W g) := rfl

theorem gradedRefiltrationMarkedHom_lattice (W : LieSubalgebra ℚ F.AssociatedGraded)
    (Γ : Subgroup F.Group) (Λ : Subgroup G.Group)
    (hφL : Γ ≤ Λ.comap (mapOfSteps
      (hL := F.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ)) :
    Γ.comap (F.gradedRefiltrationInclusionHom W) ≤
      (Λ.comap (G.gradedRefiltrationInclusionHom
        (W.map (F.associatedGradedMap G φ hφ)))).comap
          (F.gradedRefiltrationMarkedHom G φ hφ W) := by
  intro g hg
  change G.gradedRefiltrationInclusionHom (W.map (F.associatedGradedMap G φ hφ))
    (F.gradedRefiltrationMarkedHom G φ hφ W g) ∈ Λ
  rw [F.gradedRefiltrationMarkedHom_inclusion G φ hφ W g]
  exact hφL hg

end Erdos3.NilpotentLieFiltration

end

end OAI
