import OAI.Analysis.KadisonSimilarity.Tracial.TracialSupportedColumns
import OAI.Analysis.KadisonSimilarity.Derivation.FinalDerivations

namespace OAI

/-! A small-corner commutator estimate supplies the actual bounded
rectangular derivation used in the full-column argument. -/

noncomputable section
namespace KadisonSimilarity

open scoped CStarAlgebra

universe u v
variable {P : Type u} {H : Type v} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (e : P) (he : IsStarProjection e) (r : P)

/-- Compression of the ambient operator to the actual domain and output
corners. The domain may have a smaller right support. -/
def cornerRestriction (Y : H →L[ℂ] H) : G.corner e r →L[ℂ] G.corner e 1 :=
  (G.corner e 1).toSubmodule.subtypeL.adjoint.comp
    (Y.comp (G.corner e r).toSubmodule.subtypeL)

theorem cornerRestriction_commutator (Y : H →L[ℂ] H) (a : CStarCorner e he) :
    cornerCommutator (G.cornerRepresentation e he 1) (G.cornerRepresentation e he r)
      (G.cornerRestriction e r Y) a =
      (G.corner e 1).toSubmodule.subtypeL.adjoint.comp
        ((commutator Y (G.left (a : P))).comp (G.corner e r).toSubmodule.subtypeL) := by
  simp only [cornerCommutator_apply, cornerRestriction, commutator,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_assoc]
  rw [← G.corner_inclusion_intertwines e he r a]
  rw [← ContinuousLinearMap.comp_assoc (G.cornerRepresentation e he 1 a),
    ← G.corner_adjoint_intertwines e he 1 a]
  simp only [ContinuousLinearMap.comp_assoc]

/-- The rectangular derivation has norm at most the original small-corner
constant. Orthogonal domain/output compression introduces no dimension factor. -/
theorem norm_cornerRestriction_commutator_le (Y : H →L[ℂ] H) {ε : ℝ} (hε : 0 ≤ ε)
    (hY : ∀ a : CStarCorner e he, ‖commutator Y (G.left (a : P))‖ ≤ ε * ‖a‖) :
    ‖cornerCommutator (G.cornerRepresentation e he 1) (G.cornerRepresentation e he r)
      (G.cornerRestriction e r Y)‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro a
  rw [G.cornerRestriction_commutator e he r Y a]
  calc
    _ ≤ ‖(G.corner e 1).toSubmodule.subtypeL.adjoint‖ *
        (‖commutator Y (G.left (a : P))‖ * ‖(G.corner e r).toSubmodule.subtypeL‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * ((ε * ‖a‖) * 1) := by
      gcongr
      · simpa using (G.corner e 1).toSubmodule.norm_subtypeL_le
      · exact hY a
      · exact (G.corner e r).toSubmodule.norm_subtypeL_le
    _ = ε * ‖a‖ := by ring

/-- The corrected corner intertwiner is obtained with the paper's constant
from projection comparison and the exact published cyclic inputs. -/
theorem exists_corrected_corner
    (τ : P → ℝ) (comparison : FiniteFactorProjectionComparison τ)
    (hr : IsStarProjection r) (hτ : τ r ≤ τ e)
    (Y : H →L[ℂ] H) {ε : ℝ} (hε : 0 ≤ ε)
    (hY : ∀ a : CStarCorner e he, ‖commutator Y (G.left (a : P))‖ ≤ ε * ‖a‖)
    (published : PublishedDerivationInputs.{u,v} (CStarCorner e he)) :
    ∃ T : G.corner e r →L[ℂ] G.corner e 1,
      (∀ a : CStarCorner e he, T.comp (G.cornerRepresentation e he r a) =
        (G.cornerRepresentation e he 1 a).comp T) ∧
      ‖G.cornerRestriction e r Y - T‖ ≤ (1 + 4 * (4 * Real.sqrt 2)) ^ 2 * ε := by
  obtain ⟨v, hv, hev⟩ := comparison e r he hr hτ
  let ρ := G.cornerRepresentation e he 1
  let σ := G.cornerRepresentation e he r
  let Ye := G.cornerRestriction e r Y
  exact exists_corner_intertwiner_of_column_tests ρ σ Ye
    (G.norm_cornerRestriction_commutator_le e he r Y hε hY)
    (published.columns (G.corner e r) σ (G.cornerRepresentation_cyclic e he r hr v hv hev))
    (paulsenSimilarityInput
      (normalizedRectangularRepresentation ρ σ (cornerCommutator ρ σ Ye)
        (cornerCommutator_leibniz ρ σ Ye)))

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
