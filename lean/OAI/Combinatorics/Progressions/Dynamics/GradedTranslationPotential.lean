import OAI.Combinatorics.Progressions.Nilpotent.PolynomialPotentialBCHHom

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
variable {σ : Type*} [Fintype σ]

theorem exists_graded_translation_potential (w : σ → ℕ) {d : ℕ}
    (hw : ∀ i, 0 < w i) (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hU : U.toSubmodule ≤ (weightedSubalgebra w d).toSubmodule)
    (hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (U.toSubmodule.comap (weightedSubalgebra w d).subtype))
    (hbase : Function.Surjective (fun x : U => x.val.base))
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0) :
    ∃ V : MvPolynomial σ ℚ, V.IsWeightedHomogeneous w d ∧
      ∀ x ∈ U, scalarDirectionalDerivative x.base V = x.polynomial := by
  classical
  obtain ⟨P,hlift,hhom⟩ := exists_ambient_homogeneous_coordinate_lifts
    w d hw U.toSubmodule hU hgraded hbase
  exact exists_weighted_potential_of_top_frequency w hd hwd U
    (fun x hx => topProjection_mem_of_basisGraded w d hw hd U.toSubmodule hU hgraded hx)
    frequency hfrequency hkill P hlift hhom

end Erdos3.PolynomialTranslationLie

end

end OAI
