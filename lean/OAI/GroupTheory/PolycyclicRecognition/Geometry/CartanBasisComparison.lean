import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxScaling
import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightedBasisComparison

namespace OAI

/-! # Uniform comparison with a maximizing Cartan basis -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- Replacing a selected word basis by a maximizing one costs a fixed
multiplicative factor in the radius, uniformly in the template and scale. -/
theorem exists_groupBox_basis_comparison
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (E : Set W) (β γ : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ (r : ℝ), 0 ≤ r → ∀ {N : Type*} (exp : cartanRootIdeal H → N) (R : ℝ),
        M.groupBox T hunimod eW exp E γ r R ⊆
          M.groupBox T hunimod eW exp E β r (C * R) := by
  obtain ⟨C, hC, hcompare⟩ := exists_uniform_rescaled_basis_comparison M.letter M.wordList b₀
  refine ⟨C, hC, ?_⟩
  intro E β γ hβ r hr N exp R g hg
  obtain ⟨v, hv, hnorm⟩ := hg
  refine ⟨v, hv, ?_⟩
  exact (hcompare (M.boxCost T hunimod eW E) β γ hβ r hr v).trans
    (mul_le_mul_of_nonneg_left hnorm (zero_le_one.trans hC))

end PolycyclicRecognition.CartanWordModel

end

end OAI
