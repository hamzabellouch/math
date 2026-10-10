import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeAdaptedMaximalBasis
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxExponents
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TemplateSymmetries

namespace OAI

/-! # The ideal exponent is the full template support exponent -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule LieAlgebra Set
open scoped BigOperators

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- If the cone widths vanish, the pure quotient words contribute zero.
Completing a maximal ideal basis therefore gives exactly `P(E)`. -/
theorem sum_coneIdealCost_eq_templateSupport
    (C : Set (H →ₗ[ℝ] ℝ))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (E : Set W)
    (hs : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport E i)
    (hz : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport E i = 0)
    (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI
      ((M.supportIn T hunimod eW).weightSupport E) β) :
    (∑ j, M.coneIdealWordCost C ((M.supportIn T hunimod eW).weightSupport E) (β.val j)) =
      (M.supportIn T hunimod eW).templateSupport E := by
  obtain ⟨γ, hγ, hsum⟩ := M.exists_cone_adapted_maximal_basis C bN bI
    ((M.supportIn T hunimod eW).weightSupport E) hs hz β hβ
  have he := M.columnBasisWeight_eq_templateSupport_of_maximizing T hunimod eW bN E γ hγ
  exact hsum.symm.trans he

/-- The target ideal exponent agrees with the source template exponent
under the actual finite template-symmetry label. -/
theorem sum_coneIdealCost_image_templateSymmetry [FiniteDimensional ℝ W]
    (C : Set (H →ₗ[ℝ] ℝ))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (E : Set W) (hE : IsCompact E) (hne : E.Nonempty) (hconv : Convex ℝ E)
    (A : templateSymmetryGroup (M.supportIn T hunimod eW))
    (hs : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport (A.val '' E) i)
    (hz : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport (A.val '' E) i = 0)
    (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C bI
      ((M.supportIn T hunimod eW).weightSupport (A.val '' E)) β) :
    (∑ j, M.coneIdealWordCost C
      ((M.supportIn T hunimod eW).weightSupport (A.val '' E)) (β.val j)) =
      (M.supportIn T hunimod eW).templateSupport E :=
  (M.sum_coneIdealCost_eq_templateSupport T hunimod eW C bN bI (A.val '' E) hs hz β hβ).trans
    (A.property E hE hne hconv)

end PolycyclicRecognition.CartanWordModel

end

end OAI
