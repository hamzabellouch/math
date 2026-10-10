import OAI.GroupTheory.PolycyclicRecognition.Algebra.UniversalDynkinTruncation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialUnipotentModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.UnipotentCoordinateBCH
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialModelExponential

namespace OAI

/-! # The precise finite BCH input for polynomial coordinate models

The faithful representation gives a finite product formula at a concrete
operator bound. Coefficient stability and vanishing of long brackets reduce
it to every supplied lower-central-series bound.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem polynomialCoordinate_product_of_class {c n : ℕ}
    (hc : LieModule.lowerCentralSeries ℝ L L c = ⊥) (X : Fin n → L) :
    (List.ofFn X).prod = finiteDynkinPolynomial (universalDynkinCoefficients c n) X := by
  obtain ⟨m, d, ρ, j, hρ, _, _, hexp, _, hd⟩ :=
    exists_polynomial_unipotent_model (Module.finBasis ℝ L)
  let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hp := finite_product_of_unipotent_coordinates ρ hρ j hexp (max c d)
    (fun l hl => hd l ((Nat.le_max_right c d).trans hl.le)) X
  exact hp.trans (universalDynkinPolynomial_truncate (Nat.le_max_left c d) hc X)

theorem nilpotentDynkinExpansionInput_polynomial : NilpotentDynkinExpansionInput L L := by
  intro Exp hExp c hc n
  have hexp := hExp.unique (PolynomialExponentialCoordinates.isGroupExponential_identity
    (L := L) (P := P))
  subst Exp
  refine ⟨universalDynkinCoefficients c n, universalDynkinCoefficients_bound c n, ?_⟩
  intro X
  have hcL := LieIdeal.lowerCentralSeries_map_eq (f := P.tangentEquiv.symm.toLieHom)
    c P.tangentEquiv.symm.surjective
  rw [hc, (LieIdeal.map_eq_bot_iff (f := P.tangentEquiv.symm.toLieHom)
    (I := ⊥)).mpr bot_le] at hcL
  let Y : Fin n → L := fun i => P.tangentEquiv.symm (X i)
  have hY : (fun i => (X i : L)) = Y := by
    funext i
    have hi := P.tangentEquiv.apply_symm_apply (X i)
    change P.tangentEquiv (Y i) = X i at hi
    rw [P.tangentEquiv_apply] at hi
    exact hi.symm
  change List.prod (α := L) (List.ofFn (fun i => (X i : L))) =
    (finiteDynkinPolynomial (L := GroupLieAlgebra (𝓘(ℝ, L)) L)
      (universalDynkinCoefficients c n) X : L)
  rw [hY, polynomialCoordinate_product_of_class hcL.symm]
  have hm := finiteDynkinPolynomial_map P.tangentEquiv.toLieHom
    (universalDynkinCoefficients c n) Y
  change P.tangentEquiv (finiteDynkinPolynomial (universalDynkinCoefficients c n) Y) = _ at hm
  rw [P.tangentEquiv_apply] at hm
  have hf : (fun i => P.tangentEquiv.toLieHom (Y i)) = X := by
    funext i
    exact P.tangentEquiv.apply_symm_apply (X i)
  rwa [hf] at hm

end PolycyclicRecognition

end

end OAI
