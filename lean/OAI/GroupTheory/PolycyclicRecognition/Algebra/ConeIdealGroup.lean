import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConeGroup

namespace OAI

/-! # The actual simply connected group of a cone ideal

The mixed ideal integrates to the kernel of the constructed quotient map.
This provides its intrinsic Haar measure and polynomial exponential
coordinates for the ideal boxes.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold ContDiff

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

theorem coneIdeal_nilpotent (C : Set (H →ₗ[ℝ] ℝ)) :
    LieRing.IsNilpotent (M.coneWordIdeal C) := by
  let : LieRing.IsNilpotent (cartanRootIdeal H) :=
    LieModule.IsNilpotent.mk (cartanRootIdeal H) M.bound_zero
  exact (show Function.Injective (M.coneWordIdeal C).incl from Subtype.val_injective).lieAlgebra_isNilpotent

/-- Lie correspondence realizes the mixed ideal as exactly the kernel of
the already constructed quotient, with a closed embedding into the
nilpotent factor and the correct intrinsic exponential. -/
theorem exists_cone_ideal_group
    (C : Set (H →ₗ[ℝ] ℝ))
    (N : NilpotentLieModel (cartanRootIdeal H))
    (ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier)
    (hExpN : IsGroupExponential ExpN)
    (haarN : NilpotentExponentialHaarInput N.modelSpace N.carrier)
    {Q : Type*} [Group Q] (π : N.carrier →* Q)
    (hker : (π.ker : Set N.carrier) =
      ExpN '' (N.equiv '' (M.coneWordIdeal C : Set (cartanRootIdeal H))))
    (existI : NilpotentLieExistenceInput (M.coneWordIdeal C))
    (haarI : ∀ I : NilpotentLieModel (M.coneWordIdeal C),
      NilpotentExponentialHaarInput I.modelSpace I.carrier)
    (integrate : ∀ I : NilpotentLieModel (M.coneWordIdeal C),
      NilpotentLieIntegrationInput (EN := I.modelSpace) (N := I.carrier)
        (EG := N.modelSpace) (G := N.carrier)) :
    ∃ (I : NilpotentLieModel (M.coneWordIdeal C))
      (ExpI : GroupLieAlgebra (𝓘(ℝ, I.modelSpace)) I.carrier → I.carrier),
      IsGroupExponential ExpI ∧
      ∃ ι : I.carrier →* N.carrier,
        Topology.IsClosedEmbedding ι ∧
        ContMDiff (𝓘(ℝ, I.modelSpace)) (𝓘(ℝ, N.modelSpace)) ∞ ι ∧
        (∀ x : M.coneWordIdeal C, ι (ExpI (I.equiv x)) = ExpN (N.equiv x)) ∧
        Set.range ι = (π.ker : Set N.carrier) := by
  obtain ⟨I⟩ := existI (M.coneIdeal_nilpotent C)
  obtain ⟨ExpI, hExpI, cI, hcI⟩ := I.exists_exponential_chart (M.coneIdeal_nilpotent C) (haarI I)
  have hnilN : LieRing.IsNilpotent (cartanRootIdeal H) :=
    LieModule.IsNilpotent.mk (cartanRootIdeal H) M.bound_zero
  obtain ⟨cN, hcN⟩ := (haarN.2 ExpN hExpN (N.tangent_nilpotent hnilN)).1
  let j := N.equiv.toLieHom.comp ((M.coneWordIdeal C).incl.comp I.equiv.symm.toLieHom)
  have hj : Function.Injective j :=
    N.equiv.injective.comp (Subtype.val_injective.comp I.equiv.symm.injective)
  obtain ⟨ι, hclosed, hsmooth, _hdiff, hι, hrange⟩ := exists_closed_integration
    (integrate I) (I.tangent_nilpotent (M.coneIdeal_nilpotent C)) j hj
    ExpI ExpN hExpI hExpN cI hcI cN hcN
  refine ⟨I, ExpI, hExpI, ι, hclosed, hsmooth, ?_, ?_⟩
  · intro x
    simpa [j] using hι (I.equiv x)
  · rw [hrange, hker]
    congr 1
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(I.equiv.symm x : cartanRootIdeal H), (I.equiv.symm x).property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨I.equiv ⟨x, hx⟩, ?_⟩
      simp [j]

end PolycyclicRecognition.CartanWordModel

end

end OAI
