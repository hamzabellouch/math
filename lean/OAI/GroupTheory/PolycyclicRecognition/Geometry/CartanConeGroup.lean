import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConeTrace
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentLieModel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentQuotientIntegration

namespace OAI

/-! # Actual simply connected groups for the Cartan cone quotients -/

noncomputable section
namespace PolycyclicRecognition
namespace CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold ContDiff

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

/-- The canonical Lie algebra projection onto the mixed-word quotient. -/
def coneProjection (C : Set (H →ₗ[ℝ] ℝ)) :
    cartanRootIdeal H →ₗ⁅ℝ⁆ (cartanRootIdeal H) ⧸ M.coneWordIdeal C :=
  { (M.coneWordIdeal C).toSubmodule.mkQ with map_lie' := fun {_ _} => rfl }

theorem coneProjection_surjective (C : Set (H →ₗ[ℝ] ℝ)) :
    Function.Surjective (M.coneProjection C) :=
  (M.coneWordIdeal C).toSubmodule.mkQ_surjective

theorem coneQuotient_nilpotent (C : Set (H →ₗ[ℝ] ℝ)) :
    LieRing.IsNilpotent ((cartanRootIdeal H) ⧸ M.coneWordIdeal C) := by
  let : LieRing.IsNilpotent (cartanRootIdeal H) := LieModule.IsNilpotent.mk (cartanRootIdeal H) M.bound_zero
  exact (M.coneProjection_surjective C).lieAlgebra_isNilpotent

/-- Lie correspondence supplies the quotient group, while the actual
algebra projection supplies its surjective group map and compact lifts.
The kernel is precisely the exponential image of the mixed-word ideal. -/
theorem exists_cone_group_quotient
    (C : Set (H →ₗ[ℝ] ℝ))
    (N : NilpotentLieModel (cartanRootIdeal H))
    (ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier)
    (hExpN : IsGroupExponential ExpN)
    (haarN : NilpotentExponentialHaarInput N.modelSpace N.carrier)
    (existQ : NilpotentLieExistenceInput ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (haarQ : ∀ Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C),
      NilpotentExponentialHaarInput Q.modelSpace Q.carrier)
    (integrate : ∀ Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C),
      NilpotentLieIntegrationInput (EN := N.modelSpace) (N := N.carrier)
        (EG := Q.modelSpace) (G := Q.carrier)) :
    ∃ (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
      (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier),
      IsGroupExponential ExpQ ∧
      ∃ (π : N.carrier →* Q.carrier) (s : C(Q.carrier, N.carrier)),
        ContMDiff (𝓘(ℝ, N.modelSpace)) (𝓘(ℝ, Q.modelSpace)) ∞ π ∧
        (∀ x : cartanRootIdeal H,
          π (ExpN (N.equiv x)) = ExpQ (Q.equiv (M.coneProjection C x))) ∧
        (∀ y, π (s y) = y) ∧ Function.Surjective π ∧
        (π.ker : Set N.carrier) = ExpN '' (N.equiv '' (M.coneWordIdeal C : Set (cartanRootIdeal H))) ∧
        ∀ K : Set Q.carrier, IsCompact K →
          ∃ D : Set N.carrier, IsCompact D ∧ π '' D = K := by
  have hnilN : LieRing.IsNilpotent (cartanRootIdeal H) := LieModule.IsNilpotent.mk (cartanRootIdeal H) M.bound_zero
  obtain ⟨Q⟩ := existQ (M.coneQuotient_nilpotent C)
  obtain ⟨ExpQ, hExpQ, cQ, hcQ⟩ := Q.exists_exponential_chart (M.coneQuotient_nilpotent C) (haarQ Q)
  obtain ⟨cN, hcN⟩ := (haarN.2 ExpN hExpN (N.tangent_nilpotent hnilN)).1
  let j := Q.equiv.toLieHom.comp ((M.coneProjection C).comp N.equiv.symm.toLieHom)
  have hj : Function.Surjective j :=
    Q.equiv.surjective.comp ((M.coneProjection_surjective C).comp N.equiv.symm.surjective)
  obtain ⟨π, s, hsmooth, hπ, _hlog, hs, hsurj, hker, hlift⟩ :=
    exists_surjective_integration_with_section (integrate Q) (N.tangent_nilpotent hnilN)
      j hj ExpN ExpQ hExpN hExpQ cN hcN cQ hcQ
  refine ⟨Q, ExpQ, hExpQ, π, s, hsmooth, ?_, hs, hsurj, ?_, hlift⟩
  · intro x
    simpa [j] using hπ (N.equiv x)
  · rw [hker]
    ext n
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : M.coneProjection C (N.equiv.symm v) = 0 := by
        apply Q.equiv.injective
        simpa [j] using hv
      have hi : N.equiv.symm v ∈ M.coneWordIdeal C :=
        (Submodule.Quotient.mk_eq_zero (M.coneWordIdeal C).toSubmodule).mp hv'
      exact ⟨v, ⟨N.equiv.symm v, hi, N.equiv.apply_symm_apply v⟩, (hcN v).symm⟩
    · rintro ⟨v, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨N.equiv x, ?_, hcN _⟩
      change j (N.equiv x) = 0
      have hx' : M.coneProjection C x = 0 :=
        (Submodule.Quotient.mk_eq_zero (M.coneWordIdeal C).toSubmodule).mpr hx
      simp [j, hx']

end CartanWordModel
end PolycyclicRecognition

end

end OAI
