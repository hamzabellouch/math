import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeQuotientHaar
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConeAction

namespace OAI

/-! # Identifying the descended group action with its Haar multiplier -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N)
  (hExpN : IsGroupExponential ExpN) (hNbij : Function.Bijective ExpN)
  (dynkin : NilpotentDynkinExpansionInput EN N)

/-- The quotient action obtained by descending the actual source-group
automorphism is exactly the exponential of the induced Lie automorphism.
Thus the computed Haar multiplier applies to the descended group action. -/
theorem descended_cone_adjoint_eq_exponentialConjugate
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hQbij : Function.Bijective ExpQ)
    (π : N →* Q.carrier) (s : Q.carrier → N) (hs : Function.RightInverse s π)
    (hπ : ∀ x : cartanRootIdeal H,
      π (ExpN (eN x)) = ExpQ (Q.equiv (M.coneProjection C x)))
    (hker : (π.ker : Set N) = ExpN '' (eN '' (M.coneWordIdeal C : Set (cartanRootIdeal H))))
    (h : H) :
    descendQuotientAutomorphism π s hs
      (M.adjointGroupAutomorphism T eN ExpN hExpN hNbij dynkin h)
      (M.cone_kernel_adjoint_invariant T eN ExpN hExpN hNbij dynkin C hadd π hker h) =
    exponentialConjugate Q.equiv ExpQ hQbij (M.coneAdjointAutomorphism T C hadd h) := by
  apply DFunLike.ext
  intro q
  obtain ⟨v, rfl⟩ := hQbij.surjective q
  obtain ⟨w, rfl⟩ := Q.equiv.surjective v
  obtain ⟨x, rfl⟩ := M.coneProjection_surjective C w
  change descendQuotientAutomorphism π s hs
    (M.adjointGroupAutomorphism T eN ExpN hExpN hNbij dynkin h)
    (M.cone_kernel_adjoint_invariant T eN ExpN hExpN hNbij dynkin C hadd π hker h)
    (ExpQ (Q.equiv (M.coneProjection C x))) =
    exponentialConjugate Q.equiv ExpQ hQbij (M.coneAdjointAutomorphism T C hadd h)
      (ExpQ (Q.equiv (M.coneProjection C x)))
  rw [← hπ x, descendQuotientAutomorphism_project]
  change π (integrateNilpotentLieEquiv eN ExpN hNbij dynkin hExpN M.bound_zero
      (cartanIdealAdjointAutomorphism T H h) (ExpN (eN x))) = _
  rw [integrateNilpotentLieEquiv_apply_exp, hπ, hπ x, exponentialConjugate_apply_exp]
  rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
