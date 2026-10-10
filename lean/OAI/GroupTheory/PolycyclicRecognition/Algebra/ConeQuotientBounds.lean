import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanControlledAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeQuotientAutomorphism
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ChainProducts

namespace OAI

/-!
# Polynomial residual bounds on the actual cone quotient

The nilpotent residual part of the Cartan action has polynomial coordinate
growth. Passing to a quotient costs a fixed coordinate constant, obtained
from lifts of a basis. These are estimates for the constructed action,
with no quotient-contraction hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped BigOperators

/-- A coordinate bound passes to an invariant quotient, with a constant
depending only on the two bases and the quotient map. -/
theorem exists_quotient_coordinate_bound
    {V I J : Type*} [AddCommGroup V] [Module ℝ V] [Fintype I] [Fintype J]
    (a : Basis I ℝ V) (S : Submodule ℝ V) (b : Basis J ℝ (V ⧸ S)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : V →ₗ[ℝ] V) (hF : ∀ v ∈ S, F v ∈ S)
      (A : ℝ), 0 ≤ A → (∀ v, ‖a.equivFun (F v)‖ ≤ A * ‖a.equivFun v‖) →
      ∀ z, ‖b.equivFun (S.mapQ S F hF z)‖ ≤ K * A * ‖b.equivFun z‖ := by
  classical
  choose v hv using fun j => S.mkQ_surjective (b j)
  let q : (I → ℝ) →ₗ[ℝ] (J → ℝ) :=
    b.equivFun.toLinearMap.comp (S.mkQ.comp a.equivFun.symm.toLinearMap)
  let Q := q.toContinuousLinearMap
  let K := ‖Q‖ * ∑ j, ‖a.equivFun (v j)‖
  have hq (x : V) : ‖b.equivFun (S.mkQ x)‖ ≤ ‖Q‖ * ‖a.equivFun x‖ := by
    simpa only [Q, q, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.coe_toContinuousLinearMap'] using Q.le_opNorm (a.equivFun x)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro F hF A hA hbound z
  conv_lhs => rw [← b.sum_repr z]
  rw [map_sum, map_sum]
  apply (norm_sum_le _ _).trans
  calc
    (∑ j, ‖b.equivFun (S.mapQ S F hF (b.repr z j • b j))‖) ≤
        ∑ j, ‖b.equivFun z‖ * (‖Q‖ * (A * ‖a.equivFun (v j)‖)) := by
      apply Finset.sum_le_sum
      intro j _
      rw [map_smul, map_smul, norm_smul]
      have hcoord : ‖b.repr z j‖ ≤ ‖b.equivFun z‖ :=
        norm_le_pi_norm (b.equivFun z) j
      have himage : ‖b.equivFun (S.mapQ S F hF (b j))‖ ≤
          ‖Q‖ * (A * ‖a.equivFun (v j)‖) := by
        rw [← hv j]
        exact (hq (F (v j))).trans
          (mul_le_mul_of_nonneg_left (hbound (v j)) (norm_nonneg Q))
      exact mul_le_mul hcoord himage (norm_nonneg _) (norm_nonneg _)
    _ = K * A * ‖b.equivFun z‖ := by
      simp only [K, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

/-- The residual action has a polynomial bound in any fixed unscaled word
basis. No unimodularity assumption is needed for this estimate. -/
theorem exists_residual_coordinate_bound (β : M.Bases) :
    ∃ (A : ℝ) (p : ℕ), 0 ≤ A ∧ ∀ (h : H) (v : cartanRootIdeal H),
      ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun
        (cartanIdealResidualAutomorphism T H h v)‖ ≤
      A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p *
        ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun v‖ := by
  obtain ⟨C, p, hC, hletters⟩ := M.exists_residual_letters_bound T
  let b := WordBasisSelections.basis M.letter M.wordList β
  obtain ⟨K, hK, hbracket⟩ := exists_basis_structureConstant_bound b
  let d := finrank ℝ (cartanRootIdeal H)
  let Q := 1 + (d : ℝ) ^ 2 * K
  refine ⟨(d : ℝ) * Q ^ M.wordDegreeBound * (1 + C) ^ M.wordDegreeBound,
    p * M.wordDegreeBound, by dsimp [Q]; positivity, ?_⟩
  intro h v
  let q := 1 + ‖(Module.finBasis ℝ H).equivFun h‖
  have hq : 1 ≤ q := le_add_of_nonneg_right (norm_nonneg _)
  have hqp : 1 ≤ q ^ p := one_le_pow₀ hq
  have hb := M.norm_wordBasis_lieMap_le β b
    (cartanIdealResidualAutomorphism T H h).toLieHom hK
    (by positivity : 0 ≤ C * q ^ p) hbracket (hletters β h) v
  apply hb.trans
  have hs : 1 + C * q ^ p ≤ (1 + C) * q ^ p := by nlinarith
  calc
    _ ≤ (d : ℝ) * Q ^ M.wordDegreeBound * ((1 + C) * q ^ p) ^ M.wordDegreeBound *
        ‖b.equivFun v‖ := by
      dsimp only [Q, d]
      gcongr
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-- The induced residual action on every cone quotient has polynomial
coordinate growth in the Cartan parameter. -/
theorem exists_cone_residual_coordinate_bound
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    {J : Type*} [Fintype J]
    (b : Basis J ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal C)) :
    ∃ (A : ℝ) (p : ℕ), 0 ≤ A ∧ ∀ (h : H) (v : (cartanRootIdeal H) ⧸ M.coneWordIdeal C),
      ‖b.equivFun ((M.coneWordIdeal C).toSubmodule.mapQ (M.coneWordIdeal C).toSubmodule
        (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap
        (M.coneWordIdeal_residual_mem T C hadd h) v)‖ ≤
      A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p * ‖b.equivFun v‖ := by
  let β : M.Bases := Classical.choice inferInstance
  let a := WordBasisSelections.basis M.letter M.wordList β
  obtain ⟨A, p, hA, hbound⟩ := M.exists_residual_coordinate_bound T β
  obtain ⟨K, hK, hquot⟩ := exists_quotient_coordinate_bound a (M.coneWordIdeal C).toSubmodule b
  refine ⟨K * A, p, mul_nonneg hK hA, ?_⟩
  intro h v
  simpa only [mul_assoc] using hquot
    (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap
    (M.coneWordIdeal_residual_mem T C hadd h)
    (A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p) (by positivity) (hbound h) v

end CartanWordModel
end PolycyclicRecognition

end

end OAI
