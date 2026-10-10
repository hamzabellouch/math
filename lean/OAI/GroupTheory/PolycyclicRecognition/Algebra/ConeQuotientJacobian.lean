import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConeInvariance
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanJacobian

namespace OAI

/-! # The Jacobian of the induced Cartan action on a cone quotient -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped BigOperators

/-- A quotient of a unipotent operator is unipotent. This supplies the
determinant-one part of the quotient action without diagonalizability. -/
theorem quotient_unipotent
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : Submodule ℝ V) (F : V →ₗ[ℝ] V) (hF : ∀ x ∈ J, F x ∈ J)
    (hu : _root_.IsNilpotent (F - 1)) :
    _root_.IsNilpotent (J.mapQ J F hF - 1) := by
  have hsub : ∀ x ∈ J, (F - 1) x ∈ J := fun x hx => J.sub_mem (hF x hx) hx
  have he : J.mapQ J F hF - 1 = J.mapQ J (F - 1) hsub := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := J.mkQ_surjective x
    simp
  obtain ⟨k, hk⟩ := hu
  refine ⟨k, ?_⟩
  rw [he, ← J.mapQ_pow hsub]
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := J.mkQ_surjective x
  simp [hk]

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)

theorem coneWordIdeal_dilation_mem (C : Set (H →ₗ[ℝ] ℝ))
    (h : H) (v : cartanRootIdeal H) (hv : v ∈ M.coneWordIdeal C) :
    cartanIdealWeightDilation T H h v ∈ M.coneWordIdeal C := by
  apply map_mixedWordIdeal_mem M.letter
    (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) M.generates
    (cartanIdealWeightDilation T H h).toLieHom (M.coneWordIdeal C) ?_ v hv
  intro i hi
  have he := M.idealWeightDilation_word T h (.of i)
  simp only [evalBracketWord_of, bracketWordExponent_of] at he
  change cartanIdealWeightDilation T H h (M.letter i) ∈ M.coneWordIdeal C
  rw [he]
  exact (M.coneWordIdeal C).smul_mem _
    (eval_mixed_mem_span M.letter (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) (w := .of i) hi)

theorem coneWordIdeal_residual_mem (C : Set (H →ₗ[ℝ] ℝ))
    (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (h : H) (v : cartanRootIdeal H) (hv : v ∈ M.coneWordIdeal C) :
    cartanIdealResidualAutomorphism T H h v ∈ M.coneWordIdeal C := by
  apply map_mixedWordIdeal_mem M.letter
    (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) M.generates
    (cartanIdealResidualAutomorphism T H h).toLieHom (M.coneWordIdeal C) ?_ v hv
  intro i hi
  apply M.outside_genWeightSpace_le_coneWordIdeal C hadd (M.weight i) hi
  let ι : cartanRootIdeal H →ₗ⁅ℝ,H⁆ L := ((cartanRootIdeal H).restr H).incl
  rw [← comap_genWeightSpace_eq_of_injective (f := ι)
    ((cartanRootIdeal H).restr H).injective_incl]
  exact cartanIdealResidualAutomorphism_root_mem T H h (M.weight i) (M.letter i) (M.letter_root i)

/-- The quotient scalar Jacobian is the exponential of the total retained
word weight. -/
theorem det_cone_dilation_word_basis
    (C : Set (H →ₗ[ℝ] ℝ)) (h : H) {J : Type*} [Fintype J]
    (b : Basis J ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (words : J → FreeMagma (Fin M.letterCount))
    (hb : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (evalBracketWord M.letter (words j)) = b j) :
    LinearMap.det ((M.coneWordIdeal C).toSubmodule.mapQ (M.coneWordIdeal C).toSubmodule
      (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap
      (M.coneWordIdeal_dilation_mem T C h)) =
        Real.exp (∑ j, bracketWordExponent (fun i => M.weight i h) (words j)) := by
  classical
  let I := (M.coneWordIdeal C).toSubmodule
  let F := I.mapQ I (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap
    (M.coneWordIdeal_dilation_mem T C h)
  let w := fun j => Real.exp (bracketWordExponent (fun i => M.weight i h) (words j))
  have hF (j) : F (b j) = w j • b j := by
    rw [← hb j]
    change I.mkQ (cartanIdealWeightDilation T H h (evalBracketWord M.letter (words j))) = _
    rw [M.idealWeightDilation_word T h, map_smul]
  have hm : LinearMap.toMatrix b b F = Matrix.diagonal w := by
    ext i j
    simp only [LinearMap.toMatrix_apply, hF, map_smul, Finsupp.smul_apply,
      Basis.repr_self, Finsupp.single_apply, smul_eq_mul, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  rw [← LinearMap.det_toMatrix b, hm, Matrix.det_diagonal, Real.exp_sum]

theorem det_cone_residual_eq_one
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) (h : H) :
    LinearMap.det ((M.coneWordIdeal C).toSubmodule.mapQ (M.coneWordIdeal C).toSubmodule
      (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap
      (M.coneWordIdeal_residual_mem T C hadd h)) = 1 := by
  apply det_eq_one_of_sub_one_nilpotent
  apply quotient_unipotent
  let : Module ℚ (cartanRootIdeal H) := Module.compHom _ (algebraMap ℚ ℝ)
  have hn : _root_.IsNilpotent (cartanIdealResidualDerivation T H h).toLinearMap :=
    ⟨finrank ℝ L, cartanIdealResidualDerivation_pow_eq_zero T H h⟩
  exact hn.isNilpotent_exp_sub_one

/-- The full induced action has Jacobian equal to the exponential of its
actual quotient trace, including all nonsemisimple corrections. -/
theorem det_cone_adjoint_eq_exp_trace
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) (h : H) :
    LinearMap.det ((M.coneWordIdeal C).toSubmodule.mapQ (M.coneWordIdeal C).toSubmodule
      (cartanIdealAdjointAutomorphism T H h).toLinearEquiv.toLinearMap
      (M.coneWordIdeal_adjoint_mem T C hadd h)) =
    Real.exp (LinearMap.trace ℝ ((cartanRootIdeal H) ⧸ M.coneCartanSubmodule C hadd)
      (toEnd ℝ H _ h)) := by
  classical
  let I := (M.coneWordIdeal C).toSubmodule
  have heq : I.mapQ I (cartanIdealAdjointAutomorphism T H h).toLinearEquiv.toLinearMap
      (M.coneWordIdeal_adjoint_mem T C hadd h) =
      (I.mapQ I (cartanIdealWeightDilation T H h).toLinearEquiv.toLinearMap
        (M.coneWordIdeal_dilation_mem T C h)).comp
      (I.mapQ I (cartanIdealResidualAutomorphism T H h).toLinearEquiv.toLinearMap
        (M.coneWordIdeal_residual_mem T C hadd h)) := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := I.mkQ_surjective x
    rfl
  obtain ⟨b, words, _hpure, hb⟩ := exists_pure_quotient_word_basis M.letter
    (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) M.generates
  rw [heq, LinearMap.det_comp, M.det_cone_residual_eq_one T C hadd h, mul_one,
    M.det_cone_dilation_word_basis T C h b words hb]
  apply congrArg Real.exp
  rw [M.trace_cone_word_basis C hadd b words hb h]
  simp only [bracketWordExponent, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The positive integral character computed from pure words is the exact
Jacobian character of the induced Cartan action. -/
theorem exists_positive_cone_jacobian_character
    (C : Set (H →ₗ[ℝ] ℝ)) (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C) :
    ∃ c : Fin M.letterCount → ℕ,
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → c i = 0) ∧
      (∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → 0 < c i) ∧
      ∀ h : H, LinearMap.det
        ((M.coneWordIdeal C).toSubmodule.mapQ (M.coneWordIdeal C).toSubmodule
          (cartanIdealAdjointAutomorphism T H h).toLinearEquiv.toLinearMap
          (M.coneWordIdeal_adjoint_mem T C hadd h)) =
        Real.exp (∑ i, (c i : ℝ) * M.weight i h) := by
  obtain ⟨c, hout, hin, htrace⟩ := M.exists_positive_cone_trace_coefficients C hadd
  refine ⟨c, hout, hin, ?_⟩
  intro h
  rw [M.det_cone_adjoint_eq_exp_trace T C hadd h, htrace]

end CartanWordModel
end PolycyclicRecognition

end

end OAI
