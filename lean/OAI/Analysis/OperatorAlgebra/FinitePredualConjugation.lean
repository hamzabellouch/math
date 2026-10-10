import OAI.Analysis.OperatorAlgebra.FiniteOperatorPredual
import OAI.Analysis.PureInfiniteness.TwoMatrixNuclear

namespace OAI

/-! Unitary conjugation preserves the finite operator predual, contractively,
and carries a vector functional to the functional of the transformed vectors. -/

noncomputable section
open scoped InnerProductSpace

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def conjugatedOperator (U : H ≃ₗᵢ[ℂ] H) : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  starHomContinuousLinear U.symm.conjStarAlgEquiv.toStarAlgHom.toNonUnitalStarAlgHom

@[simp] lemma conjugatedOperator_apply (U : H ≃ₗᵢ[ℂ] H) (T : H →L[ℂ] H) (x : H) :
    conjugatedOperator U T x = U.symm (T (U x)) := rfl

def predualUnitaryAmbient (U : H ≃ₗᵢ[ℂ] H) :
    StrongDual ℂ (H →L[ℂ] H) →L[ℂ] StrongDual ℂ (H →L[ℂ] H) :=
  ({ toFun := fun ψ => ψ.comp (conjugatedOperator U)
     map_add' := by intros; ext T; rfl
     map_smul' := by intros; ext T; rfl } :
     StrongDual ℂ (H →L[ℂ] H) →ₗ[ℂ] StrongDual ℂ (H →L[ℂ] H)).mkContinuous 1
    (fun ψ => by
      change ‖ψ.comp (conjugatedOperator U)‖ ≤ 1 * ‖ψ‖
      simpa only [one_mul, conjugatedOperator] using (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul_of_nonneg_left (starHomContinuousLinear_norm_le_one _) (norm_nonneg ψ)).trans_eq
          (mul_one ‖ψ‖)))

lemma predualUnitaryAmbient_coefficient (U : H ≃ₗᵢ[ℂ] H) (x y : H) :
    predualUnitaryAmbient U (operatorCoefficient x y) = operatorCoefficient (U x) (U y) := by
  ext T
  change inner ℂ x (U.symm (T (U y))) = inner ℂ (U x) (T (U y))
  rw [← U.inner_map_map x (U.symm (T (U y))), U.apply_symm_apply]

lemma predualUnitaryAmbient_mem (U : H ≃ₗᵢ[ℂ] H)
    {ψ : StrongDual ℂ (H →L[ℂ] H)} (hψ : ψ ∈ finiteOperatorPredual (H := H)) :
    predualUnitaryAmbient U ψ ∈ finiteOperatorPredual (H := H) := by
  induction hψ using Submodule.span_induction with
  | mem ψ hψ =>
    obtain ⟨⟨x, y⟩, rfl⟩ := hψ
    rw [predualUnitaryAmbient_coefficient]
    exact (finiteOperatorCoefficient (U x) (U y)).property
  | zero => simpa only [map_zero] using (finiteOperatorPredual (H := H)).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (finiteOperatorPredual (H := H)).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [map_smul, RingHom.id_apply] using (finiteOperatorPredual (H := H)).smul_mem c ih

def finitePredualUnitary (U : H ≃ₗᵢ[ℂ] H) :
    finiteOperatorPredual (H := H) →L[ℂ] finiteOperatorPredual (H := H) :=
  ((predualUnitaryAmbient U).comp (finiteOperatorPredual (H := H)).subtypeL).codRestrict _
    (fun ψ => predualUnitaryAmbient_mem U ψ.property)

@[simp] lemma finitePredualUnitary_apply (U : H ≃ₗᵢ[ℂ] H)
    (ψ : finiteOperatorPredual (H := H)) (T : H →L[ℂ] H) :
    (finitePredualUnitary U ψ).val T = ψ.val (conjugatedOperator U T) := rfl

@[simp] lemma finitePredualUnitary_coefficient (U : H ≃ₗᵢ[ℂ] H) (x y : H) :
    finitePredualUnitary U (finiteOperatorCoefficient x y) = finiteOperatorCoefficient (U x) (U y) := by
  apply Subtype.ext
  exact predualUnitaryAmbient_coefficient U x y

end WeakPureInfiniteness

end

end OAI
