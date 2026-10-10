import OAI.Analysis.PureInfiniteness.FiniteDensityPowersStormer
import OAI.Analysis.OperatorAlgebra.FinitePredualConjugation

namespace OAI

/-! Finite tensor vectors give actual finite vector functionals. Their norm
controls the distance of their reduced-density square roots, without a
dimension bound on the ambient Hilbert spaces. -/

noncomputable section
open scoped InnerProductSpace TensorProduct ComplexOrder

namespace WeakPureInfiniteness

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def tensorActionOnVector (w : E ⊗[ℂ] H) : (H →L[ℂ] H) →L[ℂ] E ⊗[ℂ] H :=
  ({ toFun := fun T => T.lTensor E w
     map_add' := by intros; simp only [ContinuousLinearMap.lTensor_add, add_apply]
     map_smul' := by intros; simp only [ContinuousLinearMap.lTensor_smul, smul_apply,
       RingHom.id_apply] } : (H →L[ℂ] H) →ₗ[ℂ] E ⊗[ℂ] H).mkContinuous ‖w‖ (fun T => by
      calc
        ‖T.lTensor E w‖ ≤ ‖T.lTensor E‖ * ‖w‖ := (T.lTensor E).le_opNorm w
        _ ≤ ‖T‖ * ‖w‖ := mul_le_mul_of_nonneg_right (T.norm_lTensor_le E) (norm_nonneg w)
        _ = ‖w‖ * ‖T‖ := mul_comm _ _)

def tensorCoefficient (z w : E ⊗[ℂ] H) : StrongDual ℂ (H →L[ℂ] H) :=
  (innerSL ℂ z).comp (tensorActionOnVector w)

omit [CompleteSpace E] [CompleteSpace H] in
lemma tensorCoefficient_apply (z w : E ⊗[ℂ] H) (T : H →L[ℂ] H) :
    tensorCoefficient z w T = inner ℂ z (TensorProduct.mapL (ContinuousLinearMap.id ℂ E) T w) := by
  change inner ℂ z (T.lTensor E w) = _
  rw [ContinuousLinearMap.lTensor_eq_mapL]

omit [CompleteSpace E] [CompleteSpace H] in
lemma tensorCoefficient_mem (z w : E ⊗[ℂ] H) :
    tensorCoefficient z w ∈ finiteOperatorPredual (H := H) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      induction w using TensorProduct.inductionOn with
      | tmul v t =>
          have he : tensorCoefficient (x ⊗ₜ[ℂ] y) (v ⊗ₜ[ℂ] t) =
              inner ℂ x v • operatorCoefficient y t := by
            ext T
            simp only [tensorCoefficient_apply, TensorProduct.mapL_tmul,
              ContinuousLinearMap.id_apply, TensorProduct.inner_tmul, smul_apply,
              smul_eq_mul, operatorCoefficient_apply]
          rw [he]
          exact Submodule.smul_mem _ _ (finiteOperatorCoefficient y t).property
      | add w₁ w₂ h₁ h₂ =>
          have he : tensorCoefficient (x ⊗ₜ[ℂ] y) (w₁ + w₂) =
              tensorCoefficient (x ⊗ₜ[ℂ] y) w₁ + tensorCoefficient (x ⊗ₜ[ℂ] y) w₂ := by
            ext T; simp only [tensorCoefficient_apply, map_add, add_apply,
              inner_add_right (𝕜 := ℂ) (E := E ⊗[ℂ] H)]
          rw [he]; exact Submodule.add_mem _ h₁ h₂
  | add z₁ z₂ h₁ h₂ =>
      have he : tensorCoefficient (z₁ + z₂) w = tensorCoefficient z₁ w + tensorCoefficient z₂ w := by
        ext T; simp only [tensorCoefficient_apply, add_apply,
          inner_add_left (𝕜 := ℂ) (E := E ⊗[ℂ] H)]
      rw [he]; exact Submodule.add_mem _ h₁ h₂

def finiteTensorDensity (z : E ⊗[ℂ] H) : finiteOperatorPredual (H := H) :=
  ⟨tensorCoefficient z z, tensorCoefficient_mem z z⟩

omit [CompleteSpace E] [CompleteSpace H] in
@[simp] lemma finiteTensorDensity_apply (z : E ⊗[ℂ] H) (T : H →L[ℂ] H) :
    (finiteTensorDensity z).val T =
      inner ℂ z (TensorProduct.mapL (ContinuousLinearMap.id ℂ E) T z) :=
  tensorCoefficient_apply z z T

lemma finiteTensorDensity_trace [FiniteDimensional ℂ H] (z : E ⊗[ℂ] H) :
    finiteTensorDensity z = finiteOperatorTraceDensity (NuclearUltrapower.reducedDensity z) := by
  apply Subtype.ext
  ext T
  rw [finiteTensorDensity_apply, finiteOperatorTraceDensity_apply,
    NuclearUltrapower.trace_reducedDensity]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma operatorLift_norm_le (f : F →ₗᵢ[ℂ] H) (T : F →L[ℂ] F) :
    ‖NuclearUltrapower.operatorLift f T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖f (T (f.toContinuousLinearMap.adjoint x))‖ ≤ ‖T‖ * ‖x‖
  calc
    ‖f (T (f.toContinuousLinearMap.adjoint x))‖ = ‖T (f.toContinuousLinearMap.adjoint x)‖ := f.norm_map _
    _ ≤ ‖T‖ * ‖f.toContinuousLinearMap.adjoint x‖ := T.le_opNorm _
    _ ≤ ‖T‖ * (1 * ‖x‖) := mul_le_mul_of_nonneg_left
      ((f.toContinuousLinearMap.adjoint.le_opNorm x).trans
        (mul_le_mul_of_nonneg_right
          ((ContinuousLinearMap.adjoint.norm_map _).trans_le f.norm_toContinuousLinearMap_le)
          (norm_nonneg x))) (norm_nonneg T)
    _ = ‖T‖ * ‖x‖ := by rw [one_mul]

omit [CompleteSpace E] in
lemma finiteTensorDensity_operatorLift (f : F →ₗᵢ[ℂ] H) (z : E ⊗[ℂ] F)
    (T : F →L[ℂ] F) :
    (finiteTensorDensity (TensorProduct.mapIsometry (LinearIsometry.id : E →ₗᵢ[ℂ] E) f z)).val
      (NuclearUltrapower.operatorLift f T) = (finiteTensorDensity z).val T := by
  let g := TensorProduct.mapIsometry (LinearIsometry.id : E →ₗᵢ[ℂ] E) f
  have hf (x : F) : f.toContinuousLinearMap.adjoint (f x) = x :=
    congrArg (fun S : F →L[ℂ] F => S x) f.adjoint_comp_self
  have ht (w : E ⊗[ℂ] F) :
      TensorProduct.mapL (ContinuousLinearMap.id ℂ E) (NuclearUltrapower.operatorLift f T) (g w) =
        g (TensorProduct.mapL (ContinuousLinearMap.id ℂ E) T w) := by
    induction w using TensorProduct.inductionOn with
    | tmul x y =>
        simp only [g, TensorProduct.mapIsometry_apply, TensorProduct.map_tmul,
          TensorProduct.mapL_tmul, ContinuousLinearMap.id_apply]
        change x ⊗ₜ[ℂ] f (T (f.toContinuousLinearMap.adjoint (f y))) = x ⊗ₜ[ℂ] f (T y)
        rw [hf]
    | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  rw [finiteTensorDensity_apply, finiteTensorDensity_apply]
  change inner ℂ (g z) (TensorProduct.mapL _ _ (g z)) = _
  rw [ht, g.inner_map_map]

omit [CompleteSpace E] in
lemma finiteTensorDensity_lift_norm_le (f : F →ₗᵢ[ℂ] H) (z w : E ⊗[ℂ] F) :
    ‖finiteTensorDensity z - finiteTensorDensity w‖ ≤
      ‖finiteTensorDensity (TensorProduct.mapIsometry (LinearIsometry.id : E →ₗᵢ[ℂ] E) f z) -
        finiteTensorDensity (TensorProduct.mapIsometry (LinearIsometry.id : E →ₗᵢ[ℂ] E) f w)‖ := by
  let g := TensorProduct.mapIsometry (LinearIsometry.id : E →ₗᵢ[ℂ] E) f
  let ψ := finiteTensorDensity (g z) - finiteTensorDensity (g w)
  change ‖(finiteTensorDensity z - finiteTensorDensity w).val‖ ≤ ‖ψ.val‖
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro T
  have he : (finiteTensorDensity z - finiteTensorDensity w).val T =
      ψ.val (NuclearUltrapower.operatorLift f T) := by
    change (finiteTensorDensity z).val T - (finiteTensorDensity w).val T =
      (finiteTensorDensity (g z)).val _ - (finiteTensorDensity (g w)).val _
    rw [finiteTensorDensity_operatorLift, finiteTensorDensity_operatorLift]
  rw [he]
  exact (ψ.val.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (operatorLift_norm_le f T) (norm_nonneg _))

/-- The predual norm estimate survives passage to the common finite support
of the two densities. No ambient finite-dimensionality is assumed. -/
theorem densityRoot_predual_bound (z w : E ⊗[ℂ] H) :
    ‖NuclearUltrapower.densityRoot z - NuclearUltrapower.densityRoot w‖ ^ 2 ≤
      ‖finiteTensorDensity z - finiteTensorDensity w‖ := by
  obtain ⟨F, hF, hFzw⟩ := TensorProduct.exists_finite_submodule_right_of_setFinite
    ({z, w} : Set (E ⊗[ℂ] H)) (Set.toFinite _)
  let : FiniteDimensional ℂ F := hF
  obtain ⟨z', hz⟩ := hFzw (by simp : z ∈ ({z, w} : Set (E ⊗[ℂ] H)))
  obtain ⟨w', hw⟩ := hFzw (by simp : w ∈ ({z, w} : Set (E ⊗[ℂ] H)))
  let f := TensorProduct.mapIsometry (LinearIsometry.id : E →ₗᵢ[ℂ] E) F.subtypeₗᵢ
  have hz' : f z' = z := hz
  have hw' : f w' = w := hw
  rw [← hz', ← hw', NuclearUltrapower.densityRoot_mapIsometry,
    NuclearUltrapower.densityRoot_mapIsometry, ← UniformSpace.Completion.coe_sub,
    UniformSpace.Completion.norm_coe, ← NuclearUltrapower.liftOperatorTensor_sub,
    NuclearUltrapower.liftOperatorTensor_norm, NuclearUltrapower.finiteOperatorTensor_sub]
  refine (finite_density_root_predual_bound _ _
    (NuclearUltrapower.reducedDensity_nonneg z') (NuclearUltrapower.reducedDensity_nonneg w')).trans ?_
  have ht : finiteOperatorTraceDensity
      (NuclearUltrapower.reducedDensity z' - NuclearUltrapower.reducedDensity w') =
      finiteTensorDensity z' - finiteTensorDensity w' := by
    apply Subtype.ext
    ext T
    rw [finiteOperatorTraceDensity_apply]
    change LinearMap.trace ℂ F ((T * (NuclearUltrapower.reducedDensity z' -
      NuclearUltrapower.reducedDensity w')).toLinearMap) =
        (finiteTensorDensity z').val T - (finiteTensorDensity w').val T
    rw [mul_sub, ContinuousLinearMap.toLinearMap_sub, map_sub,
      ← finiteOperatorTraceDensity_apply, ← finiteOperatorTraceDensity_apply,
      ← finiteTensorDensity_trace, ← finiteTensorDensity_trace]
  rw [ht]
  exact finiteTensorDensity_lift_norm_le F.subtypeₗᵢ z' w'

omit [CompleteSpace E] in
lemma finiteTensorDensity_unitary (U : H ≃ₗᵢ[ℂ] H) (z : E ⊗[ℂ] H) :
    finiteTensorDensity (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ E) U z) =
      finitePredualUnitary U (finiteTensorDensity z) := by
  apply Subtype.ext
  ext T
  have ht : NuclearUltrapower.operatorLift U.toLinearIsometry (conjugatedOperator U T) = T := by
    unfold NuclearUltrapower.operatorLift
    change (U : H →L[ℂ] H) ∘L conjugatedOperator U T ∘L
      ContinuousLinearMap.adjoint (U : H →L[ℂ] H) = T
    rw [U.adjoint_eq_symm]
    ext x
    change U (U.symm (T (U (U.symm x)))) = T x
    simp only [U.apply_symm_apply]
  change (finiteTensorDensity (TensorProduct.mapIsometry
    (LinearIsometry.id : E →ₗᵢ[ℂ] E) U.toLinearIsometry z)).val T =
      (finiteTensorDensity z).val (conjugatedOperator U T)
  conv_lhs => rw [← ht]
  exact finiteTensorDensity_operatorLift U.toLinearIsometry z (conjugatedOperator U T)

/-- Norm-small conjugation defects of a finite positive functional yield
Hilbert–Schmidt-small conjugation defects of its positive square root. -/
theorem densityRoot_unitary_predual_bound (U : H ≃ₗᵢ[ℂ] H) (z : E ⊗[ℂ] H) :
    ‖NuclearUltrapower.hsConjugation U (NuclearUltrapower.densityRoot z) -
      NuclearUltrapower.densityRoot z‖ ^ 2 ≤
      ‖finitePredualUnitary U (finiteTensorDensity z) - finiteTensorDensity z‖ := by
  rw [← NuclearUltrapower.densityRoot_unitary (LinearIsometryEquiv.refl ℂ E) U z]
  simpa only [finiteTensorDensity_unitary] using densityRoot_predual_bound
    (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ E) U z) z

end WeakPureInfiniteness

end

end OAI
