import OAI.Analysis.BoundedHochschild.UniversalGNSRepresentation

namespace OAI

/-! Restriction to normal vectors gives a faithful normal representation for
the specified predual, without a faithful scalar state assumption. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace
open Classical

namespace BoundedHochschild.KadisonRingrose

open HochschildNormalPart

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def NormalGNS (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) : Type u :=
  normalVectors e (universalGNSRepresentation (M := M))

instance normalGNSNormedAddCommGroup (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    NormedAddCommGroup (NormalGNS e) :=
  inferInstanceAs (NormedAddCommGroup (normalVectors e (universalGNSRepresentation (M := M))))

instance normalGNSInnerProductSpace (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    InnerProductSpace ℂ (NormalGNS e) :=
  inferInstanceAs (InnerProductSpace ℂ (normalVectors e (universalGNSRepresentation (M := M))))

instance normalGNSCompleteSpace (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    CompleteSpace (NormalGNS e) :=
  inferInstanceAs (CompleteSpace (normalVectors e (universalGNSRepresentation (M := M))))

instance normalGNSCoe (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) : CoeOut (NormalGNS e) (UniversalGNS M) :=
  ⟨Subtype.val⟩

def normalGNSOperator (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a : M) :
    NormalGNS e →L[ℂ] NormalGNS e :=
  (universalGNSRepresentation a).restrict
    (fun _ξ hξ => normalVectors_mul e universalGNSRepresentation hξ a)

@[simp] lemma normalGNSOperator_coe (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (a : M) (ξ : NormalGNS e) :
    (normalGNSOperator e a ξ : UniversalGNS M) = universalGNSRepresentation a ξ := rfl

lemma normalGNSOperator_zero (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    normalGNSOperator e 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Subtype.ext
  change universalGNSRepresentation (M := M) (0 : M) (ξ : UniversalGNS M) = 0
  simp

lemma normalGNSOperator_one (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    normalGNSOperator e 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Subtype.ext
  change universalGNSRepresentation (M := M) (1 : M) (ξ : UniversalGNS M) = (ξ : UniversalGNS M)
  simp

lemma normalGNSOperator_add (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a b : M) :
    normalGNSOperator e (a + b) = normalGNSOperator e a + normalGNSOperator e b := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Subtype.ext
  change universalGNSRepresentation (M := M) (a + b) (ξ : UniversalGNS M) =
    universalGNSRepresentation a (ξ : UniversalGNS M) + universalGNSRepresentation b (ξ : UniversalGNS M)
  simp

lemma normalGNSOperator_mul (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a b : M) :
    normalGNSOperator e (a * b) = normalGNSOperator e a * normalGNSOperator e b := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Subtype.ext
  change universalGNSRepresentation (M := M) (a * b) (ξ : UniversalGNS M) =
    universalGNSRepresentation a (universalGNSRepresentation b (ξ : UniversalGNS M))
  rw [map_mul]
  rfl

lemma normalGNSOperator_commutes (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (z : ℂ) :
    normalGNSOperator e (algebraMap ℂ M z) = algebraMap ℂ (NormalGNS e →L[ℂ] NormalGNS e) z := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Subtype.ext
  change universalGNSRepresentation (M := M) (algebraMap ℂ M z) (ξ : UniversalGNS M) = z • (ξ : UniversalGNS M)
  exact congrArg (fun A : UniversalGNS M →L[ℂ] UniversalGNS M => A (ξ : UniversalGNS M))
    ((universalGNSRepresentation (M := M)).commutes z)

lemma normalGNSOperator_star (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a : M) :
    normalGNSOperator e (star a) = star (normalGNSOperator e a) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro ξ η
  change inner ℂ (universalGNSRepresentation (star a) (ξ : UniversalGNS M)) (η : UniversalGNS M) =
    inner ℂ (ξ : UniversalGNS M) (universalGNSRepresentation a (η : UniversalGNS M))
  rw [map_star, ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

def normalGNSRepresentation (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    M →⋆ₐ[ℂ] (NormalGNS e →L[ℂ] NormalGNS e) where
  toFun := normalGNSOperator e
  map_zero' := normalGNSOperator_zero e
  map_one' := normalGNSOperator_one e
  map_add' := normalGNSOperator_add e
  map_mul' := normalGNSOperator_mul e
  commutes' := normalGNSOperator_commutes e
  map_star' := normalGNSOperator_star e

@[simp] lemma normalGNSRepresentation_coe (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (a : M) (ξ : NormalGNS e) :
    (normalGNSRepresentation e a ξ : UniversalGNS M) = universalGNSRepresentation a ξ := rfl

lemma normalGNSRepresentation_coefficients (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (η ξ : NormalGNS e) : coefficient (normalGNSRepresentation e) η ξ ∈ normalDual e := by
  have h := (mem_normalVectors e universalGNSRepresentation ξ).mp ξ.property (η : UniversalGNS M)
  exact h

/-- Every positive cyclic coefficient occurs in the universal representation. -/
lemma universalGNS_positive_coefficient (ψ : M →ₚ[ℂ] ℂ) :
    ∀ a : M, coefficient universalGNSRepresentation
      (lp.single 2 ψ (positiveVector ψ)) (lp.single 2 ψ (positiveVector ψ)) a = ψ a := by
  classical
  intro a
  rw [coefficient_apply, lp.inner_single_left, universalGNSRepresentation_apply,
    lp.single_apply_self]
  exact positiveVector_coefficient ψ a

/-- The normal subrepresentation remains faithful even when there is no
faithful normal scalar state. -/
theorem normalGNSRepresentation_injective (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Function.Injective (normalGNSRepresentation e) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  have hzero (ξ : NormalGNS e) : universalGNSRepresentation a ξ = 0 := by
    have h := congrArg (fun A : NormalGNS e →L[ℂ] NormalGNS e =>
      (A ξ : UniversalGNS M)) ha
    exact h
  have hcoef (η : UniversalGNS M) :
      scalarNormalPart e (coefficient universalGNSRepresentation η η) a = 0 := by
    rw [scalarNormalPart_coefficient, coefficient_apply]
    have hp : normalProjection e universalGNSRepresentation η ∈ normalVectors e universalGNSRepresentation :=
      (normalVectors e universalGNSRepresentation).starProjection_apply_mem η
    rw [hzero ⟨_, hp⟩, inner_zero_right]
  have hnormal (φ : StrongDual ℂ M) (hφ : φ ∈ normalDual e) : φ a = 0 := by
    obtain ⟨ψ, _, hψ⟩ := HochschildPositiveDecomposition.exists_four_positive φ
    let f (i : Fin 4) : StrongDual ℂ M := coefficient universalGNSRepresentation
      (lp.single 2 (ψ i) (positiveVector (ψ i)))
      (lp.single 2 (ψ i) (positiveVector (ψ i)))
    have hf (i : Fin 4) (b : M) : f i b = ψ i b :=
      universalGNS_positive_coefficient (ψ i) b
    have heq : φ = f 0 - f 1 + Complex.I • (f 2 - f 3) := by
      ext b
      simpa only [add_apply, sub_apply, smul_apply, smul_eq_mul, hf] using hψ b
    have hfzero (i : Fin 4) : scalarNormalPart e (f i) a = 0 := hcoef _
    rw [← scalarNormalPart_fixes e hφ, heq, map_add, map_sub, map_smul, map_sub]
    simp only [add_apply, sub_apply, smul_apply, hfzero, smul_zero, sub_self, add_zero]
  apply predual_separates e
  intro z
  simpa only [map_zero] using hnormal (predualEmbedding e z) ⟨z, rfl⟩

theorem normalGNSRepresentation_norm (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a : M) :
    ‖normalGNSRepresentation e a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (normalGNSRepresentation e)
    (normalGNSRepresentation_injective e) a

end BoundedHochschild.KadisonRingrose

end

end OAI
