import OAI.Analysis.BoundedHochschild.NormalOperators
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI

/-! A faithful Hilbert-space realization for the operator-valued averaging
argument. It uses only the already proved separation by positive functionals. -/

noncomputable section

open scoped InnerProductSpace ComplexOrder ENNReal

namespace BoundedHochschild.KadisonRingrose

open HochschildNormalPart

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- The Hilbert sum of the cyclic representations of all positive functionals. -/
abbrev UniversalGNS (M : Type*) [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] :=
  lp (fun ψ : M →ₚ[ℂ] ℂ => ψ.GNS) 2

def universalGNSAction (a : M) (ξ : UniversalGNS M) : UniversalGNS M :=
  ⟨fun ψ => ψ.gnsStarAlgHom a (ξ ψ), by
    apply ((lp.memℓp ξ).norm.const_smul ‖a‖).mono
    intro ψ
    change ‖ψ.gnsStarAlgHom a (ξ ψ)‖ ≤ ‖a‖ * ‖ξ ψ‖
    exact ((ψ.gnsStarAlgHom a).le_opNorm (ξ ψ)).trans
      (mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le ψ.gnsStarAlgHom a)
        (norm_nonneg _))⟩

@[simp] lemma universalGNSAction_apply (a : M) (ξ : UniversalGNS M) (ψ : M →ₚ[ℂ] ℂ) :
    universalGNSAction a ξ ψ = ψ.gnsStarAlgHom a (ξ ψ) := rfl

lemma universalGNSAction_norm (a : M) (ξ : UniversalGNS M) :
    ‖universalGNSAction a ξ‖ ≤ ‖a‖ * ‖ξ‖ := by
  have h : ‖universalGNSAction a ξ‖ ≤ ‖‖a‖ • ξ‖ := by
    apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
    intro ψ
    simp only [universalGNSAction_apply, lp.coeFn_smul, Pi.smul_apply, norm_smul,
      Real.norm_of_nonneg (norm_nonneg a)]
    exact ((ψ.gnsStarAlgHom a).le_opNorm (ξ ψ)).trans
      (mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le ψ.gnsStarAlgHom a)
        (norm_nonneg _))
  simpa only [norm_smul, Real.norm_of_nonneg (norm_nonneg a)] using h

def universalGNSOperator (a : M) : UniversalGNS M →L[ℂ] UniversalGNS M :=
  LinearMap.mkContinuous
    { toFun := universalGNSAction a
      map_add' ξ η := by ext ψ; exact map_add (ψ.gnsStarAlgHom a) (ξ ψ) (η ψ)
      map_smul' z ξ := by ext ψ; exact map_smul (ψ.gnsStarAlgHom a) z (ξ ψ) }
    ‖a‖ (universalGNSAction_norm a)

@[simp] lemma universalGNSOperator_apply (a : M) (ξ : UniversalGNS M) (ψ : M →ₚ[ℂ] ℂ) :
    universalGNSOperator a ξ ψ = ψ.gnsStarAlgHom a (ξ ψ) := rfl

/-- Every C*-algebra acts on the Hilbert sum of its positive cyclic representations. -/
def universalGNSRepresentation : M →⋆ₐ[ℂ] (UniversalGNS M →L[ℂ] UniversalGNS M) where
  toFun := universalGNSOperator
  map_zero' := by ext ξ ψ; simp
  map_one' := by ext ξ ψ; simp
  map_add' a b := by ext ξ ψ; simp
  map_mul' a b := by ext ξ ψ; simp
  commutes' z := by
    ext ξ ψ
    exact congrArg (fun A : ψ.GNS →L[ℂ] ψ.GNS => A (ξ ψ)) (ψ.gnsStarAlgHom.commutes z)
  map_star' a := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro ξ η
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    congr 1
    funext ψ
    simp only [universalGNSOperator_apply, map_star]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _

@[simp] lemma universalGNSRepresentation_apply (a : M) (ξ : UniversalGNS M)
    (ψ : M →ₚ[ℂ] ℂ) :
    universalGNSRepresentation a ξ ψ = ψ.gnsStarAlgHom a (ξ ψ) := rfl

lemma eq_zero_of_all_positive_functionals (a : M)
    (ha : ∀ ψ : M →ₚ[ℂ] ℂ, ψ a = 0) : a = 0 := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro φ
  obtain ⟨ψ, _, hψ⟩ := HochschildPositiveDecomposition.exists_four_positive φ
  rw [hψ a, ha, ha, ha, ha]
  simp

/-- The cyclic representations together separate the original algebra. -/
theorem universalGNSRepresentation_injective :
    Function.Injective (universalGNSRepresentation (M := M)) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  have hzero (ψ : M →ₚ[ℂ] ℂ) (ξ : ψ.GNS) : ψ.gnsStarAlgHom a ξ = 0 := by
    have h := congrArg (fun A : UniversalGNS M →L[ℂ] UniversalGNS M =>
      A (lp.single 2 ψ ξ) ψ) ha
    simpa only [universalGNSRepresentation_apply, lp.single_apply_self,
      zero_apply, lp.coeFn_zero, Pi.zero_apply] using h
  apply (CStarRing.star_mul_self_eq_zero_iff a).mp
  apply eq_zero_of_all_positive_functionals
  intro ψ
  rw [← positiveVector_coefficient ψ (star a * a)]
  simp only [coefficient_apply, map_mul, mul_apply_eq_comp,
    hzero, map_zero, inner_zero_right]

theorem universalGNSRepresentation_norm (a : M) :
    ‖universalGNSRepresentation a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map universalGNSRepresentation universalGNSRepresentation_injective a

end BoundedHochschild.KadisonRingrose

end

end OAI
