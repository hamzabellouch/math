import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint

namespace WeakPureInfiniteness

universe u v

section ProductRepresentation

variable {ι : Type u} {H : ι → Type v}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, CompleteSpace (H i)]

lemma mem_l2_productAction (T : lp (fun i => H i →L[ℂ] H i) ∞) (ξ : lp H 2) :
    Memℓp (fun i => T i (ξ i)) 2 := by
  apply (ξ.property.const_smul (‖T‖ : ℂ)).mono'
  intro i
  change ‖T i (ξ i)‖ ≤ ‖(‖T‖ : ℂ) • (ξ i)‖
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T)]
  exact (T i).le_opNorm (ξ i) |>.trans
    (mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero T i) (norm_nonneg _))

def productAction (T : lp (fun i => H i →L[ℂ] H i) ∞) : lp H 2 →L[ℂ] lp H 2 :=
  LinearMap.mkContinuous
    { toFun ξ := ⟨fun i => T i (ξ i), mem_l2_productAction T ξ⟩
      map_add' ξ η := by ext i; exact map_add (T i) _ _
      map_smul' c ξ := by ext i; exact map_smul (T i) _ _ }
    ‖T‖ (by
      intro ξ
      calc
        _ ≤ ‖(‖T‖ : ℂ) • ξ‖ := lp.norm_mono (by norm_num) (by
          intro i
          simp only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T)]
          exact ((T i).le_opNorm (ξ i)).trans
            (mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero T i)
              (norm_nonneg _)))
        _ = ‖(‖T‖ : ℂ)‖ * ‖ξ‖ := norm_smul _ _
        _ = ‖T‖ * ‖ξ‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg T)])

@[simp] lemma productAction_apply (T : lp (fun i => H i →L[ℂ] H i) ∞)
    (ξ : lp H 2) (i : ι) : productAction T ξ i = T i (ξ i) := rfl

lemma productAction_star (T : lp (fun i => H i →L[ℂ] H i) ∞) :
    productAction (star T) = star (productAction T) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_left ℂ
  intro η
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  change (∑' i, inner ℂ (η i) (star (T i) (ξ i))) =
    ∑' i, inner ℂ (T i (η i)) (ξ i)
  apply tsum_congr
  intro i
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

def productRepresentation : lp (fun i => H i →L[ℂ] H i) ∞ →⋆ₙₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) where
  toFun := productAction
  map_zero' := by ext ξ i; simp
  map_add' S T := by ext ξ i; rfl
  map_mul' S T := by ext ξ i; rfl
  map_smul' c T := by ext ξ i; rfl
  map_star' := productAction_star

lemma productRepresentation_injective : Function.Injective (productRepresentation (H := H)) := by
  classical
  intro S T h
  apply Subtype.ext
  funext i
  apply ContinuousLinearMap.ext
  intro ξ
  have he := congrArg (fun F : lp H 2 →L[ℂ] lp H 2 => F (lp.single 2 i ξ) i) h
  change (productAction S (lp.single 2 i ξ)) i = (productAction T (lp.single 2 i ξ)) i at he
  simpa only [productAction_apply, lp.single_apply_self] using he

end ProductRepresentation

end WeakPureInfiniteness
end

end OAI
