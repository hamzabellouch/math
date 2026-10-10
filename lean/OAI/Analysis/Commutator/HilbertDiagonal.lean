import Mathlib

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap
open scoped InnerProductSpace ENNReal

namespace Kadison.HilbertDiagonal

variable {ι : Type*} (E : ι → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]

def onLp (V : ∀ i, E i →ₗᵢ[ℂ] E i) : lp E 2 →ₗᵢ[ℂ] lp E 2 where
  toFun x := ⟨fun i => V i (x i), (lp.memℓp x).mono' (fun i => le_of_eq ((V i).norm_map _))⟩
  map_add' _ _ := by ext i; exact (V i).map_add _ _
  map_smul' _ _ := by ext i; exact (V i).map_smul _ _
  norm_map' x := by
    simp only [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
    congr 2
    funext i
    exact congrArg (fun a : ℝ => a ^ (2 : ℝ≥0∞).toReal) ((V i).norm_map (x i))

@[simp] lemma onLp_apply (V : ∀ i, E i →ₗᵢ[ℂ] E i) (x : lp E 2) (i : ι) :
    onLp E V x i=V i (x i) := rfl

@[simp] lemma onLp_single [DecidableEq ι] (V : ∀ i, E i →ₗᵢ[ℂ] E i) (i : ι) (x : E i) :
    onLp E V (lp.single 2 i x)=lp.single 2 i (V i x) := by
  ext j
  by_cases hji : j=i
  · subst j
    simp only [onLp_apply,lp.single_apply,Pi.single_eq_same]
  · simp only [onLp_apply,lp.single_apply,Pi.single_eq_of_ne hji,map_zero]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : ∀ i, E i →ₗᵢ[ℂ] H) (hU : IsHilbertSum ℂ E U)

def onSum (V : ∀ i, E i →ₗᵢ[ℂ] E i) : H →ₗᵢ[ℂ] H :=
  hU.linearIsometryEquiv.symm.toLinearIsometry.comp
    ((onLp E V).comp hU.linearIsometryEquiv.toLinearIsometry)

@[simp] lemma onSum_insert (V : ∀ i, E i →ₗᵢ[ℂ] E i) (i : ι) (x : E i) :
    onSum E U hU V (U i x)=U i (V i x) := by
  classical
  have he : hU.linearIsometryEquiv (U i x)=lp.single 2 i x := by
    rw [←hU.linearIsometryEquiv_symm_apply_single x,LinearIsometryEquiv.apply_symm_apply]
  change hU.linearIsometryEquiv.symm (onLp E V (hU.linearIsometryEquiv (U i x))) = _
  rw [he,onLp_single,hU.linearIsometryEquiv_symm_apply_single]

lemma onSum_comp (V : ∀ i, E i →ₗᵢ[ℂ] E i) (i : ι) :
    (onSum E U hU V).toContinuousLinearMap.comp (U i).toContinuousLinearMap =
      (U i).toContinuousLinearMap.comp (V i).toContinuousLinearMap := by
  ext x
  exact onSum_insert E U hU V i x

lemma onSum_one : onSum E U hU (fun _ => LinearIsometry.id)=LinearIsometry.id := by
  ext x
  change hU.linearIsometryEquiv.symm (onLp E (fun _ => LinearIsometry.id)
    (hU.linearIsometryEquiv x))=x
  have he : onLp E (fun _ => LinearIsometry.id) (hU.linearIsometryEquiv x)=hU.linearIsometryEquiv x := by
    ext i
    rfl
  rw [he,LinearIsometryEquiv.symm_apply_apply]

lemma onSum_mul (V W : ∀ i, E i →ₗᵢ[ℂ] E i) :
    (onSum E U hU V).comp (onSum E U hU W)=
      onSum E U hU (fun i => (V i).comp (W i)) := by
  ext x
  change hU.linearIsometryEquiv.symm (onLp E V (hU.linearIsometryEquiv
    (hU.linearIsometryEquiv.symm (onLp E W (hU.linearIsometryEquiv x))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply congrArg hU.linearIsometryEquiv.symm
  ext i
  rfl

end Kadison.HilbertDiagonal
end

end OAI
