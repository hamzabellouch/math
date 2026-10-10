import Mathlib
import OAI.Analysis.Commutator.HilbertTensors
import OAI.Analysis.Commutator.TensorCompletion

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

namespace Kadison.HilbertCompletion

open UniformSpace

open scoped TensorProduct

variable (E F : PreHilbert)

def powerEquiv (U : Completion E ≃ₗᵢ[ℂ] Completion F) : ∀ n,
    Completion (PreHilbert.power E n) ≃ₗᵢ[ℂ] Completion (PreHilbert.power F n)
  | 0 => .refl ℂ _
  | n+1 => (tensor (E := E) (F := PreHilbert.power E n)).trans
      ((congr (TensorProduct.congrIsometry U (powerEquiv U n))).trans
        (tensor (E := F) (F := PreHilbert.power F n)).symm)

lemma powerEquiv_pure (U : Completion E ≃ₗᵢ[ℂ] Completion F)
    (n : ℕ) (v : Fin n → E) (w : Fin n → F)
    (h : ∀ i, U (v i : Completion E)=(w i : Completion F)) :
    powerEquiv E F U n (PreHilbert.pure E n v : Completion (PreHilbert.power E n)) =
      (PreHilbert.pure F n w : Completion (PreHilbert.power F n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (tensor (E := F) (F := PreHilbert.power F n)).symm
      (congr (TensorProduct.congrIsometry U (powerEquiv E F U n))
        (tensor (E := E) (F := PreHilbert.power E n)
          ((v 0 ⊗ₜ[ℂ] PreHilbert.pure E n (Fin.tail v)) :
            Completion (E ⊗[ℂ] PreHilbert.power E n)))) = _
    apply (tensor (E := F) (F := PreHilbert.power F n)).injective
    rw [LinearIsometryEquiv.apply_symm_apply, tensor_coe_tmul, congr_coe,
      TensorProduct.congrIsometry_apply, TensorProduct.congr_tmul]
    change ((U (v 0 : Completion E) ⊗ₜ[ℂ]
      powerEquiv E F U n (PreHilbert.pure E n (Fin.tail v) : Completion (PreHilbert.power E n))) :
      Completion (Completion F ⊗[ℂ] Completion (PreHilbert.power F n))) = _
    rw [h 0, ih (Fin.tail v) (Fin.tail w) (fun i => h i.succ)]
    exact (tensor_coe_tmul (w 0) (PreHilbert.pure F n (Fin.tail w))).symm

variable (E' F' : PreHilbert)

def wordEquiv (U : Completion E ≃ₗᵢ[ℂ] Completion E')
    (V : Completion F ≃ₗᵢ[ℂ] Completion F') (n : ℕ) :
    Completion (E ⊗[ℂ] PreHilbert.power F n) ≃ₗᵢ[ℂ]
      Completion (E' ⊗[ℂ] PreHilbert.power F' n) :=
  (tensor (E := E) (F := PreHilbert.power F n)).trans
    ((congr (TensorProduct.congrIsometry U (powerEquiv F F' V n))).trans
      (tensor (E := E') (F := PreHilbert.power F' n)).symm)

lemma wordEquiv_pure (U : Completion E ≃ₗᵢ[ℂ] Completion E')
    (V : Completion F ≃ₗᵢ[ℂ] Completion F') (n : ℕ)
    (a : E) (a' : E') (ha : U (a : Completion E)=(a' : Completion E'))
    (v : Fin n → F) (w : Fin n → F')
    (hv : ∀ i, V (v i : Completion F)=(w i : Completion F')) :
    wordEquiv E F E' F' U V n
      ((a ⊗ₜ[ℂ] PreHilbert.pure F n v) : Completion (E ⊗[ℂ] PreHilbert.power F n)) =
        ((a' ⊗ₜ[ℂ] PreHilbert.pure F' n w) : Completion (E' ⊗[ℂ] PreHilbert.power F' n)) := by
  change (tensor (E := E') (F := PreHilbert.power F' n)).symm
    (congr (TensorProduct.congrIsometry U (powerEquiv F F' V n))
      (tensor (E := E) (F := PreHilbert.power F n)
        ((a ⊗ₜ[ℂ] PreHilbert.pure F n v) : Completion (E ⊗[ℂ] PreHilbert.power F n)))) = _
  apply (tensor (E := E') (F := PreHilbert.power F' n)).injective
  rw [LinearIsometryEquiv.apply_symm_apply, tensor_coe_tmul, congr_coe,
    TensorProduct.congrIsometry_apply, TensorProduct.congr_tmul]
  change ((U (a : Completion E) ⊗ₜ[ℂ]
    powerEquiv F F' V n (PreHilbert.pure F n v : Completion (PreHilbert.power F n))) :
    Completion (Completion E' ⊗[ℂ] Completion (PreHilbert.power F' n))) = _
  rw [ha, powerEquiv_pure F F' V n v w hv]
  exact (tensor_coe_tmul a' (PreHilbert.pure F' n w)).symm

end Kadison.HilbertCompletion
end

end OAI
