import Mathlib
import OAI.Analysis.Commutator.TensorDevelopment

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

namespace Kadison.HilbertTensor

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

lemma inner_map_left_symmetric (a : E →L[ℂ] E)
    (ha : ∀ x y, inner ℂ (a x) y = inner ℂ x (a y))
    (x y : Completion (E ⊗[ℂ] F)) :
    inner ℂ (map a (1 : F →L[ℂ] F) x) y =
      inner ℂ x (map a (1 : F →L[ℂ] F) y) := by
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x y =>
    induction x using TensorProduct.inductionOn with
    | add x x' hx hx' =>
      simp only [Completion.coe_add, map_add, inner_add_left, hx, hx']
    | tmul x v =>
      induction y using TensorProduct.inductionOn with
      | add y y' hy hy' =>
        simp only [Completion.coe_add, map_add, inner_add_right, hy, hy']
      | tmul y w =>
        simp only [map_coe_tmul, one_apply_eq_self, Completion.inner_coe,
          TensorProduct.inner_tmul, ha]

lemma endpoint_projection_bound
    (Y : Completion (E ⊗[ℂ] F) →L[ℂ] Completion (E ⊗[ℂ] G))
    (p : E →L[ℂ] E)
    (hp : ∀ x y, inner ℂ (p x) y = inner ℂ x (p y))
    (hY : Y.comp (map p (1 : F →L[ℂ] F)) =
      (map p (1 : G →L[ℂ] G)).comp Y)
    (Ω a : E) (ha : p a = a) (x : F) (z : G) :
    ‖inner ℂ ((a ⊗ₜ[ℂ] z : E ⊗[ℂ] G) : Completion _)
      (Y ((Ω ⊗ₜ[ℂ] x : E ⊗[ℂ] F) : Completion _))‖ ≤
      ‖Y‖ * ‖a‖ * ‖p Ω‖ * ‖x‖ * ‖z‖ := by
  have htest : map p (1 : G →L[ℂ] G)
      ((a ⊗ₜ[ℂ] z : E ⊗[ℂ] G) : Completion _) =
      ((a ⊗ₜ[ℂ] z : E ⊗[ℂ] G) : Completion _) := by
    simp [ha]
  have heq : inner ℂ ((a ⊗ₜ[ℂ] z : E ⊗[ℂ] G) : Completion _)
      (Y ((Ω ⊗ₜ[ℂ] x : E ⊗[ℂ] F) : Completion _)) =
      inner ℂ ((a ⊗ₜ[ℂ] z : E ⊗[ℂ] G) : Completion _)
      (Y ((p Ω ⊗ₜ[ℂ] x : E ⊗[ℂ] F) : Completion _)) := by
    conv_lhs => rw [← htest]
    rw [inner_map_left_symmetric p hp, ← ContinuousLinearMap.comp_apply,
      ← hY, ContinuousLinearMap.comp_apply, map_coe_tmul, one_apply_eq_self]
  rw [heq]
  calc
    _ ≤ ‖((a ⊗ₜ[ℂ] z : E ⊗[ℂ] G) : Completion _)‖ *
        ‖Y ((p Ω ⊗ₜ[ℂ] x : E ⊗[ℂ] F) : Completion _)‖ := norm_inner_le_norm _ _
    _ ≤ (‖a‖ * ‖z‖) * (‖Y‖ * (‖p Ω‖ * ‖x‖)) := by
      simp only [Completion.norm_coe, TensorProduct.norm_tmul]
      gcongr
      simpa only [Completion.norm_coe, TensorProduct.norm_tmul] using
        (Y.le_opNorm ((p Ω ⊗ₜ[ℂ] x : E ⊗[ℂ] F) : Completion _))
    _ = _ := by ring

end Kadison.HilbertTensor
end

end OAI
