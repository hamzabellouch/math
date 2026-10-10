import Mathlib
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus
import OAI.Geometry.PrescribedPotential.GlobalExtension
import OAI.Geometry.PrescribedPotential.KaehlerClosedDerivatives

namespace OAI

/-! Bounded Bilinear Completion. -/

section

 

noncomputable section
namespace BoundedBilinearCompletion
variable {V H : Type*} [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  (e : V →ₗ[ℝ] H) (he : DenseRange e) (B : V →ₗ[ℝ] V →ₗ[ℝ] V)
  {C : ℝ} (hC : 0 ≤ C) (hB : ∀ u v, ‖e (B u v)‖ ≤ C*(‖e u‖*‖e v‖))

def right (u : V) : H →L[ℝ] H := (e.comp (B u)).extendOfNorm e

include he hB in
lemma right_eq (u v : V) : right e B u (e v) = e (B u v) :=
  LinearMap.extendOfNorm_eq he ⟨C*‖e u‖, fun v => by simpa only [mul_assoc, LinearMap.comp_apply] using hB u v⟩ v

include he hC hB in
lemma right_bound (u : V) : ‖right e B u‖ ≤ C*‖e u‖ :=
  LinearMap.opNorm_extendOfNorm_le he (mul_nonneg hC (norm_nonneg _))
    (fun v => by simpa only [mul_assoc, LinearMap.comp_apply] using hB u v)

def rightLinear : V →ₗ[ℝ] (H →L[ℝ] H) where
  toFun := right e B
  map_add' u v := by
    apply DFunLike.coe_injective
    apply he.equalizer (by fun_prop) (by fun_prop)
    funext w
    simp only [Function.comp_apply, add_apply, right_eq e he B hB,
      map_add, LinearMap.add_apply]
  map_smul' c u := by
    apply DFunLike.coe_injective
    apply he.equalizer (by fun_prop) (by fun_prop)
    funext w
    simp only [Function.comp_apply, smul_apply, right_eq e he B hB,
      map_smul, LinearMap.smul_apply, RingHom.id_apply]

def extend : H →L[ℝ] H →L[ℝ] H := (rightLinear e he B hB).extendOfNorm e

include hC in
lemma extend_eq (u v : V) : extend e he B hB (e u) (e v) = e (B u v) := by
  rw [extend, LinearMap.extendOfNorm_eq he ⟨C, fun u => right_bound e he B hC hB u⟩]
  exact right_eq e he B hB u v

include hC in
lemma extend_bound : ‖extend e he B hB‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le he hC (fun u => right_bound e he B hC hB u)
end BoundedBilinearCompletion

end
end

end OAI
