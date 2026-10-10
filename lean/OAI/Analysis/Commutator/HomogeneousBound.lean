import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison

variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

lemma linear_norm_bound_from_unitball (f : V →ₗ[ℂ] W) (C : ℝ)
    (h : ∀ x : V,‖x‖≤1 → ‖f x‖≤C) (x : V) : ‖f x‖≤C*‖x‖ := by
  by_cases hx : x=0
  · simp [hx]
  have hp : 0<‖x‖ := norm_pos_iff.mpr hx
  let z : ℂ := ((‖x‖⁻¹ : ℝ) : ℂ)
  have hz : ‖z‖=‖x‖⁻¹ := by simp [z]
  have hu : ‖z • x‖≤1 := by
    rw [norm_smul,hz,inv_mul_cancel₀ hp.ne']
  have hb : ‖x‖⁻¹*‖f x‖≤C := by
    simpa only [map_smul,norm_smul,hz] using h (z • x) hu
  have hb' := (inv_mul_le_iff₀ hp).mp hb
  simpa only [mul_comm] using hb'

section Algebra

variable {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] [Star A] [Star B]

def representedCommutator (ρ : A →⋆ₐ[ℂ] B) (Y : B) : A →ₗ[ℂ] B where
  toFun x := Y*ρ x-ρ x*Y
  map_add' x y := by
    simp only [map_add,mul_add,add_mul]
    abel
  map_smul' z x := by
    simp only [map_smul,mul_smul_comm,smul_mul_assoc,smul_sub,RingHom.id_apply]

end Algebra

end Kadison

end

end
end

end OAI
