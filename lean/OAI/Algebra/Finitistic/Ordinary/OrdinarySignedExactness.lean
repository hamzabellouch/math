import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorExactness

namespace OAI
noncomputable section
namespace LittleFinitistic
universe u
variable {R E F G : Type u} [Ring R]
variable [AddCommGroup E] [Module R E]
variable [AddCommGroup F] [Module R F]
variable [AddCommGroup G] [Module R G]

/-- Multiplying both differentials by an integer unit preserves exactness. -/
theorem exact_units_smul (u : ℤˣ) (f : E →ₗ[R] F) (g : F →ₗ[R] G)
    (h : Function.Exact f g) : Function.Exact (u • f) (u • g) := by
  intro z
  constructor
  · intro hz
    have hg : g z = 0 := by
      have hh := congrArg (fun x : G => u⁻¹ • x) hz
      simpa only [LinearMap.smul_apply,smul_smul,inv_mul_cancel,one_smul,smul_zero] using hh
    obtain ⟨y,hy⟩ := (h z).mp hg
    refine ⟨u⁻¹ • y, ?_⟩
    change u • f ((↑(u⁻¹) : ℤ) • y) = z
    rw [map_zsmul]
    change u • (u⁻¹ • f y) = z
    rw [smul_smul,mul_inv_cancel,one_smul,hy]
  · rintro ⟨y,rfl⟩
    have hg : g (f y) = 0 := (h (f y)).mpr ⟨y,rfl⟩
    change u • g ((↑u : ℤ) • f y) = 0
    rw [map_zsmul,hg,smul_zero,smul_zero]
end LittleFinitistic

end

end OAI
