import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnitarySubspaceAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralCocycleAverage

namespace OAI

/-! # Concrete cocycles for bundled unitary representations

The bundled form lets central restriction and quotient descent use their
actual representations without changing ambient scalar-action instances.
-/

noncomputable section

namespace PolycyclicRecognition

variable {G E F : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def IsUnitaryCocycle (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (b : G → E) : Prop :=
  ∀ g h, b (g * h) = b g + ρ g (b h)

@[instance_reducible]
def unitaryDistribMulAction (ρ : G →* (E ≃ₗᵢ[ℝ] E)) : DistribMulAction G E where
  smul g x := ρ g x
  one_smul x := by change ρ 1 x = x; rw [map_one]; rfl
  mul_smul g h x := by change ρ (g * h) x = ρ g (ρ h x); rw [map_mul]; rfl
  smul_zero g := map_zero (ρ g)
  smul_add g := map_add (ρ g)

theorem IsUnitaryCocycle.map {ρ : G →* (E ≃ₗᵢ[ℝ] E)} {σ : G →* (F ≃ₗᵢ[ℝ] F)}
    {b : G → E} (hb : IsUnitaryCocycle ρ b) (T : E →L[ℝ] F)
    (hT : ∀ g x, T (ρ g x) = σ g (T x)) : IsUnitaryCocycle σ (T ∘ b) := by
  intro g h
  change T (b (g * h)) = T (b g) + σ g (T (b h))
  rw [hb g h, map_add, hT]

theorem IsUnitaryCocycle.map_one {ρ : G →* (E ≃ₗᵢ[ℝ] E)}
    {b : G → E} (hb : IsUnitaryCocycle ρ b) : b 1 = 0 := by
  have h := hb 1 1
  rw [one_mul, ρ.map_one] at h
  change b 1 = b 1 + b 1 at h
  apply add_left_cancel (a := b 1)
  simpa only [add_zero] using h.symm

theorem IsUnitaryCocycle.central_value_fixed {ρ : G →* (E ≃ₗᵢ[ℝ] E)}
    {b : G → E} (hb : IsUnitaryCocycle ρ b)
    (hz : ∀ z : Subgroup.center G, ρ z = 1)
    (z : Subgroup.center G) (g : G) : ρ g (b z) = b z := by
  have he := Subgroup.mem_center_iff.mp z.property g
  have h₁ := hb g z
  have h₂ := hb z g
  rw [he] at h₁
  rw [hz z] at h₂
  change b ((z : G) * g) = b z + b g at h₂
  have ht : b g + ρ g (b z) = b z + b g := h₁.symm.trans h₂
  rw [add_comm (b z)] at ht
  exact add_left_cancel ht

end PolycyclicRecognition

end

end OAI
