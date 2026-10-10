import OAI.Analysis.Cotype.CubeFirstChaos

namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem kConvex_iff_coordinate_firstCoefficient_bound :
    KConvex X ↔ ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (f : PiLp 2 (fun _ : Cube n => X)),
      ‖projectionLinearCoefficient (coordinateExpectation (X := X) (n := n)) f‖ ≤ K*‖f‖ := by
  constructor
  · rintro ⟨K,hK,h⟩
    refine ⟨K,hK,fun n f => ?_⟩
    have hb := h n (fun ε => f ε)
    rw [cubeL2_eq_piLp, cubeL2_eq_piLp] at hb
    have hc : 0 < Real.sqrt ((Fintype.card (Cube n) : ℝ)⁻¹) := by
      apply Real.sqrt_pos.mpr
      apply inv_pos.mpr
      exact_mod_cast Fintype.card_pos
    have he := coordinate_firstCoefficient_eq_radProjection (fun ε => f ε)
    have hf : (toLp 2 (fun ε => f ε) : PiLp 2 (fun _ : Cube n => X)) = f := by ext ε; rfl
    rw [hf] at he
    rw [he]
    apply (mul_le_mul_iff_left₀ hc).mp
    simpa only [hf, mul_comm, mul_left_comm, mul_assoc] using hb
  · rintro ⟨K,hK,h⟩
    refine ⟨K,hK,fun n f => ?_⟩
    have hb := h n (probabilityL2Vector f)
    rwa [coordinate_firstCoefficient_probabilityL2_norm, probabilityL2Vector_norm] at hb

end Cotype

end

end OAI
