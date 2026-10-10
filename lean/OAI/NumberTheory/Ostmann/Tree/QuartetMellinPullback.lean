import OAI.NumberTheory.Ostmann.Tree.MellinSquare

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance : Fintype (MulChar F ℂ) := Fintype.ofFinite _

theorem mellin_inverse_coordinate (f : Fˣ → ℂ) (ρ : MulChar F ℂ) :
    mellin (fun z : Fˣ => f z⁻¹) ρ = mellin f ρ⁻¹ := by
  unfold mellin
  congr 1
  have hs := (Equiv.inv Fˣ).bijective.sum_comp (fun z : Fˣ => f z*conj (ρ⁻¹ z))
  change (∑ z : Fˣ, f z⁻¹*conj (ρ⁻¹ (z⁻¹:Fˣ))) = ∑ z : Fˣ, f z*conj (ρ⁻¹ z) at hs
  simpa only [MulChar.inv_apply', Units.val_inv_eq_inv_val, inv_inv] using hs

theorem mellin_inverse_square_pullback (f : Fˣ → ℂ) (K : Fˣ) (ρ : MulChar F ℂ) :
    ‖mellin (fun z : Fˣ => f (K/z^2)) ρ‖^2 ≤
      2*∑ χ : MulChar F ℂ with χ^2=ρ⁻¹, ‖mellin f χ‖^2 := by
  have he : (fun z : Fˣ => f (K/z^2)) = fun z : Fˣ => (fun w : Fˣ => f (K*w^2)) z⁻¹ := by
    funext z
    simp [div_eq_mul_inv, inv_pow]
  rw [he, mellin_inverse_coordinate (fun w : Fˣ => f (K*w^2)) ρ]
  exact mellin_square_pullback f K ρ⁻¹

end
end Ostmann.FiniteField

end OAI
