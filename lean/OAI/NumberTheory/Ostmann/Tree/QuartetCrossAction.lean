import OAI.NumberTheory.Ostmann.Tree.MellinTransform
import OAI.NumberTheory.Ostmann.Tree.QuartetFamilyPullback
import OAI.NumberTheory.Ostmann.Tree.QuartetProductFiber

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.FiniteField
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem mellin_mul_coordinate (f : Fˣ → ℂ) (w : Fˣ) (ρ : MulChar F ℂ) :
    mellin (fun z : Fˣ => f (w*z)) ρ = ρ w*mellin f ρ := by
  simpa only [mul_comm] using mellin_mulRight f w ρ

theorem norm_mellin_mul_coordinate (f : Fˣ → ℂ) (w : Fˣ) (ρ : MulChar F ℂ) :
    ‖mellin (fun z : Fˣ => f (w*z)) ρ‖ = ‖mellin f ρ‖ := by
  rw [mellin_mul_coordinate, norm_mul, mulChar_norm_unit, one_mul]

end Ostmann.FiniteField
namespace Ostmann.Tree.Quartet
variable {F : Type*} [Field F]

theorem scalePair_assignment (a : Bool) (free held z : Fˣ) :
    scalePair (pairAssignment a free held) a z = pairAssignment a (free*z) held := by
  cases a <;> simp [scalePair, pairAssignment, Density.left_join, Density.right_join] <;> rfl

theorem moveCross_assignment (a b : Bool) (m h k w z : Fˣ) :
    moveCross (crossAssignment a b m h k w) a b z = crossAssignment a b m h k (w*z) := by
  simp only [moveCross, crossAssignment, Density.left_join, Density.right_join,
    scalePair_assignment]
  have he : m/(w*h*k)*z⁻¹ = m/((w*z)*h*k) := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  rw [he]

namespace NodeInput
open Ostmann.FiniteField
variable {p : ℕ} [Fact p.Prime]

theorem crossAction_coefficient_norm (N : NodeInput (ZMod p) 1)
    (g : ZMod p → ℂ) (a b : Bool) (m h k w : (ZMod p)ˣ)
    (ρ : MulChar (ZMod p) ℂ) :
    ‖mellin (fun z : (ZMod p)ˣ => N.parameters.evaluate g N.D N.Xleft N.Xright 0
      (moveCross (crossAssignment a b m h k w) a b z)) ρ‖ =
      ‖mellin (N.crossFamilyFunction g a b m h k) ρ‖ := by
  simp_rw [moveCross_assignment]
  exact norm_mellin_mul_coordinate (N.crossFamilyFunction g a b m h k) w ρ

end NodeInput
end Ostmann.Tree.Quartet
end

end OAI
