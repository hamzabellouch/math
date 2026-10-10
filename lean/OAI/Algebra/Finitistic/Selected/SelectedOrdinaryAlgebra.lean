import OAI.Algebra.Finitistic.Selected.SelectedWindow
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBlockBimodule
import OAI.Algebra.Finitistic.Ordinary.OrdinaryRightProjective
import Mathlib.Algebra.TrivSqZeroExt.Basic

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedOrdinaryAlgebra
open SelectedFixedDiagram QuadraticEncoding
open OrdinarySimulation

/-- A fixed support interval containing degree zero, chosen before any test module. -/
def a : ℤ := min (SelectedWindow.lo-2) 0
def b : ℤ := max SelectedWindow.hi 0
def length : ℕ := (b-a).toNat

theorem a_le_zero : a ≤ 0 := min_le_right _ _
theorem b_nonneg : 0 ≤ b := le_max_right _ _
theorem endpoints : a + (length : ℤ) = b := by
  have ha := a_le_zero
  have hb := b_nonneg
  dsimp [length]
  omega

theorem support (n : ℤ) (hn : n < a ∨ b < n) :
    IsZero (SelectedRectification.bimodule.X n) := by
  apply SelectedWindow.bounded n
  dsimp [a,b] at hn
  omega

instance term_finite (n : ℤ) :
    FiniteDimensional ℂ ((underlyingComplex (k := ℂ) SelectedRectification.bimodule).X n) :=
  SelectedWindow.verified.finite n
instance term_projective (n : ℤ) :
    Module.Projective (B P)ᵐᵒᵖ ((underlyingRightComplex SelectedRectification.bimodule).X n) := by
  let : Projective ((underlyingRightComplex SelectedRectification.bimodule).X n) :=
    SelectedWindow.verified.projective n
  exact ModuleCat.projective_of_module_projective _

/-- The actual finite-dimensional ordinary algebra and off-diagonal bimodule. -/
abbrev D := AlgebraD ℂ length (B P)
abbrev O := BimoduleO SelectedRectification.bimodule a length
abbrev X := BimoduleX SelectedRectification.bimodule a length
instance base_finite : FiniteDimensional ℂ (B P) := QuadraticEncoding.finiteDimensional P
instance D_finite : FiniteDimensional ℂ D := inferInstance
instance O_finite : FiniteDimensional ℂ O := inferInstance
instance X_finite : FiniteDimensional ℂ X := ordinary_finite _ _ _
instance O_right_projective : Module.Projective (B P)ᵐᵒᵖ O :=
  ordinaryO_right_projective _ _ _

/-- The manuscript's one fixed square-zero algebra. No projective-dimension
conclusion is asserted here. -/
abbrev A := TrivSqZeroExt D X
abbrev augmentation : A →ₐ[ℂ] D := TrivSqZeroExt.fstHom ℂ D X

instance A_finite : FiniteDimensional ℂ A :=
  inferInstanceAs (FiniteDimensional ℂ (D × X))
end LittleFinitistic.SelectedOrdinaryAlgebra

end

end OAI
