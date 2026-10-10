import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConjugationFlow

namespace OAI

/-! # Algebra exponentials as actual group elements

The unit-valued exponential keeps the inverse explicit. This bridges the
operator conjugation identity to a faithful group representation.
-/

noncomputable section

namespace PolycyclicRecognition

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def algebraExpUnit (x : A) : Aˣ := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  exact
    { val := NormedSpace.exp x
      inv := NormedSpace.exp (-x)
      val_inv := by
        rw [← NormedSpace.exp_add_of_commute (Commute.refl x).neg_right,
          add_neg_cancel, NormedSpace.exp_zero]
      inv_val := by
        rw [← NormedSpace.exp_add_of_commute (Commute.refl x).neg_left,
          neg_add_cancel, NormedSpace.exp_zero] }

@[simp] theorem coe_algebraExpUnit (x : A) :
    (algebraExpUnit x : A) = NormedSpace.exp x := rfl

@[simp] theorem algebraExpUnit_neg (x : A) :
    algebraExpUnit (-x) = (algebraExpUnit x)⁻¹ := by
  apply Units.ext
  rfl

@[simp] theorem algebraExpUnit_zero : algebraExpUnit (0 : A) = 1 := by
  apply Units.ext
  exact NormedSpace.exp_zero

theorem algebraExpUnit_add_of_commute {x y : A} (hxy : Commute x y) :
    algebraExpUnit (x + y) = algebraExpUnit x * algebraExpUnit y := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  apply Units.ext
  exact NormedSpace.exp_add_of_commute hxy

theorem algebraExpUnit_conj (u : Aˣ) (x : A) :
    algebraExpUnit (u * x * (u⁻¹ : Aˣ) : A) = u * algebraExpUnit x * u⁻¹ := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  apply Units.ext
  exact NormedSpace.exp_units_conj u x

theorem algebraExpUnit_continuous : Continuous (algebraExpUnit : A → Aˣ) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  apply Units.continuous_iff.mpr
  exact ⟨NormedSpace.exp_continuous, NormedSpace.exp_continuous.comp continuous_neg⟩

end PolycyclicRecognition

end

end OAI
