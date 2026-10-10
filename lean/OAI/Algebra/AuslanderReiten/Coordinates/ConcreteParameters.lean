import OAI.Algebra.AuslanderReiten.Parameters
import OAI.Algebra.AuslanderReiten.Resolutions.CProjectiveResolution

namespace OAI

noncomputable section
namespace ArExplicit

def parameterUnit (i : Fin 3) : BaseFieldˣ := Units.mk0 (parameter i) (parameter_ne_zero i)

@[simp] theorem parameterUnit_val (i : Fin 3) : (parameterUnit i : BaseField) = parameter i := rfl

theorem q_ne_zero : q ≠ 0 := parameter_ne_zero 0

theorem one_add_q_ne_zero : 1 + q ≠ 0 := by
  simpa only [pow_one, add_comm] using q_pow_add_one_ne_zero 1 (by decide)

theorem q_noPositivePowerOne : Resolution.NoPositivePowerOne q := by
  intro n hn
  simpa only [add_comm] using q_pow_add_one_ne_zero n hn

theorem parameterUnit_twist_ne (n : ℕ) (hn : 0 < n) :
    (((parameterUnit 1)⁻¹ : BaseFieldˣ) : BaseField)^n ≠
      (((parameterUnit 2)⁻¹ : BaseFieldˣ) : BaseField)^n := by
  simpa only [Units.val_inv_eq_inv_val, parameterUnit_val, inv_pow] using twist_eigenvalues_ne n hn

end ArExplicit

end

end OAI
