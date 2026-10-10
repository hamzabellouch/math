import OAI.NumberTheory.Ostmann.Characters.AdditiveFourier

namespace OAI

/-!
# Removing the constant Fourier mode

Centering a finite-field function removes exactly its zero frequency.
The energy splits into the centered energy and the squared mean.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def fieldMean {p : ℕ} [NeZero p] (F : ZMod p → ℂ) : ℂ :=
  additiveFourier F 0

noncomputable def fieldCentered {p : ℕ} [NeZero p] (F : ZMod p → ℂ) (x : ZMod p) : ℂ :=
  F x - fieldMean F

theorem fieldCentered_fourier {p : ℕ} [NeZero p]
    (F : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fieldCentered F) a =
      additiveFourier F a - if a = 0 then fieldMean F else 0 := by
  unfold fieldCentered
  rw [additiveFourier_sub, additiveFourier_const]

theorem fieldCentered_fourier_zero {p : ℕ} [NeZero p] (F : ZMod p → ℂ) :
    additiveFourier (fieldCentered F) 0 = 0 := by
  simp only [fieldCentered_fourier, fieldMean, ite_true, sub_self]

theorem fieldCentered_energy_identity {p : ℕ} [NeZero p] (F : ZMod p → ℂ) :
    (∑ x : ZMod p, ‖F x‖ ^ 2) =
      (∑ x : ZMod p, ‖fieldCentered F x‖ ^ 2) + (p : ℝ) * ‖fieldMean F‖ ^ 2 := by
  classical
  have hterm (a : ZMod p) : ‖additiveFourier F a‖ ^ 2 =
      ‖additiveFourier (fieldCentered F) a‖ ^ 2 +
        if a = 0 then ‖fieldMean F‖ ^ 2 else 0 := by
    by_cases ha : a = 0
    · subst a
      simp [fieldCentered_fourier_zero, fieldMean]
    · simp only [fieldCentered_fourier, ha, ite_false, sub_zero, add_zero]
  calc
    _ = (p : ℝ) * ∑ a : ZMod p, ‖additiveFourier F a‖ ^ 2 := additiveFourier_energy F
    _ = (p : ℝ) * ((∑ a : ZMod p, ‖additiveFourier (fieldCentered F) a‖ ^ 2) +
        ‖fieldMean F‖ ^ 2) := by
      simp_rw [hterm]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    _ = _ := by rw [additiveFourier_energy (fieldCentered F)]; ring

theorem fieldCentered_energy_le {p : ℕ} [NeZero p] (F : ZMod p → ℂ) :
    (∑ x : ZMod p, ‖fieldCentered F x‖ ^ 2) ≤ ∑ x : ZMod p, ‖F x‖ ^ 2 := by
  rw [fieldCentered_energy_identity F]
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg p) (sq_nonneg _))

end Ostmann

end OAI
