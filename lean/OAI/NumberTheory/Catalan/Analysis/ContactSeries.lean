import Mathlib.RingTheory.PowerSeries.Derivative
import OAI.NumberTheory.Catalan.Polynomial.CentralCoefficients

namespace OAI

noncomputable section

namespace InternalCatalan

open PowerSeries

def centralKernelSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun d => centralCoeffKernel (d : ℤ))

@[simp] theorem coeff_centralKernelSeries (d : ℕ) :
    PowerSeries.coeff d centralKernelSeries = centralCoeffKernel (d : ℤ) :=
  PowerSeries.coeff_mk d _

@[simp] theorem constantCoeff_centralKernelSeries :
    PowerSeries.constantCoeff centralKernelSeries = 1 := by
  simp [centralKernelSeries]

theorem centralCoeffKernel_nat_even (l : ℕ) :
    centralCoeffKernel ((2 * l : ℕ) : ℤ) = centralCoeff l := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using centralCoeffKernel_two_mul l

theorem centralCoeffKernel_nat_odd (l : ℕ) :
    centralCoeffKernel ((2 * l + 1 : ℕ) : ℤ) = 0 := by
  apply centralCoeffKernel_of_odd
  omega

theorem centralCoeffKernel_nat_step (d : ℕ) :
    ((d + 2 : ℕ) : ℚ) * centralCoeffKernel ((d + 2 : ℕ) : ℤ) =
      ((d + 1 : ℕ) : ℚ) * centralCoeffKernel (d : ℤ) := by
  by_cases hd : d % 2 = 0
  · obtain ⟨l, rfl⟩ : ∃ l : ℕ, d = 2 * l := ⟨d / 2, by omega⟩
    rw [show 2 * l + 2 = 2 * (l + 1) by omega,
      centralCoeffKernel_nat_even, centralCoeffKernel_nat_even]
    convert centralCoeff_step l using 1
  · obtain ⟨l, rfl⟩ : ∃ l : ℕ, d = 2 * l + 1 := ⟨d / 2, by omega⟩
    rw [show 2 * l + 1 + 2 = 2 * (l + 1) + 1 by omega,
      centralCoeffKernel_nat_odd, centralCoeffKernel_nat_odd]
    simp

theorem centralKernelSeries_differential :
    (1 - (PowerSeries.X : PowerSeries ℚ) ^ 2) *
        PowerSeries.derivative centralKernelSeries =
      PowerSeries.X * centralKernelSeries := by
  ext d
  rw [sub_mul, one_mul, map_sub]
  rcases d with _ | d
  · norm_num [PowerSeries.coeff_derivative, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_zero_X_mul, centralKernelSeries, centralCoeffKernel]
  · rw [PowerSeries.coeff_succ_X_mul]
    rcases d with _ | d
    · norm_num [PowerSeries.coeff_derivative, PowerSeries.coeff_X_pow_mul',
        centralKernelSeries, centralCoeffKernel, centralCoeff]
    · rw [show d + 1 + 1 = d + 2 by omega, PowerSeries.coeff_X_pow_mul,
        PowerSeries.coeff_derivative, PowerSeries.coeff_derivative]
      simp only [coeff_centralKernelSeries]
      have hs := centralCoeffKernel_nat_step (d + 1)
      simp only [Nat.add_assoc, Nat.reduceAdd] at hs ⊢
      push_cast at hs ⊢
      nlinarith only [hs]

theorem centralKernelSeries_inverse_square :
    (1 - (PowerSeries.X : PowerSeries ℚ) ^ 2) * centralKernelSeries ^ 2 = 1 := by
  apply PowerSeries.derivative.ext
  · rw [PowerSeries.derivative_one]
    calc
      PowerSeries.derivative
          ((1 - (PowerSeries.X : PowerSeries ℚ) ^ 2) * centralKernelSeries ^ 2) =
          (2 : PowerSeries ℚ) * centralKernelSeries *
            ((1 - PowerSeries.X ^ 2) * PowerSeries.derivative centralKernelSeries -
              PowerSeries.X * centralKernelSeries) := by
        simp only [Derivation.leibniz, map_sub, PowerSeries.derivative_one,
          PowerSeries.derivative_pow, PowerSeries.derivative_X,
          Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, smul_eq_mul]
        ring
      _ = 0 := by
        rw [centralKernelSeries_differential]
        ring
  · simp

end InternalCatalan

end

end OAI
