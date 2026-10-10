import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.UnitTorusCoefficients
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzNonlinearPeriodization

namespace OAI

/-! # Exact nonlinear Fourier coefficients of a compact physical profile -/

open scoped SchwartzMap ComplexConjugate

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def schwartzPointConjugate (ψ : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ) ψ

@[simp] theorem schwartzPointConjugate_apply (ψ : 𝓢(E, ℂ)) (x : E) :
    schwartzPointConjugate ψ x = conj (ψ x) := rfl

noncomputable def schwartzOddPower : ℕ → 𝓢(E, ℂ) → 𝓢(E, ℂ)
  | 0, ψ => ψ
  | m + 1, ψ =>
      SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) ψ.hasTemperateGrowth
        (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ)
          (schwartzPointConjugate ψ).hasTemperateGrowth (schwartzOddPower m ψ))

@[simp] theorem schwartzOddPower_apply (m : ℕ) (ψ : 𝓢(E, ℂ)) (x : E) :
    schwartzOddPower m ψ x = oddPowerNonlinearity m (ψ x) := by
  induction m with
  | zero => simp [schwartzOddPower, oddPowerNonlinearity]
  | succ m ih =>
    change (schwartzOddPower m ψ x * conj (ψ x)) * ψ x = _
    rw [ih]
    simp only [oddPowerNonlinearity, pow_succ, starRingEnd_apply]
    ring

theorem sampled_oddPower_coefficient (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (m : ℕ) (ψ : 𝓢(E, ℂ)) (hψ : ∀ x : E, 2 * L < ‖x‖ → ψ x = 0)
    (n : frequencyLattice) :
    expandingFourierCoefficient a k L
      (expandingOddPower a k L ha ha1 hk hL m
        (schwartzTorusSample a k L ha1 hk hL (radianFourierKernel ψ))) n =
      schwartzLatticeCoefficient L (radianFourierKernel (schwartzOddPower m ψ)) n := by
  rw [← schwartzTorusSample_coefficient a k L ha1 hk hL]
  apply expandingFourierCoefficient_eq_of_torus_eq a k L ha ha1 hk hL
  intro x
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hx : L⁻¹ • (L • x) = x := by
    rw [smul_smul, inv_mul_cancel₀ hLp.ne', one_smul]
  rw [← hx, sampled_oddPower_periodization a k L ha ha1 hk hL m ψ hψ,
    schwartzTorusSample_physical a k L ha ha1 hk hL]
  exact tsum_congr fun n => (schwartzOddPower_apply m ψ _).symm

theorem sampled_oddPower_eq (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (m : ℕ) (ψ : 𝓢(E, ℂ)) (hψ : ∀ x : E, 2 * L < ‖x‖ → ψ x = 0) :
    expandingOddPower a k L ha ha1 hk hL m
        (schwartzTorusSample a k L ha1 hk hL (radianFourierKernel ψ)) =
      schwartzTorusSample a k L ha1 hk hL (radianFourierKernel (schwartzOddPower m ψ)) := by
  ext n
  rw [← weight_mul_expandingFourierCoefficient a k L hL _ n,
    sampled_oddPower_coefficient a k L ha ha1 hk hL m ψ hψ n,
    ← schwartzTorusSample_coefficient a k L ha1 hk hL]
  exact weight_mul_expandingFourierCoefficient a k L hL _ n

end DefocusingNLS

end OAI
