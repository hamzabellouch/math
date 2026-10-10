import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCommutatorRows

namespace OAI

/-! # An integrable output bound for bounded input frequencies

The frequency-localized commutator has a square-integrable row majorant.
This is the bounded-frequency counterpart of the R⁻¹ estimate.
-/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem schwartz_polynomial_decay (V : 𝓢(E, ℂ)) (n : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ ξ : E, (1 + ‖ξ‖) ^ n * ‖V ξ‖ ≤ M := by
  let M := 2 ^ n * (Finset.Iic (n, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) V
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun ξ => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (n, 0)) (k := n) (n := 0) (by rfl) (by rfl) V ξ
  have hh : (1 + ‖ξ‖) ^ n * ‖V ξ‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_zero] using h
  exact hh.trans (le_max_left _ _)

theorem homogeneousCommutatorRow_decay (N : ℕ) (j : Fin N → Fin 12)
    (V χ : 𝓢(E, ℂ)) (R : ℝ) (hR : 1 ≤ R)
    (hχ : ∀ η : E, R < ‖η‖ → χ η = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ η : E,
      ‖homogeneousCommutatorRowKernel N j V χ ξ η‖ ≤
        C * ((1 + ‖ξ‖) ^ (14 : ℕ))⁻¹ := by
  obtain ⟨M, hM, hMV⟩ := schwartz_polynomial_decay (radianFourierKernel V) (N + 14)
  let K := SchwartzMap.seminorm ℝ 0 0 χ
  let Q := 1 + R
  refine ⟨2 * Q ^ (2 * N + 14) * M * K, by dsimp [Q, K]; positivity, fun ξ η => ?_⟩
  by_cases hη : R < ‖η‖
  · simp only [homogeneousCommutatorRowKernel, hχ η hη, mul_zero, norm_zero]
    positivity
  · have hηR : ‖η‖ ≤ R := le_of_not_gt hη
    let X := 1 + ‖ξ‖
    let Z := 1 + ‖ξ - η‖
    have hQ : 1 ≤ Q := by dsimp [Q]; linarith
    have hX : 1 ≤ X := by dsimp [X]; linarith [norm_nonneg ξ]
    have hZ : 0 ≤ Z := by dsimp [Z]; positivity
    have hshift : X ≤ Q * Z := by
      have ht : ‖ξ‖ ≤ ‖ξ - η‖ + ‖η‖ := by
        calc
          ‖ξ‖ = ‖ξ - η + η‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      dsimp [X, Q, Z]
      nlinarith [norm_nonneg (ξ - η)]
    have hs : ‖homogeneousOrderedSymbol N j ξ - homogeneousOrderedSymbol N j η‖ ≤
        2 * Q ^ N * X ^ N := by
      have hx : ‖homogeneousOrderedSymbol N j ξ‖ ≤ X ^ N :=
        (homogeneousOrderedSymbol_norm_le N j ξ).trans
        (pow_le_pow_left₀ (norm_nonneg ξ) (by dsimp [X]; linarith) N)
      have hy : ‖homogeneousOrderedSymbol N j η‖ ≤ Q ^ N :=
        (homogeneousOrderedSymbol_norm_le N j η).trans
        (pow_le_pow_left₀ (norm_nonneg η) (by dsimp [Q]; linarith) N)
      have hQn : 1 ≤ Q ^ N := one_le_pow₀ hQ
      have hXn : 1 ≤ X ^ N := one_le_pow₀ hX
      have hqa : Q ^ N ≤ Q ^ N * X ^ N := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hXn (by positivity : 0 ≤ Q ^ N)
      have hxa : X ^ N ≤ Q ^ N * X ^ N := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hQn (by positivity : 0 ≤ X ^ N)
      exact (norm_sub_le _ _).trans (by nlinarith)
    have hp : X ^ (N + 14) ≤ Q ^ (N + 14) * Z ^ (N + 14) := by
      simpa only [mul_pow] using pow_le_pow_left₀ (by linarith : 0 ≤ X) hshift (N + 14)
    have hprod : ‖homogeneousCommutatorRowKernel N j V χ ξ η‖ ≤
        2 * Q ^ N * X ^ N * ‖radianFourierKernel V (ξ - η)‖ * K := by
      rw [homogeneousCommutatorRowKernel, norm_mul, norm_mul]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
        (SchwartzMap.norm_le_seminorm ℝ χ η) (norm_nonneg _) (by positivity)
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : 0 < (1 + ‖ξ‖) ^ (14 : ℕ))).mpr
    calc
      _ ≤ (2 * Q ^ N * X ^ N * ‖radianFourierKernel V (ξ - η)‖ * K) * X ^ 14 :=
        mul_le_mul_of_nonneg_right hprod (pow_nonneg (by linarith : 0 ≤ X) 14)
      _ = 2 * Q ^ N * X ^ (N + 14) * ‖radianFourierKernel V (ξ - η)‖ * K := by
        rw [pow_add]
        ring
      _ ≤ 2 * Q ^ N * (Q ^ (N + 14) * Z ^ (N + 14)) *
          ‖radianFourierKernel V (ξ - η)‖ * K := by gcongr
      _ = 2 * Q ^ (2 * N + 14) *
          (Z ^ (N + 14) * ‖radianFourierKernel V (ξ - η)‖) * K := by
        rw [show 2 * N + 14 = N + (N + 14) by omega, pow_add]
        ring
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hMV (ξ - η)) (by positivity)) (by dsimp [K]; positivity)

end DefocusingNLS

end OAI
