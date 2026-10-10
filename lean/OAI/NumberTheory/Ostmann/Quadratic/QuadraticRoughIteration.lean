import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFiniteDescent

namespace OAI

/-! # Iterating the actual rough-moment estimate with uniform constants -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_rough_iteration {ξ η : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ M N K D r : ℕ,
      0 < M → 0 < N → 2 ≤ D → 0 < K → K ≤ M →
      2 ^ r * N < D ^ r →
      2 * (2 * (N : ℝ)) ^ 2 * (((M : ℝ) * N) ^ η) ≤ (M : ℝ) * ((K : ℝ) + 1) →
      QuadraticRoughBound M N K
        ((r : ℝ) * (C * (Nat.log 2 N + 1 : ℕ) * (2 * (N : ℝ)) ^ η) ^ r *
          (C * (Nat.log 2 N + 1 : ℕ) * ((M : ℝ) * N) ^ (36 * η) *
            (D : ℝ) ^ 5 * quadraticDescentScale ξ M N K)) := by
  obtain ⟨C₀, hC₀, hc⟩ := quadratic_rough_descent h hξ hξ' hη
  let C := C₀ + 1
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro M N K D r hM hN hD hK hKM hpow hcut
  let L : ℝ := (Nat.log 2 N + 1 : ℕ)
  let F := ((M : ℝ) * N) ^ (36 * η) * (D : ℝ) ^ 5 * quadraticDescentScale ξ M N K
  let A := C * L * F
  let B := C * L * (2 * (N : ℝ)) ^ η
  have hC : 0 < C := by dsimp [C]; linarith
  have hL : 1 ≤ L := by
    dsimp [L]
    exact_mod_cast Nat.le_add_left 1 (Nat.log 2 N)
  have hF : 0 ≤ F := mul_nonneg (by positivity) (quadraticDescentScale_nonneg _ _ _ _)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 1 ≤ B := by
    apply one_le_mul_of_one_le_of_one_le
    · exact one_le_mul_of_one_le_of_one_le (by dsimp [C]; linarith) hL
    · apply Real.one_le_rpow _ hη.le
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
  have hstep (n : ℕ) (hn : 0 < n) (hnN : n ≤ N) (T : ℝ) (hT : 0 ≤ T)
      (hshort : QuadraticRoughBound M (2 * n / D) K T) :
      QuadraticRoughBound M n K (A + B * T) := by
    apply (hc M N n K D hM hn hnN (by omega) hK hKM hcut T hT hshort).mono_constant
    have hl : ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ L := by
      dsimp [L]
      exact_mod_cast Nat.add_le_add_right (Nat.log_mono_right (b := 2) hnN) 1
    have hcn : C₀ ≤ C := by dsimp [C]; linarith
    calc
      _ = ((Nat.log 2 n + 1 : ℕ) : ℝ) * (C₀ * F + C₀ * (2 * (N : ℝ)) ^ η * T) := by
        dsimp [F]; ring
      _ ≤ L * (C * F + C * (2 * (N : ℝ)) ^ η * T) := by gcongr
      _ = A + B * T := by dsimp [A, B]; ring
  apply (quadratic_rough_finite_descent hD hA (by linarith : 0 ≤ B)
    hstep r N le_rfl hpow).mono_constant
  convert quadraticDescentBudget_bound hA hB r using 1
  dsimp [A, B, F, L]
  ring

end Ostmann

end OAI
