import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallGcdSum
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticRoughDyadic

namespace OAI

/-! # One complete descent step for the original rough moment -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_rough_descent {ξ η : ℝ} (h : QuadraticSieveGrowth ξ)
    (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N₀ N K D₀ : ℕ,
      0 < M → 0 < N → N ≤ N₀ → 0 < D₀ → 0 < K → K ≤ M →
      2 * (2 * (N₀ : ℝ)) ^ 2 * (((M : ℝ) * N₀) ^ η) ≤ (M : ℝ) * ((K : ℝ) + 1) →
      ∀ T : ℝ, 0 ≤ T → QuadraticRoughBound M (2 * N / D₀) K T →
        QuadraticRoughBound M N K
          ((Nat.log 2 N + 1 : ℕ) *
            (C * ((M : ℝ) * N₀) ^ (36 * η) * (D₀ : ℝ) ^ 5 *
              quadraticDescentScale ξ M N₀ K + C * (2 * (N₀ : ℝ)) ^ η * T)) := by
  obtain ⟨A, hA, ha⟩ := quadratic_small_gcd_sum_growth h hξ hξ' hη
  obtain ⟨B, hB, hb⟩ := quadratic_rough_gcd_descent_epsilon η hη
  let C := A + B + 6
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro M N₀ N K D₀ hM hN hNN hD₀ hK hKM hcut T hT hshort v
  let F := ((M : ℝ) * N₀) ^ (36 * η) * (D₀ : ℝ) ^ 5 *
    quadraticDescentScale ξ M N₀ K
  let U := C * F + C * (2 * (N₀ : ℝ)) ^ η * T
  have hNN₀ : 0 < N₀ := lt_of_lt_of_le hN hNN
  have hX : 1 ≤ (M : ℝ) * N₀ := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast hM) (by exact_mod_cast hNN₀)
  have hD₁ : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD₀
  have hFp : 0 ≤ F := mul_nonneg (by positivity) (quadraticDescentScale_nonneg _ _ _ _)
  have hCF : A * F ≤ C * F := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hFp
  have hFM : (M : ℝ) * D₀ ≤ F := by
    have hp : 1 ≤ ((M : ℝ) * N₀) ^ (36 * η) := Real.one_le_rpow hX (by positivity)
    have hD : (D₀ : ℝ) ≤ (D₀ : ℝ) ^ 5 := le_self_pow₀ hD₁ (by norm_num)
    have hV : (M : ℝ) ≤ quadraticDescentScale ξ M N₀ K := by
      unfold quadraticDescentScale
      have : 0 ≤ Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) := by positivity
      have : 0 ≤ Real.sqrt M * N₀ / Real.sqrt K := by positivity
      linarith [Nat.cast_nonneg (α := ℝ) N₀]
    calc
      _ = 1 * (D₀ : ℝ) * M := by ring
      _ ≤ ((M : ℝ) * N₀) ^ (36 * η) * (D₀ : ℝ) ^ 5 *
          quadraticDescentScale ξ M N₀ K := by gcongr
      _ = F := rfl
  have hblock (j : ℕ) (hj : j ∈ Finset.range (Nat.log 2 N + 1)) :
      quadraticRoughEnergy M (2 * 2 ^ j) K (quadraticDyadicCoeff N j v) ≤
        U * quadraticSieveEnergy (2 * 2 ^ j) (quadraticDyadicCoeff N j v) := by
    let R := 2 ^ j
    let w := quadraticDyadicCoeff N j v
    have hR : 0 < R := by dsimp [R]; positivity
    have hRN : R ≤ N := (Nat.pow_le_pow_right (by norm_num : 0 < 2)
      (by have := Finset.mem_range.mp hj; omega)).trans (Nat.pow_log_le_self 2 (by omega))
    have hRN₀ := hRN.trans hNN
    have hE : 0 ≤ quadraticSieveEnergy (2 * R) w := Finset.sum_nonneg fun _ _ => sq_nonneg _
    by_cases hsmall : R ≤ D₀
    · apply (quadratic_rough_bound_trivial M (2 * R) K w).trans
      apply mul_le_mul_of_nonneg_right _ hE
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      have hRreal : (R : ℝ) ≤ D₀ := by exact_mod_cast hsmall
      have hm : 3 * (M : ℝ) * (2 * R) ≤ 6 * F := by nlinarith [Nat.cast_nonneg (α := ℝ) M]
      have h6 : 6 * F ≤ C * F := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hFp
      exact (hm.trans h6).trans (le_add_of_nonneg_right (by dsimp [C]; positivity))
    · have hshortR : QuadraticRoughBound M (2 * R / D₀) K T :=
        hshort.mono_second (Nat.div_le_div_right (Nat.mul_le_mul_left 2 hRN))
      have hsum := ha M N₀ R K D₀ hM hR hRN₀ hD₀ (lt_of_not_ge hsmall) hK hKM
        hcut w (fun n hn => quadraticDyadicCoeff_below N j v hn)
      have hdesc := hb M (2 * R) K D₀ hD₀ T hT hshortR w
      have hpow : (2 * (R : ℝ)) ^ η ≤ (2 * (N₀ : ℝ)) ^ η := by
        apply Real.rpow_le_rpow (by positivity) _ hη.le
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hRN₀) (by norm_num)
      have htail : B * ((2 * R : ℕ) : ℝ) ^ η * T ≤ C * (2 * (N₀ : ℝ)) ^ η * T := by
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        gcongr
        dsimp [C]
        linarith
      have hsum' : (∑ D ∈ (Finset.Icc 1 (2 * R)).filter (fun D => D ≤ D₀),
          ‖quadraticRoughGcdMoment M (2 * R) K D w‖) ≤
          A * F * quadraticSieveEnergy (2 * R) w := by
        convert hsum using 1
        dsimp [F]
        ring
      have hs := mul_le_mul_of_nonneg_right hCF hE
      have ht := mul_le_mul_of_nonneg_right htail hE
      dsimp only [U]
      nlinarith only [hdesc, hsum', hs, ht]
  apply (quadratic_rough_energy_dyadic M N K v).trans
  calc
    _ ≤ (Nat.log 2 N + 1 : ℕ) * ∑ j ∈ Finset.range (Nat.log 2 N + 1),
        U * quadraticSieveEnergy (2 * 2 ^ j) (quadraticDyadicCoeff N j v) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hblock) (Nat.cast_nonneg _)
    _ = (Nat.log 2 N + 1 : ℕ) * U * quadraticSieveEnergy N v := by
      rw [← Finset.mul_sum, quadratic_dyadic_coeff_energy_sum]
      ring
    _ = _ := by dsimp [U, F]; ring

end Ostmann

end OAI
