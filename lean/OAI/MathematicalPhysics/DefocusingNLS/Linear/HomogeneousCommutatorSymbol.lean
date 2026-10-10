import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOrderedDerivatives

namespace OAI

/-! # One frequency gain in the actual ordered derivative commutator

The difference of the two ordered Fourier symbols loses one power of the
large frequency. This is the algebraic input for the high-energy compact
commutator; no compactness or operator estimate is assumed here.
-/

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousOrderedSymbol (N : ℕ) (j : Fin N → Fin 12) (ξ : E) : ℂ :=
  ∏ i, ((ξ (j i) : ℂ) * Complex.I)

theorem homogeneousOrderedSymbol_norm_le (N : ℕ) (j : Fin N → Fin 12) (ξ : E) :
    ‖homogeneousOrderedSymbol N j ξ‖ ≤ ‖ξ‖ ^ N := by
  unfold homogeneousOrderedSymbol
  rw [norm_prod]
  calc
    _ ≤ ∏ _i : Fin N, ‖ξ‖ := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun i _ => by
        simpa only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one] using
          PiLp.norm_apply_le ξ (j i))
    _ = _ := by simp

theorem homogeneousOrderedSymbol_sub_le (N : ℕ) (j : Fin (N + 1) → Fin 12) (ξ η : E) :
    ‖homogeneousOrderedSymbol (N + 1) j ξ - homogeneousOrderedSymbol (N + 1) j η‖ ≤
      (N + 1 : ℕ) * ‖ξ - η‖ * (‖ξ‖ + ‖η‖) ^ N := by
  induction N with
  | zero =>
      simp only [homogeneousOrderedSymbol, Fin.prod_univ_succ, Fin.prod_univ_zero, Nat.zero_add, Nat.cast_one,
        one_mul, pow_zero, mul_one]
      rw [← sub_mul, norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_sub, Complex.norm_real]
      exact PiLp.norm_apply_le (ξ - η) (j 0)
  | succ N ih =>
      let R := ‖ξ‖ + ‖η‖
      let d := ‖ξ - η‖
      let A := ((ξ (j 0) : ℂ) * Complex.I)
      let B := ((η (j 0) : ℂ) * Complex.I)
      let P := homogeneousOrderedSymbol (N + 1) (Fin.tail j) ξ
      let Q := homogeneousOrderedSymbol (N + 1) (Fin.tail j) η
      have hR : 0 ≤ R := by dsimp [R]; positivity
      have hd : 0 ≤ d := norm_nonneg _
      have hA' : ‖A‖ ≤ ‖ξ‖ := by
        simpa only [A, norm_mul, Complex.norm_real, Complex.norm_I, mul_one] using
          PiLp.norm_apply_le ξ (j 0)
      have hA : ‖A‖ ≤ R := hA'.trans (le_add_of_nonneg_right (norm_nonneg η))
      have hAB : ‖A - B‖ ≤ d := by
        dsimp only [A, B, d]
        rw [← sub_mul, norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_sub, Complex.norm_real]
        exact PiLp.norm_apply_le (ξ - η) (j 0)
      have hQ : ‖Q‖ ≤ R ^ (N + 1) := (homogeneousOrderedSymbol_norm_le (N + 1) (Fin.tail j) η).trans
        (pow_le_pow_left₀ (norm_nonneg η) (le_add_of_nonneg_left (norm_nonneg ξ)) _)
      have hPQ : ‖P - Q‖ ≤ (N + 1 : ℕ) * d * R ^ N := ih (Fin.tail j)
      have hξ : homogeneousOrderedSymbol (N + 1 + 1) j ξ = A * P := by
        simpa only [homogeneousOrderedSymbol, A, P, Fin.tail_def] using
          Fin.prod_univ_succ (fun i => (ξ (j i) : ℂ) * Complex.I)
      have hη : homogeneousOrderedSymbol (N + 1 + 1) j η = B * Q := by
        simpa only [homogeneousOrderedSymbol, B, Q, Fin.tail_def] using
          Fin.prod_univ_succ (fun i => (η (j i) : ℂ) * Complex.I)
      rw [hξ, hη]
      calc
        _ = ‖A * (P - Q) + (A - B) * Q‖ := by congr 1; ring
        _ ≤ ‖A‖ * ‖P - Q‖ + ‖A - B‖ * ‖Q‖ := by
          simpa only [norm_mul] using norm_add_le (A * (P - Q)) ((A - B) * Q)
        _ ≤ R * ((N + 1 : ℕ) * d * R ^ N) + d * R ^ (N + 1) := by
          exact add_le_add (mul_le_mul hA hPQ (norm_nonneg _) hR)
            (mul_le_mul hAB hQ (norm_nonneg _) hd)
        _ = _ := by simp only [Nat.cast_add, Nat.cast_one, pow_succ]; ring

theorem homogeneousOrderedSymbol_highFrequency (N : ℕ) (j : Fin (N + 1) → Fin 12)
    (ξ η : E) (R : ℝ) (hR : 1 ≤ R) (hη : R ≤ ‖η‖) :
    ‖homogeneousOrderedSymbol (N + 1) j ξ - homogeneousOrderedSymbol (N + 1) j η‖ ≤
      ((N + 1 : ℕ) / R) * ‖ξ - η‖ * (2 + ‖ξ - η‖) ^ N * ‖η‖ ^ (N + 1) := by
  have hη1 : 1 ≤ ‖η‖ := hR.trans hη
  have hr : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have ht : ‖ξ‖ ≤ ‖ξ - η‖ + ‖η‖ := by
    calc
      ‖ξ‖ = ‖ξ - η + η‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hsum : ‖ξ‖ + ‖η‖ ≤ (2 + ‖ξ - η‖) * ‖η‖ := by
    nlinarith [norm_nonneg (ξ - η), mul_le_mul_of_nonneg_left hη1 (norm_nonneg (ξ - η))]
  have hpow : (‖ξ‖ + ‖η‖) ^ N ≤ (2 + ‖ξ - η‖) ^ N * ‖η‖ ^ N := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hsum N
  have hgain : ‖η‖ ^ N ≤ R⁻¹ * ‖η‖ ^ (N + 1) := by
    have hi : R * ‖η‖ ^ N ≤ ‖η‖ ^ (N + 1) := by
      simpa only [pow_succ, mul_comm] using mul_le_mul_of_nonneg_right hη (pow_nonneg (norm_nonneg η) N)
    have hh := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hr.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul] using hh
  calc
    _ ≤ (N + 1 : ℕ) * ‖ξ - η‖ * (‖ξ‖ + ‖η‖) ^ N :=
      homogeneousOrderedSymbol_sub_le N j ξ η
    _ ≤ (N + 1 : ℕ) * ‖ξ - η‖ * ((2 + ‖ξ - η‖) ^ N * ‖η‖ ^ N) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ (N + 1 : ℕ) * ‖ξ - η‖ * ((2 + ‖ξ - η‖) ^ N * (R⁻¹ * ‖η‖ ^ (N + 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgain (by positivity)) (by positivity)
    _ = _ := by rw [div_eq_mul_inv]; ring

end DefocusingNLS

end OAI
