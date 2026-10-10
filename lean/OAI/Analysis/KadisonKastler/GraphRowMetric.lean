import OAI.Analysis.KadisonKastler.GraphRowClipping
import OAI.Analysis.KadisonKastler.HilbertColumns

namespace OAI

/-! # The normalized graph metric of a rectangular operator row

The second graph coordinate loses its rescaling factor after summing the
adjoint column. This is the exact matrix-level estimate used with
complete near-inclusion, without an ordinary-gap amplification claim.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- A continuous operator acts contractively on finite RMS up to its norm. -/
theorem finiteRMS_apply_le {I K : Type*} [Fintype I]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (T : H →L[ℂ] K) (v : I → H) :
    finiteRMS (fun i => T (v i)) ≤ ‖T‖ * finiteRMS v := by
  apply (sq_le_sq₀ (finiteRMS_nonneg _) (mul_nonneg (norm_nonneg T) (finiteRMS_nonneg v))).mp
  rw [mul_pow, finiteRMS_sq, finiteRMS_sq, Finset.mul_expect]
  apply Finset.expect_le_expect
  intro i _
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm (v i)) 2

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
/-- Constant pointwise norm gives the same norm in finite RMS. -/
theorem finiteRMS_eq_of_norm_eq {I : Type*} [Fintype I] [Nonempty I]
    (v : I → H) {C : ℝ} (hC : 0 ≤ C) (hv : ∀ i, ‖v i‖ = C) : finiteRMS v = C := by
  unfold finiteRMS
  simp only [hv, Fintype.expect_const, Real.sqrt_sq hC]

/-- At rescaling sqrt(k), the normalized squared graph norm is controlled
by twice the squared rectangular row norm. -/
theorem graphRowRMS_sq_le {k : ℕ} (hk : 0 < k)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (Y : Fin k → H →L[ℂ] H) :
    (finiteRMS (fun i => rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (Y i))) ^ 2 ≤
      2 * ‖operatorRow Y‖ ^ 2 * ‖Ω‖ ^ 2 := by
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hn (i : Fin k) : ‖Y i Ω‖ ≤ ‖operatorRow Y‖ * ‖Ω‖ :=
    (Y i).le_opNorm Ω |>.trans (mul_le_mul_of_nonneg_right
      (CStarMatrix.norm_entry_le_norm (M := operatorRow Y) (i := ()) (j := i)) (norm_nonneg Ω))
  have hfirst : (𝔼 i : Fin k, ‖Y i Ω‖ ^ 2) ≤ ‖operatorRow Y‖ ^ 2 * ‖Ω‖ ^ 2 := by
    calc
      _ ≤ (𝔼 _ : Fin k, (‖operatorRow Y‖ * ‖Ω‖) ^ 2) :=
        Finset.expect_le_expect (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hn i) 2)
      _ = _ := by simp only [Fintype.expect_const, mul_pow]
  have hcolumn : ‖operatorColumn (fun i => star (Y i))‖ = ‖operatorRow Y‖ := by
    rw [norm_operatorColumn_eq_row_star]
    simp only [star_star]
  have hsecond := pow_le_pow_left₀ (norm_nonneg _)
    (norm_operatorColumn_apply_le (fun i => star (Y i)) Ω) 2
  rw [PiLp.norm_sq_eq_of_L2, hcolumn, mul_pow] at hsecond
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hsecond' : (k : ℝ) * (𝔼 i : Fin k, ‖star (Y i) Ω‖ ^ 2) ≤
      ‖operatorRow Y‖ ^ 2 * ‖Ω‖ ^ 2 := by
    simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, mul_div_cancel₀ _ hkR] using hsecond
  rw [finiteRMS_sq]
  simp_rw [norm_rescaledGraphVector_sq, Real.sq_sqrt (Nat.cast_nonneg k)]
  rw [Finset.expect_add_distrib, ← Finset.mul_expect]
  linarith

/-- The rectangular row estimate in norm form. -/
theorem graphRowRMS_le {k : ℕ} (hk : 0 < k)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (Y : Fin k → H →L[ℂ] H) :
    finiteRMS (fun i => rescaledGraphVector J Ω (Real.sqrt (k : ℝ)) (Y i)) ≤
      Real.sqrt 2 * ‖operatorRow Y‖ * ‖Ω‖ := by
  have h := graphRowRMS_sq_le hk J Ω Y
  have hs : (Real.sqrt 2 * ‖operatorRow Y‖ * ‖Ω‖) ^ 2 =
      2 * ‖operatorRow Y‖ ^ 2 * ‖Ω‖ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  apply (sq_le_sq₀ (finiteRMS_nonneg _) (by positivity)).mp
  rwa [hs]

end

end KadisonKastler

end OAI
