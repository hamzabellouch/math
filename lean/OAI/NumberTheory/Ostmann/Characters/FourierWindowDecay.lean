import OAI.NumberTheory.Ostmann.Arithmetic.RealBulkKernelPair

namespace OAI

/-! # The leaf-window decay retained in the Section 8 norm bound -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate

theorem normalizedFourierProfile_norm_window (ψ : ℝ → ℂ) (v B lo z : ℝ)
    (hψ : ∀ t, ‖ψ t‖ ≤ B) (hlo : 0 < lo) (hz : lo ≤ z) :
    ‖normalizedFourierProfile ψ v z‖ ≤ B / Real.sqrt lo := by
  have hs := Real.sqrt_pos.mpr hlo
  have hz' := Real.sqrt_le_sqrt hz
  rw [normalizedFourierProfile, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  calc
    _ ≤ (Real.sqrt z)⁻¹ * B :=
      mul_le_mul_of_nonneg_left (hψ _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ ≤ (Real.sqrt lo)⁻¹ * B :=
      mul_le_mul_of_nonneg_right (inv_anti₀ hs hz') ((norm_nonneg (ψ 0)).trans (hψ 0))
    _ = _ := by ring

theorem fourierPolynomialFactor_norm_window (P : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (v lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (x : ℝ) :
    ‖(fourierPolynomialFactor P ψ v lo hi hlo hhi).value x‖ ≤
      SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo := by
  apply normalizedFourierProfile_norm_window ψ v _ lo _
    (fun t => ψ.norm_le_seminorm ℝ t) (by linarith)
  exact (clipRealInterval_bounds lo hi (P.eval x) hhi).1

theorem realValueFourierWeight_norm_window {σ : Type*} (value : σ → ℝ) {n : ℕ}
    (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (L R : ℝ) :
    ‖realValueFourierWeight value T ψ X lo hi hlo hhi L R‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) := by
  have he : (SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) =
      ∏ _i : TreeLeafIndex n, SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo := by
    simp only [Finset.prod_const, Finset.card_univ, card_treeLeafIndex]
  rw [he, realValueFourierWeight, norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i _
  have hb := fourierPolynomialFactor_norm_window Polynomial.X ψ (T.leafFrequencies i)
    lo hi hlo hhi (T.realValueLeafModuli value L R i / X)
  split_ifs
  · simpa only [Complex.norm_conj] using hb
  · exact hb

theorem realValueNodeCutoff_norm_bound {σ : Type*} (value : σ → ℝ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hφ : ∀ x, |φ x| ≤ B)
    {n : ℕ} (T : MovingSlotData σ n) (L R : ℝ) :
    ‖realValueNodeCutoff value φ G T L R‖ ≤ B ^ (2 ^ n - 1) := by
  have hb (G x : ℝ) : ‖(positiveLogCutoff φ G x : ℂ)‖ ≤ B := by
    unfold positiveLogCutoff
    split_ifs
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using hφ _
    · simpa only [Complex.ofReal_zero, norm_zero] using hB
  induction T generalizing L R with
  | leaf => simp [realValueNodeCutoff]
  | @node n s CL CR u left right ihL ihR =>
    simp only [realValueNodeCutoff, norm_mul]
    calc
      _ ≤ (B * B ^ (2 ^ n - 1)) * B ^ (2 ^ n - 1) := by
        apply mul_le_mul _ (ihR _ _) (norm_nonneg _) (mul_nonneg hB (pow_nonneg hB _))
        exact mul_le_mul (hb _ _) (ihL _ _) (norm_nonneg _) hB
      _ = B ^ (2 ^ (n + 1) - 1) := by
        rw [← pow_succ', ← pow_add]
        congr 1
        have := Nat.one_le_two_pow (n := n)
        rw [pow_succ]
        omega

theorem realValueKernel_norm_window {σ : Type*} (value : σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hφ : ∀ x, |φ x| ≤ B) (L R : ℝ) :
    ‖realValueKernel value childBound pivotBound T ψ X lo hi hlo hhi φ G L R‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) * B ^ (2 ^ n - 1) := by
  have hψ : 0 ≤ SchwartzMap.seminorm ℝ 0 0 ψ :=
    (norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)
  rw [realValueKernel, norm_mul]
  apply (mul_le_mul_of_nonneg_right
    (realValueSupportFlag_norm value childBound pivotBound T X lo hi L R) (norm_nonneg _)).trans
  rw [one_mul, realValueSmoothWeight, norm_mul]
  exact mul_le_mul (realValueFourierWeight_norm_window value T ψ X lo hi hlo hhi L R)
    (realValueNodeCutoff_norm_bound value φ G B hB hφ T L R) (norm_nonneg _)
    (by positivity)

theorem realValueKernelPair_norm_window {σ : Type*} (value : σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : Bool → MovingSlotData σ n)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hφ : ∀ x, |φ x| ≤ B) (L R : ℝ) :
    ‖realValueKernelPair value childBound pivotBound T ψ X lo hi hlo hhi φ G L R‖ ≤
      ((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) * B ^ (2 ^ n - 1)) ^ 2 := by
  have hb b := realValueKernel_norm_window value childBound pivotBound (T b)
    ψ X lo hi hlo hhi φ G B hB hφ L R
  rw [realValueKernelPair, norm_mul, Complex.norm_conj, pow_two]
  exact mul_le_mul (hb false) (hb true) (norm_nonneg _) ((norm_nonneg _).trans (hb false))

/-- Exact exponential decay of the paired Fourier window budget. -/
theorem fourier_window_pair_exp (ψ : 𝓢(ℝ, ℂ)) (n : ℕ) (B Δ : ℝ) :
    ((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt (Real.exp Δ)) ^ (2 ^ n) *
      B ^ (2 ^ n - 1)) ^ 2 =
      ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1)) ^ 2 *
        Real.exp (-(2 ^ n : ℕ) * Δ) := by
  have hd : (Real.sqrt (Real.exp Δ) ^ (2 ^ n)) ^ 2 = Real.exp ((2 ^ n : ℕ) * Δ) := by
    rw [← pow_mul, Nat.mul_comm (2 ^ n) 2, pow_mul,
      Real.sq_sqrt (Real.exp_pos Δ).le, ← Real.exp_nat_mul]
  rw [div_pow, mul_pow, div_pow, hd, div_eq_mul_inv, ← Real.exp_neg]
  simp only [neg_mul]
  ring

theorem realValueKernelPair_norm_exp {σ : Type*} (value : σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : Bool → MovingSlotData σ n)
    (ψ : 𝓢(ℝ, ℂ)) (X Δ hi : ℝ) (hΔ : 0 ≤ Δ) (hhi : Real.exp Δ ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hφ : ∀ x, |φ x| ≤ B) (L R : ℝ) :
    ‖realValueKernelPair value childBound pivotBound T ψ X (Real.exp Δ) hi
      (Real.one_le_exp hΔ) hhi φ G L R‖ ≤
      ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1)) ^ 2 *
        Real.exp (-(2 ^ n : ℕ) * Δ) := by
  have h := realValueKernelPair_norm_window value childBound pivotBound T ψ X (Real.exp Δ) hi
    (Real.one_le_exp hΔ) hhi φ G B hB hφ L R
  exact h.trans_eq (fourier_window_pair_exp ψ n B Δ)

end Ostmann

end OAI
