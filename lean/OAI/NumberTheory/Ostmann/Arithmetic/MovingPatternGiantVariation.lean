import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternKernelGain
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSpectatorCost

namespace OAI

/-! # Uniform giant variation cost at the selected-prime scales -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingFourierVariationBudget_mono_frequency (ψ : 𝓢(ℝ, ℂ))
    (V W lo hi : ℝ) (n : ℕ) (hV : 0 ≤ V) (hVW : V ≤ W) (hhi : lo ≤ hi) :
    movingFourierVariationBudget ψ V lo hi n ≤ movingFourierVariationBudget ψ W lo hi n := by
  have hB := (norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)
  have hD := schwartz_profile_lip_nonneg ψ
  have hwidth := sub_nonneg.mpr hhi
  unfold movingFourierVariationBudget
  gcongr

/-- The manuscript's bottom window has logarithmic height `Δ + O(1)`. -/
theorem movingWindow_width_le_exp (Δ C A m hi : ℝ) (hm : 1 ≤ m)
    (hΔ : Δ ≤ A * m) (hhi : hi ≤ Real.exp (Δ + C)) :
    hi - Real.exp Δ ≤ Real.exp ((A + |C|) * m) := by
  have hCm : C ≤ |C| * m := (le_abs_self C).trans
    (le_mul_of_one_le_right (abs_nonneg C) hm)
  apply (show hi - Real.exp Δ ≤ hi by linarith [Real.exp_pos Δ]).trans
  apply hhi.trans
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- The complete pointwise cost needed for both giant integrations is bounded
before choosing the Fourier window, its frequencies, or the spectator primes. -/
theorem movingPattern_pointwise_cost_budget (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin B D : ℝ) (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      let m := spectatorBulkCount k L
      ∀ (p : Fin m → ℕ) (V lo hi : ℝ), 0 ≤ V → V ≤ Real.exp (A * m) →
      lo ≤ hi → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      4 * (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 *
          (movingFourierVariationBudget ψ V lo hi n *
            (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
        Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
  obtain ⟨Cw, hCw, hkernel⟩ := movingPatternKernelBudget_spectatorScale_window
    ψ n r₀ k A Wwin B D hA hWwin
  let K := (k : ℝ) ^ 4 + 4
  let Cs := (((2 ^ (n + 1) : ℕ) : ℝ) + 1) * K
  let C := max Cw Cs
  have hK : 4 ≤ K := by
    dsimp only [K]
    linarith [pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4]
  have hCwC : Cw ≤ C := le_max_left _ _
  have hCsC : Cs ≤ C := le_max_right _ _
  refine ⟨C, hCw.trans hCwC, ?_⟩
  intro L hL
  dsimp only
  intro p V lo hi hV hVA hhi hwidth hp
  let m := spectatorBulkCount k L
  have hL0 : 0 ≤ L := by linarith
  have hm : (m : ℝ) ≤ K * L := (spectatorBulkCount_upper k L hL0).trans
    (mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) hL0)
  have hKL : 4 ≤ K * L := by nlinarith
  have hamp : (4 : ℝ) ≤ Real.exp (K * L) := by
    linarith [Real.add_one_le_exp (K * L)]
  have hspec := moving_spectator_linear_cost n m p K L 4 (by linarith) hL0 (by norm_num) hm hamp hp
  have hprod : (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 = ∏ i, (p i : ℝ) ^ (2 ^ (n + 1)) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, pow_succ]
  have hspec' : 4 * (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 ≤
      Real.exp (C * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
    rw [hprod]
    apply hspec.trans
    apply Real.exp_le_exp.mpr
    change Cs * L * Real.exp ((1 / 1000 : ℝ) * L) ≤ _
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hCsC hL0
    · exact Real.exp_le_exp.mpr (by nlinarith)
    · exact Real.exp_nonneg _
    · exact mul_nonneg (by linarith [hCw.trans hCwC]) hL0
  have hvar := movingFourierVariationBudget_mono_frequency ψ V (Real.exp (A * m)) lo hi n hV hVA hhi
  have hsmooth :
      (movingFourierVariationBudget ψ V lo hi n *
        (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
      Real.exp (C * L ^ 2) := by
    have hpow :
        (movingFourierVariationBudget ψ V lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 := by
      rw [mul_pow, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (movingFourierVariationBudget_nonneg ψ V lo hi n hV hhi) hvar 2)
        (sq_nonneg _)
    exact hpow.trans ((bulkKernelPair_smooth_le_budget ψ (Real.exp (A * m)) lo hi n
      (2 ^ n * (r₀ + m + 4 * n + 4)) (2 ^ n * (r₀ + m + 4 * n)) 0 B D).trans
      ((hkernel L hL lo hi hhi hwidth).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCwC (sq_nonneg L)))))
  calc
    _ ≤ Real.exp (C * L * Real.exp ((1 / 1000 : ℝ) * L)) * Real.exp (C * L ^ 2) :=
      mul_le_mul hspec' hsmooth (sq_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

/-- The giant comparison uses a weaker upper scale than the spectator cost. -/
theorem movingPattern_giant_variation_budget (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin B D : ℝ) (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      let m := spectatorBulkCount k L
      ∀ (p : Fin m → ℕ) (V lo hi : ℝ), 0 ≤ V → V ≤ Real.exp (A * m) →
      lo ≤ hi → hi - lo ≤ Real.exp (Wwin * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      2 * (∏ i, (p i : ℝ) ^ (2 ^ n)) ^ 2 *
          (movingFourierVariationBudget ψ V lo hi n *
            (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
        Real.exp (C * L ^ 2 + C * L * Real.exp ((12 / 1000 : ℝ) * L)) := by
  obtain ⟨C, hC, hb⟩ := movingPattern_pointwise_cost_budget ψ n r₀ k A Wwin B D hA hWwin
  refine ⟨C, hC, ?_⟩
  intro L hL
  dsimp only
  intro p V lo hi hV hVA hhi hwidth hp
  apply le_trans _ (le_trans (hb L hL p V lo hi hV hVA hhi hwidth hp) ?_)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 4) (sq_nonneg _))
      (sq_nonneg _)
  · apply Real.exp_le_exp.mpr
    apply add_le_add (le_refl _)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (mul_nonneg (by linarith) (by linarith))

end Ostmann

end OAI
