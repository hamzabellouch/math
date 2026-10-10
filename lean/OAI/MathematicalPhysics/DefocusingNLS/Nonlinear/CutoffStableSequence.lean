import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusDiscreteLinearData
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphSmallRemainder
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffStepRemainder

namespace OAI

/-! # Decaying endpoint sequences for the actual cutoff remainder estimates -/

open scoped NNReal

namespace DefocusingNLS

local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem exists_cutoffStable_sequence_threshold {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (a δ B : ℝ) (ha : 0 < a) (hδ : 0 < δ) (hB : 0 ≤ B)
    (T : ℝ≥0) (hratio : 2 * Real.exp (-(2 + a) * T / 2) ≤ 1)
    (A : Radius → FourierL2 →L[ℝ] FourierL2) (hA : HasTorusLinearStep (F := F) T A) :
    ∃ ρ : ℝ, 0 < ρ ∧ 2 * ρ ≤ δ ∧ ∃ L₀ : ℝ,
      ∀ L : Radius, L₀ ≤ L.1 →
        ∃ ζ : ℕ → F →L[ℝ] FourierL2, ∃ π : ℕ → FourierL2 →L[ℝ] F,
          (∀ n v, π n (ζ n v) = v) ∧
          ∀ h : ℕ → {v : FourierL2 // ‖v‖ ≤ δ} → FourierL2,
            (∀ n d, 0 < d → d ≤ δ → ∀ v w, ‖v.1‖ ≤ d → ‖w.1‖ ≤ d →
              ‖h n v - h n w‖ ≤
                B * (d + (expandingDiscreteRadius L T n).1 ^ (-2 - a)) * ‖v.1 - w.1‖) →
            (∀ n v, v.1 = 0 → ‖h n v‖ ≤ B * (expandingDiscreteRadius L T n).1 ^ (-2 - a)) →
            ∀ w₀ : FourierL2, ‖w₀‖ ≤ ρ / 4 → π 0 w₀ = 0 →
              ∃ z : ℕ → FourierL2,
                stableFrameProjection (ζ 0) (π 0) (z 0) = w₀ ∧
                (∀ n, z (n + 1) = A (expandingDiscreteRadius L T n) (z n) +
                  cutoffRemainderExtension δ h n (z n)) ∧
                (∀ n, ‖z n‖ ≤ (2 * ρ) * (1 / 2 : ℝ) ^ n) := by
  obtain ⟨C, hC, hlinear⟩ := torusLinearStep_discrete T A hA
  obtain ⟨σ, Llip, hσ, hσδ, hLlip, hlip⟩ := exists_cutoffRemainder_small_lipschitz
    a B δ (1 / (128 * (C + 1))) ha hB hδ (by positivity)
  let ρ := σ / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have h2ρ : 2 * ρ = σ := by dsimp [ρ]; ring
  obtain ⟨Llin, hLlin⟩ := hlinear (1 / 128) (by norm_num)
  obtain ⟨Lforce, _, hforce⟩ := exists_cutoffResidual_small_scale a (C * B) (ρ / 8) ha (by positivity)
  refine ⟨ρ, hρ, by rw [h2ρ]; exact hσδ, max Llin (max Llip Lforce), ?_⟩
  intro L hL
  have hLlinear : Llin ≤ L.1 := (le_max_left _ _).trans hL
  have hLlip' : Llip ≤ L.1 := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLforce : Lforce ≤ L.1 := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  obtain ⟨ζ, π, D, R, hinv, hR, hπζ, hζ, hπ, hP, hstable, hmixed, he⟩ := hLlin L hLlinear
  refine ⟨ζ, π, hπζ, ?_⟩
  intro h hl hz w₀ hw₀ hker
  let ε := B * L.1 ^ (-2 - a)
  have hLp : 0 < L.1 := lt_of_lt_of_le zero_lt_one L.2
  have hε : 0 ≤ ε := mul_nonneg hB (Real.rpow_nonneg hLp.le _)
  have hsmall : ‖w₀‖ + 2 * (C * ε) ≤ ρ / 2 := by
    have hf := hforce L.1 hLforce
    change C * B * L.1 ^ (-2 - a) ≤ ρ / 8 at hf
    dsimp [ε]
    nlinarith
  have hLip : ∀ n v w, ‖v‖ ≤ 2 * ρ → ‖w‖ ≤ 2 * ρ →
      ‖cutoffRemainderExtension δ h n v - cutoffRemainderExtension δ h n w‖ ≤
        (1 / (128 * (C + 1))) * ‖v - w‖ := by
    intro n v w hv hw
    have hest := cutoffRemainderExtension_lipschitz a L.1 T δ σ B hLp T.2 ha hσ hσδ hB h hl
      n v w (by rwa [← h2ρ]) (by rwa [← h2ρ])
    exact hest.trans (mul_le_mul_of_nonneg_right (hlip L.1 hLlip') (norm_nonneg _))
  have hZero : ∀ n, ‖cutoffRemainderExtension δ h n 0‖ ≤
      ε * (Real.exp (-(2 + a) * T / 2)) ^ n :=
    cutoffRemainderExtension_zero_bound a L.1 T δ B hLp hδ.le h hz
  obtain ⟨z, hz0, hzstep, hzbound⟩ := exists_stableGraph_of_small_remainder ζ π
    (fun n => A (expandingDiscreteRadius L T n)) D R hR hinv hπζ hstable hmixed
    C ρ ε (Real.exp (-(2 + a) * T / 2)) hC hρ.le hε (Real.exp_nonneg _) hratio
    hζ hπ hP he (cutoffRemainderExtension δ h) hLip hZero w₀ hker hsmall
  refine ⟨z, hz0, hzstep, fun n => (hzbound n).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith

end DefocusingNLS

end OAI
