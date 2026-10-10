import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.ContinuousTorusDiscreteData
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableSmallRemainderContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffRemainderContinuity

namespace OAI

/-! # Continuous stable endpoint sequences for the expanding torus -/

open scoped NNReal

universe u

namespace DefocusingNLS

local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem exists_continuous_cutoffStable_sequence_threshold
    {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (a δ B : ℝ) (ha : 0 < a) (hδ : 0 < δ) (hB : 0 ≤ B)
    (T : ℝ≥0) (hratio : 2 * Real.exp (-(2 + a) * T / 2) ≤ 1)
    (A : Radius → FourierL2 →L[ℝ] FourierL2)
    (hAc : Continuous (fun q : Radius × FourierL2 => A q.1 q.2))
    (hA : HasContinuousTorusLinearStep (F := F) T A) :
    ∃ C : ℝ, 0 < C ∧ ∃ ρ : ℝ, 0 < ρ ∧ 2 * ρ ≤ δ ∧ ∃ L₀ : ℝ,
      ∃ ζ : Radius → ℕ → F →L[ℝ] FourierL2,
      ∃ π : Radius → ℕ → FourierL2 →L[ℝ] F,
        (∀ n, ContinuousOn (fun L => ζ L n) {L : Radius | L₀ ≤ L.1}) ∧
        (∀ n, Continuous (fun p : Radius × FourierL2 => π p.1 n p.2)) ∧
        (∀ L : Radius, L₀ ≤ L.1 → ∀ n, ‖ζ L n‖ ≤ 1 ∧ ‖π L n‖ ≤ C) ∧
        (∀ L : Radius, L₀ ≤ L.1 → ∀ n v, π L n (ζ L n v) = v) ∧
        ∀ (P : Type u) [TopologicalSpace P], ∀ L : P → Radius,
          Continuous L → (∀ p, L₀ ≤ (L p).1) →
          ∀ h : P → ℕ → {v : FourierL2 // ‖v‖ ≤ δ} → FourierL2,
            (∀ n, Continuous (fun q : P × {v : FourierL2 // ‖v‖ ≤ δ} => h q.1 n q.2)) →
            (∀ p n d, 0 < d → d ≤ δ → ∀ v u, ‖v.1‖ ≤ d → ‖u.1‖ ≤ d →
              ‖h p n v - h p n u‖ ≤
                B * (d + (expandingDiscreteRadius (L p) T n).1 ^ (-2 - a)) * ‖v.1 - u.1‖) →
            (∀ p n v, v.1 = 0 → ‖h p n v‖ ≤
              B * (expandingDiscreteRadius (L p) T n).1 ^ (-2 - a)) →
            ∀ w : P → FourierL2, Continuous w → (∀ p, ‖w p‖ ≤ ρ / 4) →
              (∀ p, π (L p) 0 (w p) = 0) →
              ∃ z : P → ℕ → FourierL2,
                (∀ n, Continuous (fun p => z p n)) ∧
                (∀ p, stableFrameProjection (ζ (L p) 0) (π (L p) 0) (z p 0) = w p) ∧
                (∀ p n, z p (n + 1) = A (expandingDiscreteRadius (L p) T n) (z p n) +
                  cutoffRemainderExtension δ (h p) n (z p n)) ∧
                (∀ p n, ‖z p n‖ ≤ (2 * ρ) * (1 / 2 : ℝ) ^ n) := by
  obtain ⟨C, hC, hlinear⟩ := continuous_torusLinearStep_discrete T A hA
  obtain ⟨σ, Llip, hσ, hσδ, hLlip, hlip⟩ := exists_cutoffRemainder_small_lipschitz
    a B δ (1 / (128 * (C + 1))) ha hB hδ (by positivity)
  let ρ := σ / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have h2ρ : 2 * ρ = σ := by dsimp [ρ]; ring
  obtain ⟨Llin, ζ, π, D, R, hinv, hR, hζc, hπc, hdata⟩ := hlinear (1 / 128) (by norm_num)
  obtain ⟨Lforce, _, hforce⟩ := exists_cutoffResidual_small_scale a (C * B) (ρ / 8) ha (by positivity)
  let L₀ := max Llin (max Llip Lforce)
  have hL₀lip : Llip ≤ L₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hL₀lin : Llin ≤ L₀ := le_max_left _ _
  have hL₀force : Lforce ≤ L₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hL₀pos : 0 < L₀ := lt_of_lt_of_le zero_lt_one (hLlip.trans hL₀lip)
  let ε := B * L₀ ^ (-2 - a)
  have hε : 0 ≤ ε := mul_nonneg hB (Real.rpow_nonneg hL₀pos.le _)
  have hεsmall : C * ε ≤ ρ / 8 := by
    simpa only [ε, ← mul_assoc] using hforce L₀ hL₀force
  refine ⟨C, hC, ρ, hρ, by rw [h2ρ]; exact hσδ, L₀, ζ, π, ?_, hπc,
    (fun L hL n => ⟨(hdata L (hL₀lin.trans hL)).2.1 n,
      (hdata L (hL₀lin.trans hL)).2.2.1 n⟩),
    (fun L hL => (hdata L (hL₀lin.trans hL)).1), ?_⟩
  · intro n
    apply (hζc n).mono
    intro L hL
    exact hL₀lin.trans hL
  intro P _ L hLc hL h hhc hl hz w hwc hwb hker
  have hd (p : P) := hdata (L p) (hL₀lin.trans (hL p))
  have hZc (n : ℕ) : Continuous (fun p => ζ (L p) n) :=
    (hζc n).comp_continuous hLc (fun p => hL₀lin.trans (hL p))
  have hZjoint (n : ℕ) : Continuous (fun q : P × F => ζ (L q.1) n q.2) :=
    ((hZc n).comp continuous_fst).clm_apply continuous_snd
  have hPjoint (n : ℕ) : Continuous (fun q : P × FourierL2 => π (L q.1) n q.2) :=
    (hπc n).comp ((hLc.comp continuous_fst).prodMk continuous_snd)
  have hAjoint (n : ℕ) : Continuous
      (fun q : P × FourierL2 => A (expandingDiscreteRadius (L q.1) T n) q.2) :=
    hAc.comp ((((continuous_expandingDiscreteRadius T n).comp hLc).comp
      continuous_fst).prodMk continuous_snd)
  have hpow (p : P) : (L p).1 ^ (-2 - a) ≤ L₀ ^ (-2 - a) :=
    Real.rpow_le_rpow_of_nonpos hL₀pos (hL p) (by linarith)
  have hsmall (p : P) : ‖w p‖ + 2 * (C * ε) ≤ ρ / 2 := by
    linarith [hwb p]
  have hLip : ∀ p n v u, ‖v‖ ≤ 2 * ρ → ‖u‖ ≤ 2 * ρ →
      ‖cutoffRemainderExtension δ (h p) n v - cutoffRemainderExtension δ (h p) n u‖ ≤
        (1 / (128 * (C + 1))) * ‖v - u‖ := by
    intro p n v u hv hu
    have hh := cutoffRemainderExtension_lipschitz a (L p).1 T δ σ B
      (lt_of_lt_of_le zero_lt_one (L p).2) T.2 ha hσ hσδ hB (h p) (hl p)
      n v u (by rwa [← h2ρ]) (by rwa [← h2ρ])
    exact hh.trans (mul_le_mul_of_nonneg_right
      (hlip (L p).1 (hL₀lip.trans (hL p))) (norm_nonneg _))
  have hZero : ∀ p n, ‖cutoffRemainderExtension δ (h p) n 0‖ ≤
      ε * (Real.exp (-(2 + a) * T / 2)) ^ n := by
    intro p n
    apply (cutoffRemainderExtension_zero_bound a (L p).1 T δ B
      (lt_of_lt_of_le zero_lt_one (L p).2) hδ.le (h p) (hz p) n).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpow p) hB) (by positivity)
  obtain ⟨z, hzc, hz0, hzstep, hzn⟩ := exists_continuous_stableGraph_small_remainder
    (fun p => ζ (L p)) (fun p => π (L p))
    (fun p n => A (expandingDiscreteRadius (L p) T n)) D R hR hinv
    (fun p => (hd p).1) (fun p => (hd p).2.2.2.2.1) (fun p => (hd p).2.2.2.2.2.1)
    hZjoint hPjoint hAjoint C ρ ε (Real.exp (-(2 + a) * T / 2)) hC hρ.le hε
    (Real.exp_nonneg _) hratio (fun p => (hd p).2.1) (fun p => (hd p).2.2.1)
    (fun p => (hd p).2.2.2.1) (fun p => (hd p).2.2.2.2.2.2)
    (fun p => cutoffRemainderExtension δ (h p))
    (continuous_cutoffRemainderExtension_on_ball δ (2 * ρ) (h2ρ ▸ hσδ) h hhc)
    hLip hZero w hwc hker hsmall
  refine ⟨z, hzc, hz0, hzstep, fun p n => (hzn p n).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith [hsmall p]

end DefocusingNLS

end OAI
