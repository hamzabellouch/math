import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.ContinuousTorusCoordinateData
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableSmallRemainderContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffRemainderContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableEndpointCoordinateBound

namespace OAI

/-! # Continuous stable sequences with prescribed torus coordinates -/

open scoped NNReal

universe u

namespace DefocusingNLS

local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem exists_continuous_coordinateStable_sequence
    {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    (a δ B : ℝ) (ha : 0 < a) (hδ : 0 < δ) (hB : 0 ≤ B)
    (T : ℝ≥0) (hratio : 2 * Real.exp (-(2 + a) * T / 2) ≤ 1)
    (A : Radius → FourierL2 →L[ℝ] FourierL2)
    (hAc : Continuous (fun q : Radius × FourierL2 => A q.1 q.2))
    (κ : Radius → FourierL2 →L[ℝ] F)
    (hA : HasContinuousTorusCoordinateData (F := F) T A κ)
    (ν : ℝ) (hν : 0 < ν) :
    ∃ K : ℝ, 0 < K ∧ ∃ C : ℝ, 0 < C ∧ ∃ ρ : ℝ, 0 < ρ ∧ 2 * ρ ≤ δ ∧
      ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ,
      ∃ ζ : Radius → ℕ → F →L[ℝ] FourierL2,
      ∃ π : Radius → ℕ → FourierL2 →L[ℝ] F,
        (∀ L n, π L n = K • κ (expandingDiscreteRadius L T n)) ∧
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
                (∀ p n, ‖z p n‖ ≤ (2 * ρ) * (1 / 2 : ℝ) ^ n) ∧
                (∀ p n, ‖z p n‖ ≤ (4 * (‖w p‖ + 2 * η)) * (1 / 2 : ℝ) ^ n) ∧
                (∀ p, ‖π (L p) 0 (z p 0)‖ ≤ ν * (‖w p‖ + 2 * η) + 2 * η) := by
  obtain ⟨K, hK, C, hC, hlinear⟩ := continuous_torusCoordinateData_discrete T A κ hA
  let κ₀ := min (1 / (128 * (C + 1))) (ν / (16 * C))
  let τ := min (1 / 128) (ν / 16)
  have hκ₀ : 0 < κ₀ := lt_min (by positivity) (by positivity)
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hκsmall : κ₀ ≤ 1 / (128 * (C + 1)) := min_le_left _ _
  have hτsmall : τ ≤ 1 / 128 := min_le_left _ _
  have hflat : τ + C * κ₀ ≤ ν / 8 := by
    have hkν : C * κ₀ ≤ ν / 16 := by
      apply (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le).trans_eq
      field_simp [hC.ne']
    have htν : τ ≤ ν / 16 := min_le_right _ _
    linarith
  obtain ⟨σ, Llip, hσ, hσδ, hLlip, hlip⟩ := exists_cutoffRemainder_small_lipschitz
    a B δ κ₀ ha hB hδ hκ₀
  let ρ := σ / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have h2ρ : 2 * ρ = σ := by dsimp [ρ]; ring
  obtain ⟨Llin, ζ, π, hκ, D, R, hinv, hR, hζc, hπc, hdata⟩ := hlinear τ hτ
  have hRD : ∀ v, R (D v) = v := finiteCoordinate_rightInverse_leftInverse D R hinv
  refine ⟨K, hK, C, hC, ρ, hρ, by rw [h2ρ]; exact hσδ, ?_⟩
  intro η hη
  obtain ⟨Lforce, _, hforce⟩ := exists_cutoffResidual_small_scale a (C * B) (min (ρ / 8) η) ha (lt_min (by positivity) hη)
  let L₀ := max Llin (max Llip Lforce)
  have hL₀lip : Llip ≤ L₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hL₀lin : Llin ≤ L₀ := le_max_left _ _
  have hL₀force : Lforce ≤ L₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hL₀pos : 0 < L₀ := lt_of_lt_of_le zero_lt_one (hLlip.trans hL₀lip)
  let ε := B * L₀ ^ (-2 - a)
  have hε : 0 ≤ ε := mul_nonneg hB (Real.rpow_nonneg hL₀pos.le _)
  have hεmin : C * ε ≤ min (ρ / 8) η := by
    simpa only [ε, ← mul_assoc] using hforce L₀ hL₀force
  have hεsmall : C * ε ≤ ρ / 8 := hεmin.trans (min_le_left _ _)
  have hεη : C * ε ≤ η := hεmin.trans (min_le_right _ _)
  refine ⟨L₀, ζ, π, hκ, ?_, hπc,
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
  have hLipSharp : ∀ p n v u, ‖v‖ ≤ 2 * ρ → ‖u‖ ≤ 2 * ρ →
      ‖cutoffRemainderExtension δ (h p) n v - cutoffRemainderExtension δ (h p) n u‖ ≤
        κ₀ * ‖v - u‖ := by
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
    (fun p => (hd p).2.2.2.1)
    (fun p n => ((hd p).2.2.2.2.2.2 n).trans hτsmall)
    (fun p => cutoffRemainderExtension δ (h p))
    (continuous_cutoffRemainderExtension_on_ball δ (2 * ρ) (h2ρ ▸ hσδ) h hhc)
    (fun p n v u hv hu => (hLipSharp p n v u hv hu).trans
      (mul_le_mul_of_nonneg_right hκsmall (norm_nonneg _)))
    hZero w hwc hker hsmall
  refine ⟨z, hzc, hz0, hzstep, ?_, ?_, ?_⟩
  · intro p n
    apply (hzn p n).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith [hsmall p]
  · intro p n
    apply (hzn p n).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith

  · intro p
    have hzball (n : ℕ) : ‖z p n‖ ≤ 2 * ρ := by
      apply (hzn p n).trans
      have hpow : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      calc
        _ ≤ 4 * (‖w p‖ + 2 * (C * ε)) :=
          mul_le_of_le_one_right (by positivity) hpow
        _ ≤ 2 * ρ := by linarith [hsmall p]
    have hhpoint : ∀ n : ℕ,
        ‖cutoffRemainderExtension δ (h p) n (z p n) -
          cutoffRemainderExtension δ (h p) n 0‖ ≤ κ₀ * ‖z p n‖ := by
      intro n
      simpa only [sub_zero] using
        hLipSharp p n (z p n) 0 (hzball n) (by simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hρ.le)
    have hb := stableEndpoint_coordinate_bound (E := FourierL2) (F := F) (π (L p))
      (fun n => A (expandingDiscreteRadius (L p) T n)) D R hRD hR
      C τ κ₀ ε (4 * (‖w p‖ + 2 * (C * ε)))
      (Real.exp (-(2 + a) * T / 2)) hC.le hτ.le hκ₀.le hε (by positivity)
      (Real.exp_nonneg _) (by linarith) (fun n => (hd p).2.2.1 n)
      ((hd p).2.2.2.2.2.2) (cutoffRemainderExtension δ (h p)) (z p)
      (hzstep p) (hzn p) hhpoint (hZero p)
    apply hb.trans
    calc
      _ ≤ 2 * ((ν / 8) * (4 * (‖w p‖ + 2 * (C * ε))) + C * ε) := by
        gcongr
      _ = ν * (‖w p‖ + 2 * (C * ε)) + 2 * (C * ε) := by ring
      _ ≤ ν * (‖w p‖ + 2 * η) + 2 * η := by gcongr

end DefocusingNLS

end OAI
