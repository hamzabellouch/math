import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableEndpointContinuity

namespace OAI

/-! # Continuous stable endpoints from the quantitative small-remainder bounds -/

namespace DefocusingNLS

variable {P E F : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_continuous_stableGraph_small_remainder
    (ζ : P → ℕ → F →L[ℝ] E) (π : P → ℕ → E →L[ℝ] F)
    (A : P → ℕ → E →L[ℝ] E) (D R : F →L[ℝ] F)
    (hR : ‖R‖ ≤ 1) (hinv : ∀ v, D (R v) = v)
    (hπζ : ∀ p n v, π p n (ζ p n v) = v)
    (hA : ∀ p n, ‖stableProjectedBlock (ζ p n) (ζ p (n + 1))
      (π p n) (π p (n + 1)) (A p n)‖ ≤ 1 / 8)
    (hB : ∀ p n, ‖stableMixedBlock (ζ p n) (ζ p (n + 1)) (π p (n + 1)) (A p n)‖ ≤ 1 / 16)
    (hζc : ∀ n, Continuous (fun q : P × F => ζ q.1 n q.2))
    (hπc : ∀ n, Continuous (fun q : P × E => π q.1 n q.2))
    (hAc : ∀ n, Continuous (fun q : P × E => A q.1 n q.2))
    (C ρ ε r : ℝ) (hC : 0 < C) (hρ : 0 ≤ ρ) (hε : 0 ≤ ε)
    (hr : 0 ≤ r) (hrsmall : 2 * r ≤ 1)
    (hζ : ∀ p n, ‖ζ p n‖ ≤ 1) (hπ : ∀ p n, ‖π p n‖ ≤ C)
    (hP : ∀ p n, ‖stableFrameProjection (ζ p n) (π p n)‖ ≤ C)
    (he : ∀ p n, ‖(π p (n + 1)).comp (A p n) - D.comp (π p n)‖ ≤ 1 / 128)
    (h : P → ℕ → E → E)
    (hhc : ∀ n, Continuous (fun q : P × {v : E // ‖v‖ ≤ 2 * ρ} => h q.1 n q.2.1))
    (hlip : ∀ p n v u, ‖v‖ ≤ 2 * ρ → ‖u‖ ≤ 2 * ρ →
      ‖h p n v - h p n u‖ ≤ (1 / (128 * (C + 1))) * ‖v - u‖)
    (hzero : ∀ p n, ‖h p n 0‖ ≤ ε * r ^ n)
    (w : P → E) (hw : Continuous w) (hwker : ∀ p, π p 0 (w p) = 0)
    (hsmall : ∀ p, ‖w p‖ + 2 * (C * ε) ≤ ρ / 2) :
    ∃ z : P → ℕ → E, (∀ n, Continuous (fun p => z p n)) ∧
      (∀ p, stableFrameProjection (ζ p 0) (π p 0) (z p 0) = w p) ∧
      (∀ p n, z p (n + 1) = A p n (z p n) + h p n (z p n)) ∧
      (∀ p n, ‖z p n‖ ≤ (4 * (‖w p‖ + 2 * (C * ε))) * (1 / 2 : ℝ) ^ n) := by
  have hκ : 0 ≤ 1 / (128 * (C + 1)) := by positivity
  have hCκ : C * (1 / (128 * (C + 1))) ≤ 1 / 128 := by
    rw [one_div, ← div_eq_mul_inv]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hN (p : P) (n : ℕ) (v u : E × F) (hv : ‖v‖ ≤ ρ) (hu : ‖u‖ ≤ ρ) :=
    stableFramePointSources_lipschitz (ζ p) (π p) (A p) D (h p) 1 C C (1 / 128)
      (1 / (128 * (C + 1))) ρ (2 * ρ) zero_le_one hC.le hC.le (by norm_num) hκ
      (hζ p) (fun n => hP p (n + 1)) (fun n => hπ p (n + 1)) (he p)
      (by ring_nf; rfl) (hlip p) n v u hv hu
  have hz (p : P) (n : ℕ) := stableFramePointSources_zero (ζ p) (π p) (A p) D (h p)
    C C ε r hC.le hC.le (fun n => hP p (n + 1)) (fun n => hπ p (n + 1)) (hzero p) n
  have hhc' : ∀ n, Continuous
      (fun q : P × {v : E // ‖v‖ ≤ (1 + (1 : ℝ)) * ρ} => h q.1 n q.2.1) := by
    rw [show (1 + (1 : ℝ)) * ρ = 2 * ρ by ring]
    exact hhc
  obtain ⟨z, hzc, hz0, hzstep, hzb⟩ := exists_continuous_stableGraph_endpoints ζ π A D R
    hR hinv hπζ hA hB hζc hπc hAc h w hw hwker ρ (C * ε) 1 r hρ
    (mul_nonneg hC.le hε) zero_le_one hr hrsmall hζ hhc'
    (fun p n v u hv hu => (hN p n v u hv hu).1.trans
      (mul_le_mul_of_nonneg_right (by nlinarith : C * (1 / (128 * (C + 1))) * (1 + 1) ≤ 1 / 16)
        (norm_nonneg _)))
    (fun p n v u hv hu => (hN p n v u hv hu).2.trans
      (mul_le_mul_of_nonneg_right (by nlinarith :
        (1 / 128 + C * (1 / (128 * (C + 1)))) * (1 + 1) ≤ 1 / 16) (norm_nonneg _)))
    (fun p n => (hz p n).1) (fun p n => (hz p n).2) hsmall
  refine ⟨z, hzc, hz0, hzstep, fun p n => (hzb p n).trans_eq ?_⟩
  ring

end DefocusingNLS

end OAI
