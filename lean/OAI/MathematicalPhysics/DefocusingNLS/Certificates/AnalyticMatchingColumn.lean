import OAI.MathematicalPhysics.DefocusingNLS.Certificates.NormalizedMatchingColumns
import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowParameterHolomorphy

namespace OAI

/-! # The analytic boundary column and its normalized tail representation -/

open Matrix

namespace DefocusingNLS

/-- The derivative-shift formula gives an explicitly analytic boundary column. -/
noncomputable def slowBoundaryColumn (q : ℂ) (m : ℕ) (s : ℂ) : Fin 2 → ℂ :=
  ![regularizedSlowSolution q m (-s), q * regularizedSlowSolution (q + 1) (m + 1) (-s)]

theorem slowBoundaryColumn_eq_jet (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    slowBoundaryColumn q m s =
      ![regularizedSlowSolution q m (-s), -deriv (regularizedSlowSolution q m) (-s)] := by
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr (fun h => hsim (by simp [h]))
  have hd := (hasDerivAt_regularizedSlowSolution_shift_closed q m (-s) hq
    (by simp [hsre]) hs0).deriv
  simp [slowBoundaryColumn, hd]

theorem differentiableAt_slowBoundaryColumn (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    DifferentiableAt ℂ (fun z => slowBoundaryColumn z m s) q := by
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr (fun h => hsim (by simp [h]))
  have hq' : -1 < (q + 1).re := by change -1 < q.re + 1; linarith
  have h₀ := differentiableAt_regularizedSlowSolution_parameter_closed q m (-s) hq
    (by simp [hsre]) hs0
  have h₁ := differentiableAt_regularizedSlowSolution_parameter_closed (q + 1) (m + 1)
    (-s) hq' (by simp [hsre]) hs0
  apply differentiableAt_pi.mpr
  intro i
  fin_cases i
  · change DifferentiableAt ℂ (fun z => regularizedSlowSolution z m (-s)) q
    exact h₀
  · change DifferentiableAt ℂ (fun z => z * regularizedSlowSolution (z + 1) (m + 1) (-s)) q
    convert! differentiableAt_id.mul (h₁.comp q (differentiableAt_id.add_const 1)) using 1

theorem analyticOnNhd_slowBoundaryColumn (m : ℕ) (s : ℂ)
    (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    AnalyticOnNhd ℂ (fun q => slowBoundaryColumn q m s) {q : ℂ | -1 < q.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro q hq
  exact (differentiableAt_slowBoundaryColumn q m s hq hsre hsim).differentiableWithinAt

theorem slowBoundaryColumn_ne_zero (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    slowBoundaryColumn q m s ≠ 0 := by
  rw [slowBoundaryColumn_eq_jet q m s hq hsre hsim]
  intro hz
  have h₀ := congrFun hz 0
  have h₁ := congrFun hz 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h₀ h₁
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr (fun h => hsim (by simp [h]))
  exact (regularizedSlowSolution_jet_nonzero q m (-s) hq (by simp [hsre]) hs0).elim
    (fun h => h h₀) (fun h => h (neg_eq_zero.mp h₁))

theorem normalizedMatching_tail_disk (σ : ℝ) (ℓ K : ℕ) (q s : ℂ)
    (hσ : -(1 / 32 : ℝ) ≤ σ) (hK : 3 ≤ K)
    (hq : q.re = σ + (ℓ : ℝ) / 2) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    normalizedMatchingC q (ℓ + 6) s K ≠ 0 ∧
      Complex.normSq (normalizedMatchingB q (ℓ + 6) s K /
        normalizedMatchingC q (ℓ + 6) s K + s / ((ℓ : ℝ) + 5 : ℂ)) <
          Complex.normSq (s / ((ℓ : ℝ) + 5 : ℂ)) := by
  have hq' : -1 < q.re := by rw [hq]; linarith [Nat.cast_nonneg (α := ℝ) ℓ]
  have hp := shiftedPochhammer_ne_zero q (K - 1) hq'
  obtain ⟨hC, hd⟩ := normalizedSlow_tail_disk σ ℓ K q s hσ hK hq hsre hsim
  refine ⟨div_ne_zero hC hp, ?_⟩
  have he : normalizedMatchingB q (ℓ + 6) s K / normalizedMatchingC q (ℓ + 6) s K =
      normalizedSlowB q (ℓ + 6) s K / normalizedSlowC q (ℓ + 6) s K := by
    unfold normalizedMatchingB normalizedMatchingC
    field_simp
  rwa [he]

/-- The backward image of the ratio column differs from the true analytic
boundary column by the explicit nonzero tail scalar. -/
theorem normalizedMatching_ratio_column (q : ℂ) (M K : ℕ) (s : ℂ)
    (hK : 0 < K) (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0)
    (hC : normalizedMatchingC q (M + 1) s K ≠ 0) :
    backwardProduct M s q K *ᵥ
      ![normalizedMatchingB q (M + 1) s K / normalizedMatchingC q (M + 1) s K, 1] =
        (normalizedMatchingC q (M + 1) s K)⁻¹ • slowBoundaryColumn q (M + 1) s := by
  have hv : ![normalizedMatchingB q (M + 1) s K / normalizedMatchingC q (M + 1) s K, 1] =
      (normalizedMatchingC q (M + 1) s K)⁻¹ •
        ![normalizedMatchingB q (M + 1) s K, normalizedMatchingC q (M + 1) s K] := by
    ext i
    fin_cases i <;> simp [div_eq_mul_inv, mul_comm, hC]
  rw [hv, Matrix.mulVec_smul, normalizedMatching_backwardProduct q M K s hK hq hsre hsim,
    slowBoundaryColumn_eq_jet q (M + 1) s hq hsre hsim]

end DefocusingNLS

end OAI
