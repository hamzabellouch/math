import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphWeightedSource
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffNonlinearStep

namespace OAI

/-! # The actual cutoff-step estimates in weighted sequence form

These adapters use exactly the remainder bounds proved for the sampled
nonlinear step.  The exponent along `L exp(nM/2)` is geometric, and the small
Lipschitz constant is obtained by first reducing the state ball and then
increasing the starting radius.  The step maps themselves are not assumed
to be spectral projections or a stable graph.
-/

open scoped BoundedContinuousFunction

namespace DefocusingNLS

theorem expandingRadius_discrete_residual (a L M : ℝ) (hL : 0 < L) (n : ℕ) :
    (expandingRadius L ((n : ℝ) * M)) ^ (-2 - a) =
      L ^ (-2 - a) * (Real.exp (-(2 + a) * M / 2)) ^ n := by
  rw [expandingRadius_residual_power a L _ hL, ← Real.exp_nat_mul]
  congr 2
  ring

theorem exists_cutoffStep_geometric_ratio (a : ℝ) (ha : 0 < a) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      2 * Real.exp (-(2 + a) * M / 2) ≤ 1 / 2 := by
  let M₀ := 2 * Real.log 4 / (2 + a)
  have hd : 0 < 2 + a := by linarith
  have hl : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hM₀ : 0 < M₀ := by dsimp [M₀]; positivity
  refine ⟨M₀, hM₀, ?_⟩
  intro M hM
  have heq : (2 + a) * M₀ = 2 * Real.log 4 := by
    dsimp [M₀]
    field_simp [hd.ne']
  have hp : Real.log 4 ≤ (2 + a) * M / 2 := by
    have h := mul_le_mul_of_nonneg_left hM hd.le
    nlinarith
  have he := Real.exp_le_exp.mpr (neg_le_neg hp)
  have hv : Real.exp (-Real.log 4) = 1 / 4 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    norm_num
  rw [hv] at he
  have hi : -(2 + a) * M / 2 = -((2 + a) * M / 2) := by ring
  rw [hi]
  linarith

noncomputable def cutoffRemainderExtension {V : Type*} [NormedAddCommGroup V]
    (δ : ℝ) (h : ℕ → {v : V // ‖v‖ ≤ δ} → V) (n : ℕ) (v : V) : V :=
  if hv : ‖v‖ ≤ δ then h n ⟨v, hv⟩ else 0

theorem cutoffRemainderExtension_lipschitz {V : Type*} [NormedAddCommGroup V]
    (a L M δ ρ C : ℝ) (hL : 0 < L) (hM : 0 ≤ M) (ha : 0 < a)
    (hρ : 0 < ρ) (hρδ : ρ ≤ δ) (hC : 0 ≤ C)
    (h : ℕ → {v : V // ‖v‖ ≤ δ} → V)
    (hlip : ∀ n d, 0 < d → d ≤ δ → ∀ v w,
      ‖v.1‖ ≤ d → ‖w.1‖ ≤ d → ‖h n v - h n w‖ ≤
        C * (d + (expandingRadius L ((n : ℝ) * M)) ^ (-2 - a)) * ‖v.1 - w.1‖) :
    ∀ n v w, ‖v‖ ≤ ρ → ‖w‖ ≤ ρ →
      ‖cutoffRemainderExtension δ h n v - cutoffRemainderExtension δ h n w‖ ≤
        (C * (ρ + L ^ (-2 - a))) * ‖v - w‖ := by
  intro n v w hv hw
  have hgeo : (Real.exp (-(2 + a) * M / 2)) ^ n ≤ 1 :=
    pow_le_one₀ (Real.exp_nonneg _) (Real.exp_le_one_iff.mpr (by
      have hp := mul_nonneg (show 0 ≤ 2 + a by linarith) hM
      nlinarith))
  have hpow : (expandingRadius L ((n : ℝ) * M)) ^ (-2 - a) ≤ L ^ (-2 - a) := by
    rw [expandingRadius_discrete_residual a L M hL n]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hL.le _) hgeo
  have hvδ := hv.trans hρδ
  have hwδ := hw.trans hρδ
  simp only [cutoffRemainderExtension, dite_eq_left hvδ, dite_eq_left hwδ]
  exact (hlip n ρ hρ hρδ ⟨v, hvδ⟩ ⟨w, hwδ⟩ hv hw).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl hpow) hC) (norm_nonneg _))

theorem cutoffRemainderExtension_zero_bound {V : Type*} [NormedAddCommGroup V]
    (a L M δ C : ℝ) (hL : 0 < L) (hδ : 0 ≤ δ)
    (h : ℕ → {v : V // ‖v‖ ≤ δ} → V)
    (hzero : ∀ n z, z.1 = 0 → ‖h n z‖ ≤
      C * (expandingRadius L ((n : ℝ) * M)) ^ (-2 - a)) :
    ∀ n, ‖cutoffRemainderExtension δ h n 0‖ ≤
      (C * L ^ (-2 - a)) * (Real.exp (-(2 + a) * M / 2)) ^ n := by
  intro n
  have h0 : ‖(0 : V)‖ ≤ δ := by simpa only [norm_zero] using hδ
  rw [cutoffRemainderExtension, dite_eq_left h0]
  simpa only [expandingRadius_discrete_residual a L M hL n, mul_assoc] using
    hzero n ⟨0, h0⟩ rfl

theorem exists_cutoffRemainder_small_lipschitz (a C δ η : ℝ)
    (ha : 0 < a) (hC : 0 ≤ C) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ ρ L₀ : ℝ, 0 < ρ ∧ ρ ≤ δ ∧ 1 ≤ L₀ ∧
      ∀ L : ℝ, L₀ ≤ L → C * (ρ + L ^ (-2 - a)) ≤ η := by
  let ρ := min δ (η / (4 * (C + 1)))
  have hρ : 0 < ρ := lt_min hδ (by positivity)
  have hρδ : ρ ≤ δ := min_le_left _ _
  have hρsmall : C * ρ ≤ η / 4 := by
    have h := (le_div_iff₀ (show 0 < 4 * (C + 1) by positivity)).mp
      (show ρ ≤ η / (4 * (C + 1)) from min_le_right _ _)
    nlinarith [mul_nonneg hC hρ.le]
  obtain ⟨L₀, hL₀, hlarge⟩ := exists_cutoffResidual_small_scale a C (η / 2) ha (by positivity)
  refine ⟨ρ, L₀, hρ, hρδ, hL₀, ?_⟩
  intro L hL
  have h := hlarge L hL
  nlinarith

end DefocusingNLS

end OAI
