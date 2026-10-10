import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGridErrorBound

namespace OAI

/-! # A fixed polynomial-size grid with negligible approximation error -/

namespace Ostmann

open Filter
open scoped SchwartzMap

theorem quadraticParameterGrid_exponential_card (T : ℝ) (hT : 1 ≤ T) :
    ((quadraticParameterGrid (Real.exp (14 * T)) (Real.exp (-200 * T))).card : ℝ) ≤
      Real.exp (416 * T) := by
  have hT0 : 0 ≤ T := by linarith
  have h1 : (1 : ℝ) ≤ Real.exp (200 * T) := Real.one_le_exp_iff.mpr (by positivity)
  have h2 : (1 : ℝ) ≤ Real.exp (214 * T) := Real.one_le_exp_iff.mpr (by positivity)
  have htwo : (2 : ℝ) ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  have hfour : (4 : ℝ) ≤ Real.exp (2 * T) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 2
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] using hh
  apply (quadraticParameterGrid_card_le _ _ (Real.exp_nonneg _) (Real.exp_pos _)).trans
  have hinv : 1 / Real.exp (-200 * T) = Real.exp (200 * T) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  have hratio : Real.exp (14 * T) / Real.exp (-200 * T) = Real.exp (214 * T) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hinv, hratio]
  calc
    _ ≤ (2 * Real.exp (200 * T)) * (2 * Real.exp (214 * T)) := by gcongr <;> linarith
    _ = 4 * Real.exp (414 * T) := by
      rw [mul_mul_mul_comm, ← Real.exp_add,
        show 200 * T + 214 * T = 414 * T by ring]
      norm_num
    _ ≤ Real.exp (2 * T) * Real.exp (414 * T) := mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem eventual_quadratic_grid_approximation (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (q s : ℕ) [NeZero q] (g : ZMod q → ℂ)
      (B : ℝ) (a : ZMod q) (θ R v : ℝ),
      (∀ x, ‖g x‖ ≤ B) → 1 ≤ q → (q : ℝ) ≤ Real.exp T →
      1 ≤ s → (s : ℝ) ≤ Real.exp (28 * T) →
      1 ≤ v → v ≤ Real.exp T → 0 ≤ B → B ≤ Real.exp T →
      0 ≤ θ → θ ≤ 1 → 1 ≤ R → R ≤ Real.exp (14 * T) →
      ∃ j ∈ quadraticParameterGrid (Real.exp (14 * T)) (Real.exp (-200 * T)),
        0 ≤ quadraticGridPhase (Real.exp (-200 * T)) j ∧
        quadraticGridPhase (Real.exp (-200 * T)) j ≤ 1 ∧
        1 ≤ quadraticGridScale (Real.exp (-200 * T)) j ∧
        quadraticGridScale (Real.exp (-200 * T)) j ≤ Real.exp (14 * T) ∧
        ‖positiveQuadraticSum g a θ Φ R v s -
          positiveQuadraticSum g a (quadraticGridPhase (Real.exp (-200 * T)) j) Φ
            (quadraticGridScale (Real.exp (-200 * T)) j) v s‖ ≤ Real.exp (-128 * T) := by
  filter_upwards [Real.tendsto_exp_atTop.eventually_ge_atTop (2 : ℝ),
    Real.tendsto_exp_atTop.eventually_ge_atTop (2 * Real.pi),
    Real.tendsto_exp_atTop.eventually_ge_atTop H,
    Real.tendsto_exp_atTop.eventually_ge_atTop (SchwartzMap.seminorm ℝ 0 0 Φ),
    Real.tendsto_exp_atTop.eventually_ge_atTop (SchwartzMap.seminorm ℝ 0 1 Φ)] with T hX hpi hHX hΦ0 hΦ1
  intro q s _ g B a θ R v hg hq1 hq hs1 hs hv1 hv hB0 hB hθ0 hθ1 hR hRR
  have hs' : (s : ℝ) ≤ (Real.exp T) ^ 28 := by simpa only [← Real.exp_nat_mul, Nat.cast_ofNat] using hs
  have hR' : Real.exp (14 * T) ≤ (Real.exp T) ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
  have herror := quadraticGridError_le_power (Real.exp T) q s B (Real.exp (14 * T)) v H Φ
    hX hpi hq1 hq hs1 hs' hv1 hv hB0 hB (Real.exp_nonneg _) hR' hH hHX hΦ0 hΦ1
  obtain ⟨j, hj, hjθ0, hjθ1, hjR1, hjRmax, hjerr⟩ := positiveQuadraticSum_grid_approximation
    g B hg a θ Φ R (Real.exp (14 * T)) v H (Real.exp (-200 * T)) s
    hθ0 hθ1 hR hRR (by linarith) hH (by omega) (Real.exp_pos _) hΦ
  refine ⟨j, hj, hjθ0, hjθ1, hjR1, hjRmax, hjerr.trans ?_⟩
  calc
    _ ≤ (Real.exp T) ^ 72 * Real.exp (-200 * T) :=
      mul_le_mul_of_nonneg_right herror (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; norm_num; ring

end Ostmann

end OAI
