import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGridRates

namespace OAI

/-! # One grid point simultaneously approximates every coefficient -/

namespace Ostmann

open Filter
open scoped SchwartzMap

/-- The quantifier order matters: the chosen grid point depends only on
the original phase and scale, and works for all moduli and kernels. -/
theorem eventual_uniform_quadratic_grid (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ θ R : ℝ,
      0 ≤ θ → θ ≤ 1 → 1 ≤ R → R ≤ Real.exp (14 * T) →
      ∃ j ∈ quadraticParameterGrid (Real.exp (14 * T)) (Real.exp (-200 * T)),
        0 ≤ quadraticGridPhase (Real.exp (-200 * T)) j ∧
        quadraticGridPhase (Real.exp (-200 * T)) j ≤ 1 ∧
        1 ≤ quadraticGridScale (Real.exp (-200 * T)) j ∧
        quadraticGridScale (Real.exp (-200 * T)) j ≤ Real.exp (14 * T) ∧
        |R - quadraticGridScale (Real.exp (-200 * T)) j| ≤ Real.exp (-200 * T) ∧
        ∀ (q s : ℕ) [NeZero q] (g : ZMod q → ℂ) (B : ℝ) (a : ZMod q) (v h₀ : ℝ),
          (∀ x, ‖g x‖ ≤ B) → 1 ≤ q → (q : ℝ) ≤ Real.exp T →
          1 ≤ s → (s : ℝ) ≤ Real.exp (28 * T) →
          1 ≤ v → v ≤ Real.exp T → 0 ≤ B → B ≤ Real.exp T →
          ‖positiveQuadraticSum g a (h₀ + θ) Φ R v s -
            positiveQuadraticSum g a (h₀ + quadraticGridPhase (Real.exp (-200 * T)) j) Φ
              (quadraticGridScale (Real.exp (-200 * T)) j) v s‖ ≤ Real.exp (-128 * T) := by
  filter_upwards [Real.tendsto_exp_atTop.eventually_ge_atTop (2 : ℝ),
    Real.tendsto_exp_atTop.eventually_ge_atTop (2 * Real.pi),
    Real.tendsto_exp_atTop.eventually_ge_atTop H,
    Real.tendsto_exp_atTop.eventually_ge_atTop (SchwartzMap.seminorm ℝ 0 0 Φ),
    Real.tendsto_exp_atTop.eventually_ge_atTop (SchwartzMap.seminorm ℝ 0 1 Φ)] with T hX hpi hHX hΦ0 hΦ1
  intro θ R hθ0 hθ1 hR hRR
  obtain ⟨j, hj, hjθ0, hjθ, hjR1, hjR, hjθδ, hjRδ⟩ :=
    quadraticParameterGrid_covers (Real.exp (14 * T)) (Real.exp (-200 * T)) θ R
      (Real.exp_pos _) hθ0 hθ1 hR hRR
  refine ⟨j, hj, hjθ0, hjθ.trans hθ1, hjR1, hjR.trans hRR, hjRδ.le, ?_⟩
  intro q s _ g B a v h₀ hg hq1 hq hs1 hs hv1 hv hB0 hB
  have hs' : (s : ℝ) ≤ (Real.exp T) ^ 28 := by simpa only [← Real.exp_nat_mul, Nat.cast_ofNat] using hs
  have hR' : Real.exp (14 * T) ≤ (Real.exp T) ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
  have herror := quadraticGridError_le_power (Real.exp T) q s B (Real.exp (14 * T)) v H Φ
    hX hpi hq1 hq hs1 hs' hv1 hv hB0 hB (Real.exp_nonneg _) hR' hH hHX hΦ0 hΦ1
  have hpoint := positiveQuadraticSum_parameter_sub_bound g B hg a (h₀ + θ)
    (h₀ + quadraticGridPhase (Real.exp (-200 * T)) j) Φ R
    (quadraticGridScale (Real.exp (-200 * T)) j) (Real.exp (14 * T)) v H
    (Real.exp (-200 * T)) s hR hjR1 hRR (hjR.trans hRR) (by linarith) hH (by omega)
    (by simpa only [add_sub_add_left_eq_sub] using hjθδ.le) hjRδ.le hΦ
  apply hpoint.trans
  calc
    _ ≤ (Real.exp T) ^ 72 * Real.exp (-200 * T) :=
      mul_le_mul_of_nonneg_right herror (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; norm_num; ring

end Ostmann

end OAI
