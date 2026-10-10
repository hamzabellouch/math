import OAI.NumberTheory.Ostmann.QuadraticCenter.UniformQuadraticGrid
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMultiples

namespace OAI

/-! # The same fixed grid covers all sampled outer divisors -/

namespace Ostmann

open Filter
open scoped SchwartzMap

theorem eventual_uniform_outer_divisor_grid (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ θ R : ℝ,
      0 ≤ θ → θ ≤ 1 → 1 ≤ R → R ≤ Real.exp (14 * T) →
      ∃ j ∈ quadraticParameterGrid (Real.exp (14 * T)) (Real.exp (-200 * T)),
        0 ≤ quadraticGridPhase (Real.exp (-200 * T)) j ∧
        quadraticGridPhase (Real.exp (-200 * T)) j ≤ 1 ∧
        1 ≤ quadraticGridScale (Real.exp (-200 * T)) j ∧
        quadraticGridScale (Real.exp (-200 * T)) j ≤ Real.exp (14 * T) ∧
        |R - quadraticGridScale (Real.exp (-200 * T)) j| ≤ Real.exp (-200 * T) ∧
        ∀ (q s P : ℕ) [NeZero q] (g : ZMod q → ℂ) (B : ℝ) (a : ZMod q) (v h₀ : ℝ),
          (∀ x, ‖g x‖ ≤ B) → 1 ≤ q → (q : ℝ) ≤ Real.exp T →
          1 ≤ s → (s : ℝ) ≤ Real.exp (14 * T) →
          0 < P → (P : ℝ) ≤ Real.exp (7 * T) →
          1 ≤ v → v ≤ Real.exp T → 0 ≤ B → B ≤ Real.exp T →
          ‖positiveQuadraticMultiples g a (h₀ + θ) Φ R v s P -
            positiveQuadraticMultiples g a (h₀ + quadraticGridPhase (Real.exp (-200 * T)) j) Φ
              (quadraticGridScale (Real.exp (-200 * T)) j) v s P‖ ≤ Real.exp (-128 * T) := by
  filter_upwards [eventual_uniform_quadratic_grid H Φ hH hΦ] with T hgrid
  intro θ R hθ0 hθ1 hR hRR
  obtain ⟨j, hj, hjθ0, hjθ1, hjR1, hjRmax, hjRδ, hpoint⟩ := hgrid θ R hθ0 hθ1 hR hRR
  refine ⟨j, hj, hjθ0, hjθ1, hjR1, hjRmax, hjRδ, ?_⟩
  intro q s P _ g B a v h₀ hg hq1 hq hs1 hs hP hPU hv1 hv hB0 hB
  have hsp1 : 1 ≤ s * P ^ 2 := Nat.mul_pos hs1 (pow_pos hP _)
  have hsp : ((s * P ^ 2 : ℕ) : ℝ) ≤ Real.exp (28 * T) := by
    push_cast
    calc
      _ ≤ Real.exp (14 * T) * (Real.exp (7 * T)) ^ 2 := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; norm_num; ring
  have hp := hpoint q (s * P ^ 2) g B a v h₀ hg hq1 hq hsp1 hsp hv1 hv hB0 hB
  rw [positiveQuadraticMultiples_eq g a (h₀ + θ) Φ R v s P hP (by linarith) (by linarith),
    positiveQuadraticMultiples_eq g a _ Φ _ v s P hP (by linarith) (by linarith),
    ← mul_sub, norm_mul, norm_inv, Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (Nat.cast_nonneg P))).trans
  exact mul_le_of_le_one_left (Real.exp_nonneg _) (inv_le_one_of_one_le₀ (by exact_mod_cast hP))

end Ostmann

end OAI
