import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

namespace OAI

open scoped ComplexConjugate ENNReal lp

namespace InvariantProjection

theorem cocycle_two_ratio_bounds
    (Fx Fy : ℤ → ℝ) (hFx : ∀ k, 0 < Fx k) (hFy : ∀ k, 0 < Fy k)
    (hx : Antitone Fx) (hy : Antitone Fy)
    (hxy : ∀ k, Fy k / Fx k ≤ 1) (n : ℕ) (v : ℤ) :
    0 < Fy ((n : ℤ) + v) / Fx v ∧
      Fy ((n : ℤ) + v) / Fx v ≤ min (Fy v / Fx v)
        (Fy ((n : ℤ) + v) / Fx ((n : ℤ) + v)) ∧
      min (Fy v / Fx v) (Fy ((n : ℤ) + v) / Fx ((n : ℤ) + v)) ≤ 1 := by
  have hv : v ≤ (n : ℤ) + v := by omega
  refine ⟨div_pos (hFy _) (hFx _), le_min ?_ ?_, (min_le_left _ _).trans (hxy v)⟩
  · exact div_le_div_of_nonneg_right (hy hv) (le_of_lt (hFx v))
  · exact div_le_div_of_nonneg_left (le_of_lt (hFy _)) (hFx _) (hx hv)

theorem l2_reindexed_absolute_products (ξ γ : ℓ²(ℤ, ℂ)) (e : ℤ ≃ ℤ) :
    (Summable fun v : ℤ => ‖ξ v‖ * ‖γ (e v)‖) ∧
      (∑' v : ℤ, ‖ξ v‖ * ‖γ (e v)‖) ≤ ‖ξ‖ * ‖γ‖ := by
  let γe : ℓ²(ℤ, ℂ) := ⟨fun v => γ (e v), by
    apply memℓp_gen
    exact e.summable_iff.mpr ((lp.memℓp γ).summable (by norm_num))⟩
  have hnorm : ‖γe‖ = ‖γ‖ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.tsum_eq (fun v => ‖γ v‖ ^ (2 : ℝ≥0∞).toReal)
  simpa only [hnorm] using lp.tsum_mul_le_mul_norm
    (p := 2) (q := 2) (by simpa using Real.HolderConjugate.two_two) ξ γe

theorem l2_reindexed_multiplier_bound (ξ γ : ℓ²(ℤ, ℂ)) (e : ℤ ≃ ℤ)
    (r : ℤ → ℝ) (hr : ∀ v, 0 ≤ r v ∧ r v ≤ 1) :
    (Summable fun v : ℤ => ‖(r v : ℂ) * ξ v * conj (γ (e v))‖) ∧
      (∑' v : ℤ, ‖(r v : ℂ) * ξ v * conj (γ (e v))‖) ≤ ‖ξ‖ * ‖γ‖ := by
  have hbase := l2_reindexed_absolute_products ξ γ e
  have hbound (v : ℤ) :
      ‖(r v : ℂ) * ξ v * conj (γ (e v))‖ ≤ ‖ξ v‖ * ‖γ (e v)‖ := by
    simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hr v).1]
    calc
      r v * ‖ξ v‖ * ‖γ (e v)‖ ≤ 1 * ‖ξ v‖ * ‖γ (e v)‖ := by gcongr; exact (hr v).2
      _ = _ := by ring
  have hs := Summable.of_nonneg_of_le (fun v => norm_nonneg _) hbound hbase.1
  exact ⟨hs, (Summable.tsum_le_tsum hbound hs hbase.1).trans hbase.2⟩

theorem cocycle_convolution_absolute
    (Fx Fy : ℤ → ℝ) (hFx : ∀ k, 0 < Fx k) (hFy : ∀ k, 0 < Fy k)
    (hx : Antitone Fx) (hy : Antitone Fy)
    (hxy : ∀ k, Fy k / Fx k ≤ 1) (n : ℕ) (ξ γ : ℓ²(ℤ, ℂ)) :
    (Summable fun v : ℤ =>
      ‖((Fy ((n : ℤ) + v) / Fx v : ℝ) : ℂ) * ξ v * conj (γ ((n : ℤ) + v))‖) ∧
    (∑' v : ℤ,
      ‖((Fy ((n : ℤ) + v) / Fx v : ℝ) : ℂ) * ξ v * conj (γ ((n : ℤ) + v))‖)
      ≤ ‖ξ‖ * ‖γ‖ := by
  apply l2_reindexed_multiplier_bound ξ γ (Equiv.addLeft (n : ℤ))
    (fun v => Fy ((n : ℤ) + v) / Fx v)
  intro v
  have h := cocycle_two_ratio_bounds Fx Fy hFx hFy hx hy hxy n v
  exact ⟨h.1.le, h.2.1.trans h.2.2⟩

theorem convolution_coefficient_factorization
    (Fx Fy : ℤ → ℝ) (ξ γ : ℤ → ℂ) (n v : ℤ) :
    (ξ v / (Fx v : ℂ)) * ((Fy (n + v) : ℂ) * conj (γ (n + v))) =
      ((Fy (n + v) / Fx v : ℝ) : ℂ) * ξ v * conj (γ (n + v)) := by
  push_cast
  ring

end InvariantProjection

end OAI
