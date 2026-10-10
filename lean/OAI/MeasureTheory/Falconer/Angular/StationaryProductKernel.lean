import OAI.MeasureTheory.Falconer.Angular.StationaryProductIntegral

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem stationary_product_radial_bound {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) (n : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ {f g : ℝ → ℂ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
    ∀ {C E D R d₁ d₂ : ℝ}, 0 ≤ C → 0 ≤ E → 1 ≤ D → 0 < R → 0 < d₁ → 0 < d₂ →
    D^2 ≤ R*d₁ → D^2 ≤ R*d₂ →
    (∀ l ≤ 2*n, ∀ t, ‖iteratedDeriv l f t‖ ≤ C*D^l) →
    (∀ l ≤ 2*n, ∀ t, ‖iteratedDeriv l g t‖ ≤ E*D^l) →
    ‖R⁻¹ • (∫ r : ℝ, Ψ (r/R) •
      (fullCircleStationaryExpansion (r*d₁) f n * fullCircleStationaryExpansion (r*d₂) g n))‖ ≤
      H*C*E*((R*d₁)^(-1/2:ℝ)*(R*d₂)^(-1/2:ℝ))/(1+R*|d₁-d₂|)^2 := by
  choose H hH hb using fun j k => signedStationaryRadial_kernel hΨ hs j k
  let Htot := ∑ p ∈ stationarySignedIndices n, ∑ q ∈ stationarySignedIndices n, H p.2 q.2
  refine ⟨Htot,Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun q _ => hH p.2 q.2)),?_⟩
  intro f g hf hg C E D R d₁ d₂ hC hE hD hR h1 h2 hDA hDB hbf hbg
  rw [stationary_product_radial_integral hΨ hs hf hg n hR h1 h2]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ stationarySignedIndices n, ∑ q ∈ stationarySignedIndices n,
        H p.2 q.2*C*E*((R*d₁)^(-1/2:ℝ)*(R*d₂)^(-1/2:ℝ))/(1+R*|d₁-d₂|)^2 := by
      apply Finset.sum_le_sum
      intro p hp
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q hq
      have hj : p.2 ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hp).2)
      have hk : q.2 ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hq).2)
      exact hb p.2 q.2 hf hg hC hE hD hR h1 h2 hDA hDB p.1 q.1 0 0
        (stationarySign p.1) (stationarySign q.1)
        (by cases p.1 <;> simp [stationarySign]) (by cases q.1 <;> simp [stationarySign])
        (fun l hl => hbf l (hl.trans (Nat.mul_le_mul_left 2 hj)))
        (fun l hl => hbg l (hl.trans (Nat.mul_le_mul_left 2 hk)))
    _ = _ := by simp only [Htot,Finset.sum_mul,Finset.sum_div]

end PlanarFalconer

end OAI
