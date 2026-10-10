import OAI.Probability.InvariantIsing.Cavity.CavityCutoffLimit

namespace OAI

/-! The order of the two remaining limits: choose a large spatial radius,
then a small denominator floor, then pass to the system-size limit. -/

noncomputable section
open Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_cutoff_floor_comparison
    (f : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (u v : ℕ → ℝ → ℕ → ℝ) (a e : ℕ → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ j, 0 < a j) (he : Tendsto e atTop (𝓝 0))
    (hfu : ∀ j δ, 0 < δ → ∀ n, |f j n - u j δ n| ≤ C*δ/a j + e j)
    (hvg : ∀ j δ, 0 < δ → ∀ n, |v j δ n - g n| ≤ C*δ/a j + e j)
    (huv : ∀ j δ, 0 < δ → Tendsto (fun n => u j δ n - v j δ n) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ n in atTop, |f j n - g n| < ε := by
  intro ε hε
  filter_upwards [he.eventually (Iio_mem_nhds (show (0 : ℝ) < ε/6 by positivity))] with j hj
  have haj := ha j
  let δ := ε*a j/(12*(C+1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hsmall : C*δ/a j ≤ ε/12 := by
    have heq : C*δ/a j = (ε/12)*(C/(C+1)) := by
      dsimp only [δ]
      field_simp [haj.ne', show C+1 ≠ 0 by linarith]
    rw [heq]
    have hc : C/(C+1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq (mul_one _)
  filter_upwards [(huv j δ hδ).eventually
    (Metric.ball_mem_nhds 0 (show 0 < ε/3 by positivity))] with n hn
  rw [Real.dist_eq,sub_zero] at hn
  have h₁ := hfu j δ hδ n
  have h₂ := hvg j δ hδ n
  have htri := abs_sub_le (f j n) (u j δ n) (g n)
  have htri' := abs_sub_le (u j δ n) (v j δ n) (g n)
  linarith

theorem cavity_limit_of_eventual_cutoff_comparison
    (f g : ℕ → ℝ) (cut : ℕ → ℕ → ℝ)
    (hcut : ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ n in atTop, |f n - cut j n| < ε)
    (hmatch : ∀ ε > 0, ∀ᶠ j in atTop, ∀ᶠ n in atTop, |cut j n - g n| < ε) :
    Tendsto (fun n => f n - g n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j,hj₁,hj₂⟩ := ((hcut (ε/2) (by positivity)).and
    (hmatch (ε/2) (by positivity))).exists
  filter_upwards [hj₁,hj₂] with n hn₁ hn₂
  rw [Real.dist_eq,sub_zero]
  exact (abs_sub_le (f n) (cut j n) (g n)).trans_lt (by linarith)

end InvariantIsing

end

end OAI
