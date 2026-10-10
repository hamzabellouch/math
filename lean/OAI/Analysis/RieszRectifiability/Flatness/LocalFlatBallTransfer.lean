import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.BilateralBeta
import OAI.Analysis.RieszRectifiability.Limits.BilateralSupportConvergence

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem local_bilateral_tube_transfer {d : ℕ} (A B S : Set (Ambient d)) (hA : A.Nonempty)
    (a b : Ambient d) (r δ η : ℝ) (hr : 0 < r) (hδ : δ ≤ r / 4) (hη : η ≤ r / 4)
    (hab : dist b a ≤ r / 4)
    (hBA : ∀ x ∈ ball a (2 * r), x ∈ B → infDist x A < δ)
    (hAB : ∀ x ∈ ball a (2 * r), x ∈ A → infDist x B < δ)
    (hAS : ∀ x ∈ ball a (2 * r), x ∈ A → infDist x S < η)
    (hSA : ∀ x ∈ ball a (2 * r), x ∈ S → infDist x A < η) :
    (∀ x ∈ ball b r, x ∈ B → infDist x S < η + δ) ∧
    (∀ x ∈ ball b r, x ∈ S → infDist x B < η + δ) := by
  have hxlarge (x : Ambient d) (hx : x ∈ ball b r) : x ∈ ball a (2 * r) := by
    have ht := dist_triangle x b a
    have hx' : dist x b < r := hx
    change dist x a < 2 * r
    linarith
  have hylarge (x y : Ambient d) (hx : x ∈ ball b r) (hxy : dist x y < r / 4) :
      y ∈ ball a (2 * r) := by
    have ht := dist_triangle y x a
    have ht' := dist_triangle x b a
    have hx' : dist x b < r := hx
    rw [dist_comm y x] at ht
    change dist y a < 2 * r
    linarith
  constructor
  · intro x hx hxB
    obtain ⟨y, hyA, hxy⟩ := (infDist_lt_iff hA).mp (hBA x (hxlarge x hx) hxB)
    have hyS := hAS y (hylarge x y hx (hxy.trans_le hδ)) hyA
    exact infDist_le_infDist_add_dist.trans_lt (by linarith : infDist y S + dist x y < η + δ)
  · intro x hx hxS
    obtain ⟨y, hyA, hxy⟩ := (infDist_lt_iff hA).mp (hSA x (hxlarge x hx) hxS)
    have hyB := hAB y (hylarge x y hx (hxy.trans_le hη)) hyA
    exact infDist_le_infDist_add_dist.trans_lt (by linarith : infDist y B + dist x y < η + δ)

theorem compactTestConvergence_local_flat_ball {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ t : ℝ, AdmissibleRadius (μ j) t →
      ENNReal.ofReal (t ^ n / C) ≤ (μ j) (ball x t))
    (hdiam : ∀ t : ℝ, 0 < t → ∀ᶠ j in atTop, ENNReal.ofReal t ≤ ediam (μ j).support)
    (a : Ambient d) (ha : a ∈ ν.support) (b : ℕ → Ambient d) (hb : Tendsto b atTop (𝓝 a))
    (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (hforward : ∀ x ∈ ball a (2 * r), x ∈ ν.support →
      infDist x (S : Set (Ambient d)) < ε * r / 16)
    (hreverse : ∀ x ∈ ball a (2 * r), x ∈ S → infDist x ν.support < ε * r / 16) :
    ∀ᶠ j in atTop, bilateralBeta n (μ j) (b j) r < ε := by
  have hmargin : ε * r / 16 ≤ r / 4 := by nlinarith [mul_le_mul_of_nonneg_right hε1 hr.le]
  filter_upwards [compactTestConvergence_bilateral_support_tubes n μ ν hlocal C hC hlower hdiam
    a (2 * r) (ε * r / 16) (by positivity),
    Metric.tendsto_nhds.mp hb (r / 4) (by positivity)] with j hj hjb
  have ht := local_bilateral_tube_transfer ν.support (μ j).support (S : Set (Ambient d))
    ⟨a, ha⟩ a (b j) r (ε * r / 16) (ε * r / 16) hr hmargin hmargin hjb.le
    hj.1 hj.2 hforward hreverse
  apply bilateralBeta_lt_of_support_tubes n (μ j) (b j) r ε hr hε S hS
  · intro x hx hxs
    have hp := ht.1 x hx hxs
    nlinarith [mul_pos hε hr]
  · intro x hx hxs
    have hp := ht.2 x hx hxs
    nlinarith [mul_pos hε hr]

end

end RieszRectifiability

end OAI
