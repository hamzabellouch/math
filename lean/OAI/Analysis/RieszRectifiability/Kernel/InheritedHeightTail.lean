import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.InheritedHeightMoments
import OAI.Analysis.RieszRectifiability.Kernel.InfiniteHeightTail

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem inherited_height_tail_bound {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ℕ) (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (R : ℝ) (hR : 0 < R) (M : ℕ) (hM : 2 * R * ((Q : ℝ) + 1) ≤ M)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    (C B : ℝ) (hg : GlobalUpperGrowth m C ν) (hCB : C * 2 ^ m ≤ B)
    (w : ℕ → Ambient d → ℝ) (f : Ambient d → ℝ) (hfm : Measurable f)
    (hf : ∀ H, MemLp f 2 (ν.restrict (boundedProjectionRegion π (e 0) K H)))
    (hlimit : ∀ H, Tendsto (fun j => ∫ x, w j x ^ 2
      ∂(μ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop
      (𝓝 (∫ x, f x ^ 2 ∂ν.restrict (boundedProjectionRegion π (e 0) K H))))
    (hw : ∀ k j, MemLp (w j) 2 ((μ j).restrict
      (ball (e 0) ((((K : ℝ) + 1) * ((M : ℝ) + 1)) * (2 : ℝ) ^ k))))
    (b : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hbound : ∀ k, ∀ᶠ j in atTop,
      (∫ x in ball (e 0) ((((K : ℝ) + 1) * ((M : ℝ) + 1)) * (2 : ℝ) ^ k), w j x ^ 2 ∂μ j) ≤
        (B * (R * 2 ^ k) ^ m) * ((R * 2 ^ k) * b ^ k) ^ 2) :
    ∀ ℓ, IntegrableOn (fun y => |f y| * inverseDistancePow (m + 2) (e 0) y)
      (closedExterior (e 0) (R * 2 ^ ℓ)) ν ∧
      (∫ y in closedExterior (e 0) (R * 2 ^ ℓ), |f y| * inverseDistancePow (m + 2) (e 0) y ∂ν) ≤
        ((B / R) / (1 - b / 2)) * (b / 2) ^ ℓ := by
  have hmoments := inherited_annular_second_moments e π K Q hπ hleft R M hM μ ν w f
    hf hlimit hw (fun k => (B * (R * 2 ^ k) ^ m) * ((R * 2 ^ k) * b ^ k) ^ 2) hbound
  intro ℓ
  have ht := infinite_weighted_height_tail_shifted m C B ν hg hCB (e 0) R hR f hfm
    (fun k => (hmoments k).1) 1 b (by norm_num) hb0 hb2
    (fun k => by simpa only [one_mul] using! (hmoments k).2) ℓ
  simpa only [mul_one] using! ht

end

end RieszRectifiability

end OAI
