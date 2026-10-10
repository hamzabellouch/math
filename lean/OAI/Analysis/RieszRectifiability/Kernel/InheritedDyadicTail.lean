import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.DyadicSourceMoments

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem limiting_height_tail_from_dyadic_source {ι : Type*} [Fintype ι] {d : ℕ} (m : ℕ)
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    (C : ℝ) (hg : GlobalUpperGrowth m C ν)
    (w : ℕ → Ambient d → ℝ) (f : Ambient d → ℝ) (hfm : Measurable f)
    (hf : ∀ H, MemLp f 2 (ν.restrict (boundedProjectionRegion π (e 0) K H)))
    (hlimit : ∀ H, Tendsto (fun j => ∫ x, w j x ^ 2
      ∂(μ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop
      (𝓝 (∫ x, f x ^ 2 ∂ν.restrict (boundedProjectionRegion π (e 0) K H))))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (D b : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hw : ∀ l j, MemLp (w j) 2 ((μ j).restrict (ball (e 0) ((2 : ℝ) ^ l))))
    (hbound : ∀ j l, l ≤ N j → (∫ x in ball (e 0) ((2 : ℝ) ^ l), w j x ^ 2 ∂μ j) ≤
      D * ((2 : ℝ) ^ l) ^ m * ((2 : ℝ) ^ l * b ^ l) ^ 2) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun x => |f x| * inverseDistancePow (m + 2) (e 0) x)
      (closedExterior (e 0) R) ν := by
  obtain ⟨J, hJ⟩ := exists_nat_ge (2 * R * ((Q : ℝ) + 1))
  obtain ⟨B, hB, hballs, hb⟩ := comparable_ball_moments_from_dyadic_control m μ (e 0) w N hN D b
    hw hbound (((K : ℝ) + 1) * ((J : ℝ) + 1)) R (C * 2 ^ m) hR
  have h := (inherited_height_tail_bound m e π K Q hπ hleft R hR J hJ μ ν C B hg hB
    w f hfm hf hlimit hballs b hb0 hb2 hb 0).1
  simpa only [pow_zero, mul_one] using! h

end

end RieszRectifiability

end OAI
