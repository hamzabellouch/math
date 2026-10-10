import OAI.GroupTheory.PolycyclicRecognition.Geometry.ChartContraction
import Mathlib.Analysis.Normed.Group.Basic

namespace OAI

/-! # Uniform contractions about arbitrary centers -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

variable (G : Type*) [MetricSpace G]

/-- The quantitative contraction data used by the interpolation algorithm.
It is constructed from coordinates below, rather than assumed to supply
a quasi-isometry representative. -/
structure ControlledContraction where
  contract : G → ℝ → G → G
  zero : ∀ p z, contract p 0 z = p
  one : ∀ p z, contract p 1 z = z
  bounds : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 1 ≤ C ∧
    ∀ p z w : G, dist z p ≤ R → dist w p ≤ R →
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (contract p s z) (contract p t w) ≤
        C * (|s - t| + min s t * dist z w)

namespace ControlledContraction

variable {G}

theorem dist_center_le (c : ControlledContraction G) {R C : ℝ}
    (hC : ∀ p z w : G, dist z p ≤ R → dist w p ≤ R →
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (c.contract p s z) (c.contract p t w) ≤
        C * (|s - t| + min s t * dist z w))
    {p z : G} (hz : dist z p ≤ R) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    dist (c.contract p s z) p ≤ C * s := by
  have h := hC p z z hz hz s hs 0 ⟨le_rfl, zero_le_one⟩
  simpa only [c.zero, sub_zero, abs_of_nonneg hs.1, min_eq_right hs.1,
    dist_self, mul_zero, add_zero] using h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] [Group G] [ProperSpace G] [IsIsometricSMul G G]

/-- Left translation of radial contraction makes the same constants work
about every center of a left-invariant metric. -/
def ofChart (φ : E ≃ₜ G) (hφ : φ 0 = 1)
    (hf : LocallyLipschitz φ) (hb : LocallyLipschitz φ.symm) : ControlledContraction G where
  contract p s z := p * chartContraction φ s (p⁻¹ * z)
  zero p z := by simp [hφ]
  one p z := by simp
  bounds R hR := by
    obtain ⟨C, hC, htime, hspace⟩ := chartContraction_bounds φ hφ hf hb hR
    refine ⟨C, hC, ?_⟩
    intro p z w hz hw s hs t ht
    have hzp : p⁻¹ * z ∈ closedBall (1 : G) R := by
      change dist (p⁻¹ * z) 1 ≤ R
      calc
        _ = dist z p := by simpa using dist_mul_left p⁻¹ z p
        _ ≤ R := hz
    have hwp : p⁻¹ * w ∈ closedBall (1 : G) R := by
      change dist (p⁻¹ * w) 1 ≤ R
      calc
        _ = dist w p := by simpa using dist_mul_left p⁻¹ w p
        _ ≤ R := hw
    rw [dist_mul_left]
    rcases le_total s t with hst | hts
    · have h₁ := hspace s hs _ hzp _ hwp
      have h₂ := htime s hs t ht _ hwp
      rw [dist_mul_left] at h₁
      have h := dist_triangle (chartContraction φ s (p⁻¹ * z))
        (chartContraction φ s (p⁻¹ * w)) (chartContraction φ t (p⁻¹ * w))
      rw [min_eq_left hst]
      linarith
    · have h₁ := htime s hs t ht _ hzp
      have h₂ := hspace t ht _ hzp _ hwp
      rw [dist_mul_left] at h₂
      have h := dist_triangle (chartContraction φ s (p⁻¹ * z))
        (chartContraction φ t (p⁻¹ * z)) (chartContraction φ t (p⁻¹ * w))
      rw [min_eq_right hts]
      linarith

end ControlledContraction
end PolycyclicRecognition

end

end OAI
