import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.DyadicTimes

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X]

def DynamicActionBound (μ : Time → Measure X) (C : ℝ) : Prop :=
  ∀ s t : Time, ∃ π : Measure (Curve X), IsProbabilityMeasure π ∧
    π.map (fun γ => γ timeZero) = μ s ∧ π.map (fun γ => γ timeOne) = μ t ∧
    (∫⁻ γ, kineticAction γ ∂π) ≤ ENNReal.ofReal (C*(dist s t)^2)

omit [CompactSpace X] [BorelSpace X] [Nonempty X] in
lemma DynamicActionBound.half {μ : Time → Measure X} {C : ℝ}
    (h : DynamicActionBound μ C) : DynamicActionBound (μ ∘ halfTime) (C/4) := by
  intro s t
  obtain ⟨π,hπ,h0,h1,hb⟩ := h (halfTime s) (halfTime t)
  refine ⟨π,hπ,h0,h1,?_⟩
  convert hb using 1
  rw [dist_halfTime]
  congr 1
  ring

omit [CompactSpace X] [BorelSpace X] [Nonempty X] in
lemma DynamicActionBound.right {μ : Time → Measure X} {C : ℝ}
    (h : DynamicActionBound μ C) : DynamicActionBound (μ ∘ rightTime) (C/4) := by
  intro s t
  obtain ⟨π,hπ,h0,h1,hb⟩ := h (rightTime s) (rightTime t)
  refine ⟨π,hπ,h0,h1,?_⟩
  convert hb using 1
  rw [dist_rightTime]
  congr 1
  ring

lemma exists_grid_plan (n : ℕ) (μ : Time → Measure X) {C : ℝ} (hC : 0 ≤ C)
    (h : DynamicActionBound μ C) :
    ∃ π : Measure (Curve X), IsProbabilityMeasure π ∧
      (∀ t ∈ dyadicTimes n, π.map (fun γ => γ t) = μ t) ∧
      (∫⁻ γ, kineticAction γ ∂π) ≤ ENNReal.ofReal C := by
  induction n generalizing μ C with
  | zero =>
    obtain ⟨π,hπ,h0,h1,hb⟩ := h timeZero timeOne
    refine ⟨π,hπ,?_,?_⟩
    · intro t ht
      rcases ht with rfl | ht
      · exact h0
      · have he : t = timeOne := ht
        simpa only [he] using h1
    · simpa only [Subtype.dist_eq, timeZero, timeOne, Real.dist_eq, zero_sub,
        abs_neg, abs_one, one_pow, mul_one] using hb
  | succ n ih =>
    obtain ⟨πL,hL,hLm,hLA⟩ := ih (μ ∘ halfTime) (div_nonneg hC (by norm_num)) h.half
    obtain ⟨πR,hR,hRm,hRA⟩ := ih (μ ∘ rightTime) (div_nonneg hC (by norm_num)) h.right
    let := hL
    let := hR
    have hmatch : πL.map (fun γ => γ timeOne) = πR.map (fun γ => γ timeZero) := by
      rw [hLm _ (one_mem_dyadicTimes n),hRm _ (zero_mem_dyadicTimes n)]
      simp only [Function.comp_apply,halfTime_one_eq_rightTime_zero]
    obtain ⟨π,hπ,hπL,hπR,hπA⟩ := exists_join_plan πL πR hmatch
    refine ⟨π,hπ,?_,?_⟩
    · intro t ht
      rcases ht with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
      · rw [hπL,hLm _ hs]; rfl
      · rw [hπR,hRm _ hs]; rfl
    · calc
        (∫⁻ γ, kineticAction γ ∂π) ≤ 2*((∫⁻ γ, kineticAction γ ∂πL)+(∫⁻ γ, kineticAction γ ∂πR)) := hπA
        _ ≤ 2*(ENNReal.ofReal (C/4)+ENNReal.ofReal (C/4)) := mul_le_mul_right (add_le_add hLA hRA) 2
        _ = ENNReal.ofReal C := by
          rw [← ENNReal.ofReal_add (div_nonneg hC (by norm_num)) (div_nonneg hC (by norm_num)),
            ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
          congr 1
          ring

end WeakHessian

end
end InlinedFile0

end OAI
