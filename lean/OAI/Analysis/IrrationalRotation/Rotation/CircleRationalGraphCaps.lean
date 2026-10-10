import OAI.Analysis.IrrationalRotation.Rotation.ParameterCircleReindex
import OAI.Analysis.IrrationalRotation.Analysis.InfiniteRatioCaps
import OAI.Analysis.IrrationalRotation.Analysis.RationalGraphTrimming

namespace OAI

noncomputable section
open MeasureTheory Function
open scoped BigOperators

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem ae_flattened_floor_support :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
      HasFiniteSupport (fun i : ℕ => Int.floor
        (CircleWeights.coordinate p.flattenedFrequency i x +
          (k : ℝ) * CircleWeights.phase θ p.flattenedFrequency i)) := by
  have hq : ∀ i, p.flattenedFrequency i ≠ 0 := by
    intro i
    change (p.q (i + 1) : ℤ) ≠ 0
    exact_mod_cast (hp.q_pos (i + 1)).ne'
  have hs : Summable (CircleWeights.phase θ p.flattenedFrequency) := by
    change Summable (fun i : ℕ => Int.fract ((p.q (i + 1) : ℝ) * θ))
    exact hp.summable_phases
  exact CircleWeightSupport.ae_all_int_finite_floor_support
    p.flattenedFrequency hq (CircleWeights.phase θ p.flattenedFrequency)
    (CircleWeights.phase_nonneg θ p.flattenedFrequency) hs

theorem ae_all_rational_graph_floor_support :
    ∀ᵐ x ∂circleMeasure,
      (∀ k : ℤ, HasFiniteSupport (fun i : ℕ => Int.floor
        (CircleWeights.coordinate p.flattenedFrequency i x +
          (k : ℝ) * CircleWeights.phase θ p.flattenedFrequency i))) ∧
      ∀ (A : ℕ) (r : ℤ) (k : ℤ), HasFiniteSupport (fun i : ℕ => Int.floor
        (CircleWeights.coordinate p.flattenedFrequency i
          (x + (((r : ℝ) / (p.q A : ℝ) : ℝ) : Circle)) +
          (k : ℝ) * CircleWeights.phase θ p.flattenedFrequency i)) := by
  refine hp.ae_flattened_floor_support.and ?_
  apply ae_all_iff.mpr
  intro A
  apply ae_all_iff.mpr
  intro r
  have hmp : MeasurePreserving
      (fun x : Circle => x + (((r : ℝ) / (p.q A : ℝ) : ℝ) : Circle))
      circleMeasure circleMeasure := by
    change MeasurePreserving _ volume volume
    exact measurePreserving_add_right volume _
  let P : Circle → Prop := fun y => ∀ k : ℤ, HasFiniteSupport (fun i : ℕ =>
    Int.floor (CircleWeights.coordinate p.flattenedFrequency i y +
      (k : ℝ) * CircleWeights.phase θ p.flattenedFrequency i))
  have hP : ∀ᵐ y ∂circleMeasure, P y := hp.ae_flattened_floor_support
  exact hmp.quasiMeasurePreserving.ae (p := P) hP

theorem ae_rational_graph_ratio_cap :
    ∀ᵐ x ∂circleMeasure, ∀ (A : ℕ), 1 ≤ A → ∀ (r k : ℤ),
      p.floorCocycle θ k
          (x + (((r : ℝ) / (p.q A : ℝ) : ℝ) : Circle)) /
        p.floorCocycle θ k x ≤
          Real.exp (∑ i ∈ Finset.range (A - 1), p.flattenedCost i) := by
  filter_upwards [hp.ae_all_rational_graph_floor_support] with x hx
  intro A hA r k
  rw [hp.parameter_cocycle_eq_flattened, hp.parameter_cocycle_eq_flattened]
  apply CircleWeights.cocycle_ratio_cap_finite_exceptions θ
    p.flattenedFrequency p.flattenedCost k _ _ (Finset.range (A - 1))
    (fun i => (hp.flattenedCost_pos i).le) _ (hx.1 k) (hx.2 A r k)
  intro i hi
  have hAi : A ≤ i + 1 := by
    simp only [Finset.mem_range, not_lt] at hi
    omega
  have he := hp.trimming_coordinate_rational_translation hAi r x
  change p.coordinate (i + 1) x ≤ p.coordinate (i + 1)
    (x + (((r : ℝ) / (p.q A : ℝ) : ℝ) : Circle))
  exact le_of_eq he.symm

end Invariant233.CircleParameterLaws

end

end OAI
