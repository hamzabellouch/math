import OAI.GroupTheory.PolycyclicRecognition.Analysis.CellProfileRestriction
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TranslatedCellDomination
import Mathlib.MeasureTheory.Group.Measure

namespace OAI

/-! # The actual changed-center sampling law

The deterministic inclusion is isolated from its measure-theoretic use.
The conclusion concerns the translated and conjugated ordinary Haar cell,
with the exact volume ratio of the suffix cell.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- Independent smaller-cell and suffix sampling dominates the actual
nilpotent factor after changing the ambient basepoint. -/
theorem basepoint_cell_domination
    {N D : Type*} [Group N] [Group D] [MeasurableSpace N] [MeasurableMul₂ N]
    (φ : D →* MulAut N) (μ : Measure N) [μ.IsMulLeftInvariant]
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (ν : ProbabilityMeasure N) (A : Set N)
    (hA : ∀ᵐ a ∂(ν : Measure N), a ∈ A)
    (C B : Set N) (hC : MeasurableSet C) (hB : MeasurableSet B)
    (hC0 : μ C ≠ 0) (hCfin : μ C ≠ ∞) (hB0 : μ B ≠ 0) (hBfin : μ B ≠ ∞)
    (u : N) (d : D)
    (hcover : ∀ a₀ ∈ A, ∀ a ∈ C, (φ d a₀)⁻¹ * u⁻¹ * a ∈ B)
    (S : Set N) (hS : MeasurableSet S) :
    let K := (φ d) ⁻¹' B
    (cellProbabilityMeasure μ C hC0 hCfin : Measure N)
        ((fun a => φ d⁻¹ (u⁻¹ * a)) ⁻¹' S) ≤
      (μ B / μ C) * (ν : Measure N).prod
        (cellProbabilityMeasure μ K
          (by rw [(hφ d).measure_preimage hB.nullMeasurableSet]; exact hB0)
          (by rw [(hφ d).measure_preimage hB.nullMeasurableSet]; exact hBfin) : Measure N)
        {p | p.1 * p.2 ∈ S} := by
  dsimp only
  have hK0 : μ ((φ d) ⁻¹' B) ≠ 0 := by
    rw [(hφ d).measure_preimage hB.nullMeasurableSet]
    exact hB0
  have hKfin : μ ((φ d) ⁻¹' B) ≠ ∞ := by
    rw [(hφ d).measure_preimage hB.nullMeasurableSet]
    exact hBfin
  have h := translated_cell_domination ν A hA μ C ((φ d) ⁻¹' B)
    hC hC0 hCfin hK0 hKfin
    (fun a => φ d⁻¹ (u⁻¹ * a))
    ((hφ d⁻¹).measurable.comp (measurable_const.mul measurable_id))
    (fun a k => u * φ d (a * k)) (fun a k => a * k)
    (by
      intro a ha
      simpa only [Function.comp_def, map_mul, mul_assoc] using
        (measurePreserving_mul_left μ (u * φ d a)).comp (hφ d))
    (by
      intro a ha k hk
      change φ d k ∈ B
      have hc := hcover a ha (u * φ d (a * k)) hk
      simpa only [map_mul, mul_assoc, inv_mul_cancel_left] using hc)
    (measurable_fst.prodMk
      (measurable_const.mul ((hφ d).measurable.comp (measurable_fst.mul measurable_snd))))
    (by intro a k; simp)
    S hS
  rwa [(hφ d).measure_preimage hB.nullMeasurableSet] at h

/-- The conjugated suffix cell can be packaged as a probability law, with
any established upper bound for its exact Haar-volume ratio. -/
theorem exists_basepoint_cell_domination
    {N D : Type*} [Group N] [Group D] [MeasurableSpace N] [MeasurableMul₂ N]
    (φ : D →* MulAut N) (μ : Measure N) [μ.IsMulLeftInvariant]
    (hφ : ∀ d, MeasurePreserving (φ d) μ μ)
    (νA : ProbabilityMeasure N) (A : Set N)
    (hA : ∀ᵐ a ∂(νA : Measure N), a ∈ A)
    (C B : Set N) (hC : MeasurableSet C) (hB : MeasurableSet B)
    (hC0 : μ C ≠ 0) (hCfin : μ C ≠ ∞) (hB0 : μ B ≠ 0) (hBfin : μ B ≠ ∞)
    (u : N) (d : D)
    (hcover : ∀ a₀ ∈ A, ∀ a ∈ C, (φ d a₀)⁻¹ * u⁻¹ * a ∈ B)
    {K : ℝ≥0∞} (hratio : μ B / μ C ≤ K) :
    ∃ ν : ProbabilityMeasure N,
      (∀ᵐ k ∂(ν : Measure N), φ d k ∈ B) ∧
      ∀ S : Set N, MeasurableSet S →
      (cellProbabilityMeasure μ C hC0 hCfin : Measure N)
        ((fun a => φ d⁻¹ (u⁻¹ * a)) ⁻¹' S) ≤
      K * (νA : Measure N).prod (ν : Measure N) {p | p.1 * p.2 ∈ S} := by
  let Q := (φ d) ⁻¹' B
  have hQ : MeasurableSet Q := (hφ d).measurable hB
  have hQmass : μ Q = μ B := (hφ d).measure_preimage hB.nullMeasurableSet
  have hQ0 : μ Q ≠ 0 := hQmass ▸ hB0
  have hQfin : μ Q ≠ ∞ := hQmass ▸ hBfin
  let ν := cellProbabilityMeasure μ Q hQ0 hQfin
  refine ⟨ν, ?_, ?_⟩
  · exact ae_mem_cellProbabilityMeasure μ Q hQ hQ0 hQfin
  · intro S hS
    exact (basepoint_cell_domination φ μ hφ νA A hA C B hC hB
      hC0 hCfin hB0 hBfin u d hcover S hS).trans (mul_le_mul' hratio le_rfl)

end PolycyclicRecognition

end

end OAI
