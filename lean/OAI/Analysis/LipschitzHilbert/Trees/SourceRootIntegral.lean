import OAI.Analysis.LipschitzHilbert.Trees.SourceRootCells
import OAI.Analysis.LipschitzHilbert.Trees.SourceAmplitudeMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-! The root estimates integrate the exact boundary-weighted packet sum.
At most two nonempty eligible roots occur in the bounded slope range,
so this final spatial sum has only an absolute factor. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem sourceBoundarySum_integral_le (μ : Measure X)
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (hwmeas : ∀ t, Measurable (weight t)) {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (hv : ∀ s, Measurable (fun x => value x s))
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (heligible : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s))
    (a start B : ℝ) (hB : 0 ≤ B)
    (hslope : ∀ t ∈ tops, start ≤ slope t ∧ slope t ≤ start+g.rootWidth)
    (hrootInt : ∀ c ∈ g.sourceRootCells tops slope precision cutoff,
      Integrable (fun x => ‖((g.mass tops slope precision cutoff weight 0 c x^a:ℝ):ℂ) •
        g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
          (value x) (fun _ => (a:ℂ)) a x 0 c‖) μ)
    (hrootBound : ∀ c ∈ g.sourceRootCells tops slope precision cutoff,
      (∫ x, ‖((g.mass tops slope precision cutoff weight 0 c x^a:ℝ):ℂ) •
        g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
          (value x) (fun _ => (a:ℂ)) a x 0 c‖ ∂μ) ≤ B) :
    let W := fun x => ∑ s ∈ packets,
      ((g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap
        (stop s) (assigned s) a x:ℝ):ℂ) • value x s
    Integrable (fun x => ‖W x‖) μ ∧ (∫ x, ‖W x‖ ∂μ) ≤ 2*B := by
  intro W
  let roots := g.sourceRootCells tops slope precision cutoff
  let f := fun c x => ((g.mass tops slope precision cutoff weight 0 c x^a:ℝ):ℂ) •
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
      (value x) (fun _ => (a:ℂ)) a x 0 c
  have hfmeas (c : ℤ) : Measurable (f c) :=
    ((((g.measurable_mass tops slope precision cutoff weight hwmeas 0 c).pow_const a).complex_ofReal).smul
      (g.measurable_sourcePacketAmplitude tops slope precision cutoff weight hwmeas K gap
        packets assigned stop value hv (fun _ => (a:ℂ)) a 0 c))
  have hfi (c : ℤ) (hc : c ∈ roots) : Integrable (f c) μ :=
    (integrable_norm_iff (hfmeas c).aestronglyMeasurable).mp (hrootInt c hc)
  have hi : Integrable (fun x => ∑ c ∈ roots, f c x) μ := integrable_finsetSum roots hfi
  have hni : Integrable (fun x => ∑ c ∈ roots, ‖f c x‖) μ :=
    integrable_finsetSum roots (fun c hc => (hfi c hc).norm)
  have heq : W = fun x => ∑ c ∈ roots, f c x := by
    funext x
    exact g.sourceBoundarySum_root_decomposition tops slope precision cutoff weight hp hw
      hK gap packets assigned stop (value x) hassigned heligible a x
  rw [heq]
  refine ⟨hi.norm,?_⟩
  calc
    _ ≤ ∫ x, ∑ c ∈ roots, ‖f c x‖ ∂μ :=
      integral_mono hi.norm hni (fun x => norm_sum_le _ _)
    _ = ∑ c ∈ roots, ∫ x, ‖f c x‖ ∂μ :=
      integral_finsetSum roots (fun c hc => (hfi c hc).norm)
    _ ≤ ∑ _c ∈ roots, B := Finset.sum_le_sum fun c hc => hrootBound c hc
    _ = (roots.card:ℝ)*B := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ 2*B := mul_le_mul_of_nonneg_right
      (by exact_mod_cast g.sourceRootCells_card_le_two tops slope precision cutoff start hslope) hB

end LipschitzHilbert.AngularGrid

end

end OAI
