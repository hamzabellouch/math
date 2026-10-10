import OAI.Analysis.LipschitzHilbert.Trees.SourcePathCountInvariant
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-! Per-top path integrals are unchanged when their terminal counts are
replaced by a common terminal count. The original good set, weights and
physical packet values are preserved. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {τ σ X : Type*} {κ : Type} [Fintype κ] [MeasurableSpace X]

theorem sourceActivePathValue_integral_count_congr {Kb : ℕ}
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 ≤ weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a alpha p M : ℝ) (hM : 0 ≤ M)
    (hKb : 0 < Kb) (shift : Fin Kb) (top : τ) (htop : top ∈ tops)
    (c d : ℕ)
    (hc : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint shift c))
    (hd : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint shift d))
    (good : Set X) (μ : Measure X) (C : ℝ)
    (hbound :
      Integrable (good.indicator (fun x => weight top x *
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop
          value phase a alpha p M shift top c x)) μ ∧
      (∫ x, good.indicator (fun y => weight top y *
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop
          value phase a alpha p M shift top c y) x ∂μ) ≤ C*(∫ x, weight top x ∂μ)) :
    Integrable (good.indicator (fun x => weight top x *
      g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop
        value phase a alpha p M shift top d x)) μ ∧
    (∫ x, good.indicator (fun y => weight top y *
      g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop
        value phase a alpha p M shift top d y) x ∂μ) ≤ C*(∫ x, weight top x ∂μ) := by
  have heq : (fun x => g.sourceActivePathValue tops slope precision cutoff weight K gap
      packets assigned stop value phase a alpha p M shift top c x) =
      (fun x => g.sourceActivePathValue tops slope precision cutoff weight K gap
      packets assigned stop value phase a alpha p M shift top d x) := by
    funext x
    exact g.sourceActivePathValue_count_congr tops slope precision cutoff weight hp hw
      K gap packets assigned stop value phase a alpha p M hM hKb shift top htop c d hc hd x
  simpa only [heq] using hbound

theorem sourceActivePathValue_common_terminal_integral {Kb : ℕ}
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 ≤ weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a alpha p M : ℝ) (hM : 0 ≤ M)
    (hKb : 0 < Kb) (shift : Fin Kb) (count : τ → ℕ)
    (hterminal : ∀ t ∈ tops, ¬g.eligible cutoff (precision t)
      (ShiftedBlocks.endpoint shift (count t)))
    (good : Set X) (μ : Measure X) (C : ℝ)
    (hbound : ∀ t ∈ tops,
      Integrable (good.indicator (fun x => weight t x *
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop
          value phase a alpha p M shift t (count t) x)) μ ∧
      (∫ x, good.indicator (fun y => weight t y *
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop
          value phase a alpha p M shift t (count t) y) x ∂μ) ≤ C*(∫ x, weight t x ∂μ)) :
    ∀ t ∈ tops,
      Integrable (good.indicator (fun x => weight t x *
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop
          value phase a alpha p M shift t (tops.sup count) x)) μ ∧
      (∫ x, good.indicator (fun y => weight t y *
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop
          value phase a alpha p M shift t (tops.sup count) y) x ∂μ) ≤ C*(∫ x, weight t x ∂μ) := by
  intro t ht
  exact g.sourceActivePathValue_integral_count_congr tops slope precision cutoff weight hp hw
    K gap packets assigned stop value phase a alpha p M hM hKb shift t ht (count t)
    (tops.sup count) (hterminal t ht)
    (g.source_common_terminal tops precision cutoff hp hKb shift count hterminal t ht)
    good μ C (hbound t ht)

end LipschitzHilbert.AngularGrid

end

end OAI
