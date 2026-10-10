import OAI.Analysis.LipschitzHilbert.Trees.SourceNodeMeasurable
import OAI.Analysis.LipschitzHilbert.Fourier.LineWeightAverage

namespace OAI

/-! The original finite hierarchy path integrand, expressed only through
packet amplitudes, top weights and the stopping threshold. Its spatial
measurability does not involve the auxiliary snapshot choices. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {τ σ X : Type*} {κ : Type} [MeasurableSpace X] [Fintype κ]

def sourceBlockNodeRatio (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a α p : ℝ) (lower upper : ℕ) (parent : ℤ) (x : X) : ℝ :=
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  sourceNodeRatio (g.mass tops slope precision cutoff weight lower parent x)
    (fun i : cells => g.mass tops slope precision cutoff weight upper i.val x)
    (fun i : cells => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop (value x) phase a x upper i.val) α p
    (g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop (value x) phase a x lower parent)

def sourceShiftedPathRatio {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a α p : ℝ) (tag : Fin Kb) (top : τ) (x : X) (j : ℕ) : ℝ :=
  g.sourceBlockNodeRatio tops slope precision cutoff weight K gap packets assigned stop value
    phase a α p (ShiftedBlocks.endpoint tag j) (ShiftedBlocks.endpoint tag (j+1))
    (g.index (ShiftedBlocks.endpoint tag j) (slope top)) x

def sourceActivePathValue {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a α p M : ℝ) (tag : Fin Kb) (top : τ) (count : ℕ) : X → ℝ :=
  sourceActiveProduct (g.shiftedPathMass tops slope precision cutoff weight tag top)
    (g.sourceShiftedPathRatio tops slope precision cutoff weight K gap packets assigned stop value
      phase a α p tag top) M count

theorem sourceActivePathValue_measurable {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t, Measurable (weight t))
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (hv : ∀ s, Measurable (fun x => value x s))
    (phase : ℕ → ℂ) (a α p M : ℝ) (tag : Fin Kb) (top : τ) (count : ℕ) :
    Measurable (g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned
      stop value phase a α p M tag top count) := by
  apply measurable_sourceActiveProduct
  · exact fun j => g.measurable_shiftedPathMass tops slope precision cutoff weight hw tag top j
  · intro j
    exact g.source_packet_node_ratio_measurable tops slope precision cutoff weight hw
      K gap packets assigned stop value hv phase a α p _ _ _

omit [MeasurableSpace X] in
theorem sourceBlockNodeRatio_nonneg (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t x, 0 ≤ weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a α p : ℝ) (lower upper : ℕ) (parent : ℤ) (x : X) :
    0 ≤ g.sourceBlockNodeRatio tops slope precision cutoff weight K gap packets assigned
      stop value phase a α p lower upper parent x := by
  unfold sourceBlockNodeRatio
  apply sourceNodeRatio_nonneg
  · exact g.mass_nonnegative tops slope precision cutoff weight hw lower parent x
  · intro i
    exact g.mass_nonnegative tops slope precision cutoff weight hw upper i.val x

omit [MeasurableSpace X] in
theorem sourceActivePathValue_nonneg {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t x, 0 ≤ weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a α p M : ℝ) (tag : Fin Kb) (top : τ) (count : ℕ) (x : X) :
    0 ≤ g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned
      stop value phase a α p M tag top count x := by
  apply sourceActiveProduct_nonneg
  intro j _ _
  exact g.sourceBlockNodeRatio_nonneg tops slope precision cutoff weight hw K gap packets
    assigned stop value phase a α p _ _ _ x

/-- The actual source path factor, restricted to an arbitrary measurable
good set and multiplied by its distinguished top weight, is measurable. -/
theorem source_path_integrand_measurable {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (T : τ → SlopeBox) (w cutoff Kw D : ℝ) (hKw : 0 < Kw)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : (ℝ × ℝ) → σ → EuclideanSpace ℂ κ)
    (hv : ∀ s, Measurable (fun x => value x s))
    (phase : ℕ → ℂ) (a α p M : ℝ) (tag : Fin Kb) (top : τ) (count : ℕ)
    (good : Set (ℝ × ℝ)) (hgood : MeasurableSet good) :
    Measurable (good.indicator (fun x => (T top).weight Kw D x *
      g.sourceActivePathValue tops (fun t => (T t).slope) (fun t => w/(T t).length) cutoff
        (fun t x => (T t).weight Kw D x) K gap packets assigned stop value
        phase a α p M tag top count x)) := by
  apply Measurable.indicator _ hgood
  exact ((T top).continuous_weight hKw D).measurable.mul
    (g.sourceActivePathValue_measurable tops _ _ _ _
      (fun t => ((T t).continuous_weight hKw D).measurable)
      K gap packets assigned stop value hv phase a α p M tag top count)

end LipschitzHilbert.AngularGrid

end

end OAI
