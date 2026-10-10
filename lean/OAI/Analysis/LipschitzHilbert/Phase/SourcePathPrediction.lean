import OAI.Analysis.LipschitzHilbert.Trees.SourcePathIntegrand
import OAI.Analysis.LipschitzHilbert.Trees.SourceBlockPathMass

namespace OAI

/-! The residual-free predictor on the actual packet path. Its child
family and coefficients are the same ones used by the physical estimate. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {τ σ X : Type*} {κ : Type} [MeasurableSpace X] [Fintype κ]

def sourceBlockPrediction (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a p μ : ℝ) (lower upper : ℕ) (parent : ℤ) (x : X) : ℝ :=
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  sourcePredictionValue p μ (g.mass tops slope precision cutoff weight lower parent x)
    (fun i : cells => g.mass tops slope precision cutoff weight upper i.val x)
    (fun i : cells => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop (value x) phase a x upper i.val)
    (fun i : cells => g.packetPathProduct
      (g.sourceTransition tops slope precision cutoff weight K gap phase x) lower upper
      (slope (g.sourceBlockTop tops slope precision cutoff lower upper parent i)))

def sourceShiftedPathPrediction {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a p μ : ℝ) (tag : Fin Kb) (top : τ) (x : X) (j : ℕ) : ℝ :=
  g.sourceBlockPrediction tops slope precision cutoff weight K gap packets assigned stop value
    phase a p μ (ShiftedBlocks.endpoint tag j) (ShiftedBlocks.endpoint tag (j+1))
    (g.index (ShiftedBlocks.endpoint tag j) (slope top)) x

theorem sourceBlockPrediction_measurable (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t, Measurable (weight t))
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (hv : ∀ s, Measurable (fun x => value x s))
    (phase : ℕ → ℂ) (a p μ : ℝ) (lower upper : ℕ) (parent : ℤ) :
    Measurable (g.sourceBlockPrediction tops slope precision cutoff weight K gap packets
      assigned stop value phase a p μ lower upper parent) := by
  apply measurable_sourcePredictionValue
  · exact g.measurable_mass tops slope precision cutoff weight hw lower parent
  · intro i
    exact g.measurable_mass tops slope precision cutoff weight hw upper i.val
  · intro i
    exact g.measurable_sourcePacketAmplitude tops slope precision cutoff weight hw K gap
      packets assigned stop value hv phase a upper i.val
  · intro i
    exact g.measurable_packetPathProduct _
      (g.measurable_sourceTransition tops slope precision cutoff weight hw K gap phase) _ _ _

theorem sourceShiftedPathPrediction_measurable {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t, Measurable (weight t))
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (hv : ∀ s, Measurable (fun x => value x s))
    (phase : ℕ → ℂ) (a p μ : ℝ) (tag : Fin Kb) (top : τ) (j : ℕ) :
    Measurable (fun x => g.sourceShiftedPathPrediction tops slope precision cutoff weight K gap
      packets assigned stop value phase a p μ tag top x j) :=
  g.sourceBlockPrediction_measurable tops slope precision cutoff weight hw K gap packets
    assigned stop value hv phase a p μ _ _ _

omit [MeasurableSpace X] in
theorem sourceShiftedPathPrediction_pos {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t x, 0 < weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a p μ : ℝ) (tag : Fin Kb) (top : τ)
    (htop : top ∈ tops) (x : X) (j : ℕ)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag j)) :
    0 < g.sourceShiftedPathPrediction tops slope precision cutoff weight K gap packets
      assigned stop value phase a p μ tag top x j := by
  unfold sourceShiftedPathPrediction sourceBlockPrediction
  apply sourcePredictionValue_pos
  · exact g.path_mass_pos tops slope precision cutoff weight hw _ top htop he x
  · intro i
    exact g.mass_nonnegative tops slope precision cutoff weight (fun t x => (hw t x).le)
      _ i.val x

end LipschitzHilbert.AngularGrid

end

end OAI
