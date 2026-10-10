import OAI.Analysis.LipschitzHilbert.Trees.SourceStoppedAmplitude
import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualPropagation

namespace OAI

/-! The source residual identities on the actual mass-stopped path.
A unary step cannot terminate the distinguished top while its mass is active. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X : Type*} {κ : Type} [Fintype κ]

theorem shiftedPathMass_ne_zero_eligible {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (tag : Fin Kb) (top : τ) (x : X) (j : ℕ)
    (hn : g.shiftedPathMass tops slope precision cutoff weight tag top x j ≠ 0) :
    g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag j) := by
  by_contra he
  exact hn (by simp only [shiftedPathMass,ite_eq_right he])

theorem source_unary_next_eligible {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (tag : Fin Kb) (top : τ) (x : X) (j : ℕ) {M : ℝ} (hM : 1 ≤ M)
    (hactive : M < g.shiftedPathMass tops slope precision cutoff weight tag top x j)
    (hdrop : g.shiftedPathMass tops slope precision cutoff weight tag top x j-
      g.shiftedPathMass tops slope precision cutoff weight tag top x (j+1) < 1) :
    g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag (j+1)) := by
  apply g.shiftedPathMass_ne_zero_eligible tops slope precision cutoff weight tag top x
  have hpos : 0 < g.shiftedPathMass tops slope precision cutoff weight tag top x (j+1) := by
    linarith
  exact hpos.ne'

theorem source_stopped_unary_recurrence {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hprecision : ∀ t ∈ tops, 0 ≤ precision t) (hweight : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (packets : Finset σ)
    (assigned : σ → τ) (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a : ℝ) (hphase : ∀ k, 0 ≤ (phase k).re)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (heligible : ∀ q ∈ packets, g.eligible cutoff (precision (assigned q)) (stop q))
    (hKb : 0 < Kb) (tag : Fin Kb) (top : τ) (htop : top ∈ tops)
    (x : X) (j : ℕ) {M : ℝ} (hM : 1 ≤ M)
    (hactive : M < g.shiftedPathMass tops slope precision cutoff weight tag top x j)
    (hdrop : g.shiftedPathMass tops slope precision cutoff weight tag top x j-
      g.shiftedPathMass tops slope precision cutoff weight tag top x (j+1) < 1) :
    let lower := ShiftedBlocks.endpoint tag j
    let upper := ShiftedBlocks.endpoint tag (j+1)
    let A := g.sourceShiftedPathAmplitude tops slope precision cutoff weight K gap
      packets assigned stop value phase a tag top x
    let base := g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x
    let transition := g.sourceTransition tops slope precision cutoff weight K gap phase x
    let keep := fun q => assigned q ∈ g.cellTops tops slope precision cutoff upper
      (g.index upper (slope top))
    let lam := g.packetPathProduct transition lower upper (slope top)
    ‖lam‖ ≤ 1 ∧ A j = lam • A (j+1)+
      g.packetResidual (packets.filter keep) (fun q => slope (assigned q)) stop base transition
        lower upper (g.index lower (slope top))+
      g.packetAmplitude (packets.filter fun q => ¬keep q) (fun q => slope (assigned q)) stop base
        transition lower (g.index lower (slope top)) := by
  dsimp only
  have hnext := g.source_unary_next_eligible tops slope precision cutoff weight tag top x j
    hM hactive hdrop
  have hlo := (ShiftedBlocks.endpoint_strictMono hKb tag).monotone (Nat.le_succ j)
  have he := g.eligible_of_le (hprecision top htop) hlo hnext
  refine ⟨g.source_path_product_norm_le_one tops slope precision cutoff weight hprecision
    hweight hK gap phase x _ _ top htop hnext (fun k _ => hphase k),?_⟩
  have hr := g.sourcePacketAmplitude_unary_recurrence tops slope precision cutoff weight
    hprecision K gap packets assigned stop (value x) phase a x hassigned heligible hlo (slope top)
  simpa only [sourceShiftedPathAmplitude,ite_eq_left he,ite_eq_left hnext] using hr

/-- Removing the actual block residual gives exactly the predictor used
in the physical marked integral, with the original child denominator. -/
theorem source_stopped_residual_free_ratio {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hprecision : ∀ t ∈ tops, 0 ≤ precision t) (hweight : ∀ t x, 0 < weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a α p μ : ℝ) (hrelation : p*μ = α-1)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (heligible : ∀ q ∈ packets, g.eligible cutoff (precision (assigned q)) (stop q))
    (hKb : 0 < Kb) (tag : Fin Kb) (top : τ) (htop : top ∈ tops) (x : X) (j : ℕ)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag j)) :
    let residual := g.packetResidual packets (fun q => slope (assigned q)) stop
      (g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x)
      (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      (ShiftedBlocks.endpoint tag j) (ShiftedBlocks.endpoint tag (j+1))
      (g.index (ShiftedBlocks.endpoint tag j) (slope top))
    g.sourceShiftedPathPrediction tops slope precision cutoff weight K gap packets assigned stop
      value phase a p μ tag top x j =
    vertexAmount (g.shiftedPathMass tops slope precision cutoff weight tag top x j)
      (g.sourceShiftedPathAmplitude tops slope precision cutoff weight K gap packets assigned stop
        value phase a tag top x j-residual) α p /
      g.sourceShiftedPathDenominator tops slope precision cutoff weight K gap packets assigned stop
        value phase a α p tag top x j := by
  have hparent : (g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint tag j)
      (g.index (ShiftedBlocks.endpoint tag j) (slope top))).Nonempty :=
    ⟨top,(g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨htop,rfl,he⟩⟩
  have hr := g.source_block_residual_free_ratio tops slope precision cutoff weight hprecision
    hweight K gap packets assigned stop (value x) phase a x hassigned heligible
    ((ShiftedBlocks.endpoint_strictMono hKb tag).monotone (Nat.le_succ j))
    (g.index (ShiftedBlocks.endpoint tag j) (slope top)) hparent μ α p hrelation
  simpa only [sourceShiftedPathPrediction,sourceBlockPrediction,shiftedPathMass,
    sourceShiftedPathAmplitude,ite_eq_left he,sourceShiftedPathDenominator,sourceNodeRatio] using hr

end LipschitzHilbert.AngularGrid

end

end OAI
