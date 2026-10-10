import OAI.Analysis.LipschitzHilbert.Phase.SourcePathPrediction

namespace OAI

/-! The amplitude on a distinguished top path stops when that top becomes
ineligible. Other surviving children remain in the original denominator. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem sourceNodeDenominator_ge_mass {ι κ : Type} [Fintype ι] [Fintype κ]
    (n : ℝ) (c : ι → ℝ) (A : ι → EuclideanSpace ℂ κ) (α p : ℝ)
    (hc : ∀ i, 0 ≤ c i) : n ≤ sourceNodeDenominator n c A α p := by
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (hc i) _)
    (Real.rpow_nonneg (norm_nonneg _) _)

theorem sourceNodeDenominator_ge_child {ι κ : Type} [Fintype ι] [Fintype κ]
    (n : ℝ) (c : ι → ℝ) (A : ι → EuclideanSpace ℂ κ) (α p : ℝ)
    (hc : ∀ i, 0 ≤ c i) (i : ι) :
    n-c i+vertexAmount (c i) (A i) α p ≤ sourceNodeDenominator n c A α p := by
  have h := Finset.single_le_sum
    (s := Finset.univ) (f := fun k => (c k)^(α-p)*‖A k‖^p)
    (fun k _ => mul_nonneg (Real.rpow_nonneg (hc k) _)
      (Real.rpow_nonneg (norm_nonneg _) _)) (Finset.mem_univ i)
  dsimp only [vertexAmount,sourceNodeDenominator]
  linarith

namespace AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X : Type*} {κ : Type} [Fintype κ]

def sourceShiftedPathAmplitude {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a : ℝ) (tag : Fin Kb) (top : τ) (x : X) (j : ℕ) :
    EuclideanSpace ℂ κ :=
  if g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag j) then
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
      (value x) phase a x (ShiftedBlocks.endpoint tag j)
      (g.index (ShiftedBlocks.endpoint tag j) (slope top)) else 0

def sourceShiftedPathDenominator {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a α p : ℝ) (tag : Fin Kb) (top : τ) (x : X) (j : ℕ) : ℝ :=
  let lower := ShiftedBlocks.endpoint tag j
  let upper := ShiftedBlocks.endpoint tag (j+1)
  let parent := g.index lower (slope top)
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  sourceNodeDenominator (g.mass tops slope precision cutoff weight lower parent x)
    (fun i : cells => g.mass tops slope precision cutoff weight upper i.val x)
    (fun i : cells => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
        packets assigned stop (value x) phase a x upper i.val) α p

theorem source_shifted_ratio_eq_amount_div_denominator {Kb : ℕ}
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ)
    (assigned : σ → τ) (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a α p : ℝ) (tag : Fin Kb) (top : τ) (x : X) (j : ℕ)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag j)) :
    g.sourceShiftedPathRatio tops slope precision cutoff weight K gap packets assigned stop value
      phase a α p tag top x j =
    vertexAmount (g.shiftedPathMass tops slope precision cutoff weight tag top x j)
      (g.sourceShiftedPathAmplitude tops slope precision cutoff weight K gap packets assigned stop
        value phase a tag top x j) α p /
      g.sourceShiftedPathDenominator tops slope precision cutoff weight K gap packets assigned stop
        value phase a α p tag top x j := by
  simp only [sourceShiftedPathRatio,sourceBlockNodeRatio,sourceNodeRatio,shiftedPathMass,
    sourceShiftedPathAmplitude,ite_eq_left he,sourceShiftedPathDenominator]

theorem source_active_path_eq_stopped_product {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hprecision : ∀ t ∈ tops, 0 ≤ precision t) (hweight : ∀ t x, 0 ≤ weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ) (phase : ℕ → ℂ)
    (a α p M : ℝ) (hM : 0 ≤ M) (hKb : 0 < Kb) (tag : Fin Kb)
    (top : τ) (htop : top ∈ tops) (count : ℕ)
    (hterminal : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag count)) (x : X) :
    g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
      phase a α p M tag top count x =
    ∏ j ∈ Finset.range
      (firstMassStop (g.shiftedPathMass tops slope precision cutoff weight tag top x) count M),
      g.sourceShiftedPathRatio tops slope precision cutoff weight K gap packets assigned stop value
        phase a α p tag top x j := by
  apply sourceActiveProduct_eq_stopped_product
  · rw [g.shiftedPathMass_terminal_zero tops slope precision cutoff weight tag top count hterminal]
    exact hM
  · exact g.shiftedPathMass_antitone tops slope precision cutoff weight hprecision hweight
      hKb tag top htop x

/-- The true denominator controls the next distinguished path node, even
when the path terminates while other children survive. -/
theorem source_shifted_path_denominator_ge_next {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hprecision : ∀ t ∈ tops, 0 ≤ precision t) (hweight : ∀ t x, 0 ≤ weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a α p : ℝ) (hp : 0 < p) (hKb : 0 < Kb)
    (tag : Fin Kb) (top : τ) (htop : top ∈ tops) (x : X) (j : ℕ)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag j)) :
    let n := g.shiftedPathMass tops slope precision cutoff weight tag top x
    let A := g.sourceShiftedPathAmplitude tops slope precision cutoff weight K gap
      packets assigned stop value phase a tag top x
    n j-n (j+1)+vertexAmount (n (j+1)) (A (j+1)) α p ≤
      g.sourceShiftedPathDenominator tops slope precision cutoff weight K gap packets
        assigned stop value phase a α p tag top x j := by
  dsimp only
  let lower := ShiftedBlocks.endpoint tag j
  let upper := ShiftedBlocks.endpoint tag (j+1)
  let parent := g.index lower (slope top)
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  have hn := g.mass_nonnegative tops slope precision cutoff weight hweight
  by_cases hnext : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag (j+1))
  · have hi : g.index upper (slope top) ∈ cells := g.mem_sourceBlockCells_of_top tops
      slope precision cutoff lower upper parent hprecision
      ((ShiftedBlocks.endpoint_strictMono hKb tag).monotone (Nat.le_succ j)) top htop rfl hnext
    have h := sourceNodeDenominator_ge_child
      (g.mass tops slope precision cutoff weight lower parent x)
      (fun i : cells => g.mass tops slope precision cutoff weight upper i.val x)
      (fun i : cells => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
        packets assigned stop (value x) phase a x upper i.val) α p (fun i => hn _ _ x)
      ⟨g.index upper (slope top),hi⟩
    simpa only [shiftedPathMass,sourceShiftedPathAmplitude,ite_eq_left he,
      ite_eq_left hnext,sourceShiftedPathDenominator] using h
  · have h := sourceNodeDenominator_ge_mass
      (g.mass tops slope precision cutoff weight lower parent x)
      (fun i : cells => g.mass tops slope precision cutoff weight upper i.val x)
      (fun i : cells => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
        packets assigned stop (value x) phase a x upper i.val) α p (fun i => hn _ _ x)
    simpa only [shiftedPathMass,sourceShiftedPathAmplitude,ite_eq_left he,
      ite_eq_right hnext,sourceShiftedPathDenominator,sub_zero,vertexAmount,norm_zero,
      Real.zero_rpow (ne_of_gt hp),mul_zero,add_zero] using h

end AngularGrid
end LipschitzHilbert

end

end OAI
