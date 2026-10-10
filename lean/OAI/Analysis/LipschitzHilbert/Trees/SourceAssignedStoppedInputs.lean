import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedVertexPath
import OAI.Analysis.LipschitzHilbert.Trees.SourceStoppedRecurrence

namespace OAI

/-! The original-packet local bounds give exactly the amplitude inputs of
`physicalStoppedBoundAt`. The terminal distinguished top may disappear
while other children remain; the actual cell loss is still bounded by
the stopped path loss. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X : Type*} {κ : Type} [Fintype κ]

/-- Local node and off-child estimates transfer to the mass-stopped path
without altering the packet coefficients or the terminal mass convention. -/
theorem source_stopped_local_envelope {Kb : ℕ}
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cut : ℝ) (weight : τ → X → ℝ) (hw : ∀ t x, 0 ≤ weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a : ℝ) (hKb : 0 < Kb) (shift : Fin Kb)
    (top : τ) (x : X) (count : ℕ) (M C CW : ℝ) (hM : 0 ≤ M) (hCW : 0 ≤ CW)
    (hterminal : ¬g.eligible cut (precision top) (ShiftedBlocks.endpoint shift count))
    (hnode : ∀ level cell,
      ‖g.sourcePacketAmplitude tops slope precision cut weight K gap packets assigned stop
        (value x) phase a x level cell‖ ≤ C*g.mass tops slope precision cut weight level cell x)
    (hoff : ∀ lower upper, lower ≤ upper → ∀ s,
      g.mass tops slope precision cut weight lower (g.index lower s) x-
        g.mass tops slope precision cut weight upper (g.index upper s) x < 1 →
      ‖g.sourcePacketAmplitude tops slope precision cut weight K gap
        (packets.filter (fun q => assigned q ∉ g.cellTops tops slope precision cut
          upper (g.index upper s))) assigned stop (value x) phase a x lower (g.index lower s)‖ ≤
        CW*(g.mass tops slope precision cut weight lower (g.index lower s) x-
          g.mass tops slope precision cut weight upper (g.index upper s) x)) :
    let n := g.shiftedPathMass tops slope precision cut weight shift top x
    let finish := firstMassStop n count M
    let amp := g.sourceShiftedPathAmplitude tops slope precision cut weight K gap
      packets assigned stop value phase a shift top x
    let base := g.sourcePacketBase tops slope precision cut weight assigned stop (value x) a x
    let transition := g.sourceTransition tops slope precision cut weight K gap phase x
    let W := fun j => g.packetAmplitude
      (packets.filter (fun q => assigned q ∉ g.cellTops tops slope precision cut
        (ShiftedBlocks.endpoint shift (j+1))
        (g.index (ShiftedBlocks.endpoint shift (j+1)) (slope top))))
      (fun q => slope (assigned q)) stop base transition
      (ShiftedBlocks.endpoint shift j) (g.index (ShiftedBlocks.endpoint shift j) (slope top))
    (∀ j, ‖amp j‖ ≤ C*n j) ∧
      (∀ j < finish, n j-n (j+1) < 1 → ‖W j‖ ≤ CW*(n j-n (j+1))) := by
  dsimp only
  let n := g.shiftedPathMass tops slope precision cut weight shift top x
  have hnlast : n count ≤ M := by
    rw [show n count = 0 from g.shiftedPathMass_terminal_zero tops slope precision
      cut weight shift top count hterminal x]
    exact hM
  constructor
  · intro j
    by_cases he : g.eligible cut (precision top) (ShiftedBlocks.endpoint shift j)
    · simpa only [sourceShiftedPathAmplitude,shiftedPathMass,ite_eq_left he] using
        hnode (ShiftedBlocks.endpoint shift j) (g.index (ShiftedBlocks.endpoint shift j) (slope top))
    · simp only [sourceShiftedPathAmplitude,shiftedPathMass,ite_eq_right he,norm_zero,mul_zero,le_refl]
  · intro j hj hdrop
    have hnpos : 0 < n j := lt_of_le_of_lt hM ((firstMassStop_spec n count M hnlast).2.2 j hj)
    have he := g.shiftedPathMass_ne_zero_eligible tops slope precision cut weight
      shift top x j hnpos.ne'
    have hcell :
        g.mass tops slope precision cut weight (ShiftedBlocks.endpoint shift j)
          (g.index (ShiftedBlocks.endpoint shift j) (slope top)) x-
        g.mass tops slope precision cut weight (ShiftedBlocks.endpoint shift (j+1))
          (g.index (ShiftedBlocks.endpoint shift (j+1)) (slope top)) x ≤ n j-n (j+1) := by
      dsimp only [n]
      rw [shiftedPathMass,ite_eq_left he]
      by_cases hnext : g.eligible cut (precision top) (ShiftedBlocks.endpoint shift (j+1))
      · rw [shiftedPathMass,ite_eq_left hnext]
      · rw [shiftedPathMass,ite_eq_right hnext,sub_zero]
        exact sub_le_self _ (g.mass_nonnegative tops slope precision cut weight hw _ _ x)
    have hb := hoff (ShiftedBlocks.endpoint shift j) (ShiftedBlocks.endpoint shift (j+1))
      ((ShiftedBlocks.endpoint_strictMono hKb shift).monotone (Nat.le_succ j))
      (slope top) (lt_of_le_of_lt hcell hdrop)
    exact hb.trans (mul_le_mul_of_nonneg_left hcell hCW)

end LipschitzHilbert.AngularGrid

end

end OAI
