import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalGoodResidual
import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualBlockBudget
import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryScales

namespace OAI

/-! The actual shifted angular blocks satisfy the good-reference
residual square estimate with a fixed polynomial exponent. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.SourceLabeledLattice

/-- Source dyadic stopping and the good event discharge the block count,
mask normalization and positive reference envelopes simultaneously. -/
theorem eventually_physical_shifted_good_reference_residual_square
    (q D : ℝ) (hq : 0 ≤ q) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), 6 ≤ P.order → P.absoluteConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k u, ‖b j l k u‖ ≤ 1) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (τ : Type*) (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
      (T : τ → SlopeBox) (A s : ℝ) (w : ℝ) (hw : 0 < w),
      (grid.branching:ℝ) = SourceParameters.step L →
    ∀ (_hK : 0 < SourceParameters.blockCount L) (shift : Fin (SourceParameters.blockCount L)),
      (∀ j : Fin N, grid.eligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (w/P.length j) 0) → (∀ top ∈ tops, 0 ≤ precision top) →
    let cut := grid.rootWidth/(SourceParameters.branching L)^2
    let stop := fun j : Fin N => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let weight := fun top z => (T top).weight (L^(A+2)) D z
    ∀ (phase : ℕ → ℂ), (∀ k, 0 ≤ (phase k).re) →
    ∀ (alpha : ℝ), 0 ≤ alpha → alpha ≤ 1 →
    ∀ (z : ℝ×ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
      (∀ u ∈ packets, assigned u ∈ tops) →
      (∀ u ∈ packets, grid.eligible cut (precision (assigned u)) (stop u.1)) →
    ∀ (count : ℕ) (pathSlope : ℝ),
      z ∉ P.physicalReferenceBad alt hAlt t a b v f
        (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A (q+8) (2*q+9) s →
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
    (∑ j : Fin count, ‖grid.packetResidual packets (fun u => slope (assigned u))
      (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cut weight assigned (fun u => stop u.1) value alpha z)
      (grid.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
        (grid.sourceBoundaryGap L) phase z)
      (ShiftedBlocks.endpoint shift j.val) (ShiftedBlocks.endpoint shift (j.val+1))
      (grid.index (ShiftedBlocks.endpoint shift j.val) pathSlope)‖^2) ≤
        (L^(3*q+12))^2 := by
  filter_upwards [eventually_shifted_residual_length_budget,
    eventually_ge_atTop (max 6 D)] with L hbudget hlarge
  have hL : 6 ≤ L := (le_max_left _ _).trans hlarge
  have hdegree : D ≤ ((2*⌈L⌉₊:ℕ):ℝ) := by
    have hceil : L ≤ (⌈L⌉₊:ℝ) := Nat.le_ceil L
    have hDL : D ≤ L := (le_max_right _ _).trans hlarge
    push_cast
    linarith
  intro N κ Label Item _ _ P horder hP alt hAlt t a b hb hb1 v hv f hf hf1
    τ grid tops slope precision T A s w hw hbranch hK shift hzero hp
  dsimp only
  intro phase hz alpha ha ha1 z packets assigned hassigned he count pathSlope hgood
  let cut := grid.rootWidth/(SourceParameters.branching L)^2
  let stop := fun j : Fin N => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
  have hcard (j : ℕ) (_hj : j < count) :
      ((residualLengthSet stop (ShiftedBlocks.endpoint shift j)
        (ShiftedBlocks.endpoint shift (j+1))).card:ℝ) ≤ L^(2:ℝ) :=
    hbudget N κ Label Item P grid hbranch hK shift w hw hzero j
  have h := P.physical_good_reference_residual_square alt hAlt horder t a b hb hb1 v hv
    f hf hf1 grid tops slope precision cut T L A D q 2 s hL hD hdegree hq (by norm_num) hP hp
    hK (grid.sourceBoundaryGap L) phase hz alpha ha ha1 z packets assigned stop hassigned he
    (ShiftedBlocks.endpoint shift) (ShiftedBlocks.endpoint_strictMono hK shift)
    count pathSlope (L^(2:ℝ)) (Real.rpow_nonneg (by linarith) _) le_rfl hcard hgood
  simpa only [show 3*q+2+10 = 3*q+12 by ring] using h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
