import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalShiftedResidual
import OAI.Analysis.LipschitzHilbert.Packets.SourceRestrictedPacketAmplitude

namespace OAI

/-! A good event for the selected physical reference family controls
the original selected packet residuals, with the same hierarchy masses. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.SourceLabeledLattice

theorem eventually_selected_physical_shifted_residual_square
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
      z ∉ (P.restrictPackets packets).physicalReferenceBad
        (P.restrictedAlternate alt packets) (P.restrictedAlternate_bound alt hAlt packets)
        t a b v f (fun j l u => T (assigned ⟨j,⟨l,u.val⟩⟩)) L A (q+8) (2*q+9) s →
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
  filter_upwards [eventually_physical_shifted_good_reference_residual_square q D hq hD]
    with L hbound
  intro N κ Label Item _ _ P horder hP alt hAlt t a b hb hb1 v hv f hf hf1
    τ grid tops slope precision T A s w hw hbranch hK shift hzero hp
  dsimp only
  intro phase hz alpha ha ha1 z packets assigned hassigned he count pathSlope hgood
  let Q := P.restrictPackets packets
  let own : Q.PacketIndex → τ := fun u => assigned ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩
  have hown (u : Q.PacketIndex) (_hu : u ∈ Finset.univ) : own u ∈ tops :=
    hassigned _ (P.restrictedPacketEquiv packets u).property
  have helig (u : Q.PacketIndex) (_hu : u ∈ Finset.univ) :
      grid.eligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (precision (own u))
        (grid.lastEligible (grid.rootWidth/(SourceParameters.branching L)^2)
          (w/Q.length u.1) (div_pos hw (Q.length_pos u.1))) :=
    he _ (P.restrictedPacketEquiv packets u).property
  have hs := hbound N κ Label (P.RestrictedPacketItem packets) Q horder hP
    (P.restrictedAlternate alt packets) (P.restrictedAlternate_bound alt hAlt packets)
    t a b hb hb1 v hv f hf hf1 τ grid tops slope precision T A s w hw hbranch hK shift
    hzero hp phase hz alpha ha ha1 z Finset.univ own hown helig count pathSlope hgood
  convert hs using 1
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun u : EuclideanSpace ℂ κ => ‖u‖^2)
  exact (P.restrictPackets_physicalSourceResidual alt hAlt packets t b v f grid tops slope
    precision (grid.rootWidth/(SourceParameters.branching L)^2)
    (fun top z => (T top).weight (L^(A+2)) D z) assigned
    (fun i => grid.lastEligible (grid.rootWidth/(SourceParameters.branching L)^2)
      (w/P.length i) (div_pos hw (P.length_pos i))) T L A alpha z
    (grid.sourceTransition tops slope precision (grid.rootWidth/(SourceParameters.branching L)^2)
      (fun top z => (T top).weight (L^(A+2)) D z) (SourceParameters.blockCount L)
      (grid.sourceBoundaryGap L) phase z)
    (ShiftedBlocks.endpoint shift j.val) (ShiftedBlocks.endpoint shift (j.val+1))
    (grid.index (ShiftedBlocks.endpoint shift j.val) pathSlope)).symm

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
