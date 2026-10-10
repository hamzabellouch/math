import OAI.Analysis.LipschitzHilbert.Trees.SourceOriginalParentMarkedPath
import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedVertexPath

namespace OAI

/-! Assigned-reference interval concentration supplies every local
amplitude bound in the actual marked path theorem. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable

def assignedParentMarkedPathBoundAt (q qEnv D Cmass A_M Cweight L : ℝ) (Klocal Hlocal : ℕ) : Prop :=

    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), 6 ≤ P.order → P.absoluteConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t a : ℝ) (d radius : Fin N → ℝ), (∀ j, 0 < d j) → (∀ j, radius j ≤ Klocal) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => t+P.rowSlope j l) (d j) Hlocal) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 → |s-(t+P.rowSlope j l)| ≤ radius j*d j) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (τ : Type) (grid : AngularGrid) (tops : Finset τ)
      (T : τ → SlopeBox) (A s w R C F : ℝ) (hw : 0 < w) (hR : 0 < R),
    let slope : τ → ℝ := fun top => (T top).slope;
    let precision : τ → ℝ := fun top => w/(T top).length;
      (grid.branching:ℝ) = SourceParameters.step L →
    ∀ (hK : 0 < SourceParameters.blockCount L) (shift : Fin (SourceParameters.blockCount L)),
      (∀ j : Fin N, grid.eligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (w/P.length j) 0) → (∀ top ∈ tops, 0 ≤ precision top) →
    ∀ (top : τ), top ∈ tops → R = (T top).length →
    ∀ (hcone : 0 ≤ C+(SourceParameters.branching L)^2) (hF : 0 ≤ F)
      (hwide : (C+(SourceParameters.branching L)^2)*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
      (hparentCone : 0 ≤ C+(SourceParameters.branching L)^3)
      (hparentWide : (C+(SourceParameters.branching L)^3)*w ≤ P.width),
    let cut := grid.rootWidth/(SourceParameters.branching L)^2
    let stop := fun j : Fin N => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let weight := fun top z => (T top).weight (L^(A+2)) D z
    let count := grid.firstIneligibleShiftedBlock cut (w/R) (div_pos hw hR) hK shift
    ∀ (phase : ℕ → ℂ), (∀ k, 0 ≤ (phase k).re) →
    ∀ (Z Nmass α μ : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 →
      (∀ k, ‖phase k‖ ≤ Z) → 0 < Nmass → Real.log Nmass ≤ 2*L →
      1 ≤ α → α ≤ 3 → (α-1)/Real.sqrt L ≤ 1/12 → Real.sqrt L*μ = α-1 →
    ∀ (z : ℝ×ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
      (∀ u ∈ packets, assigned u ∈ tops) →
      (∀ u ∈ packets, grid.eligible cut (precision (assigned u)) (stop u.1)) →
      (∀ u ∈ packets, |t+P.rowSlope u.1 u.2.1-slope (assigned u)| ≤ C*(w/P.length u.1)) →
    let squarePackets := sourceReferencePackets packets (fun u => P.length u.1)
      (fun u => t+P.rowSlope u.1 u.2.1) R (slope top) (C+(SourceParameters.branching L)^3) w
    let Qsquare := P.referenceFamily t (slope top) R (C+(SourceParameters.branching L)^3) w F
      hw hparentCone hF hparentWide hfrequency
    let origSquare := P.referenceOriginalLabel t (slope top) R (C+(SourceParameters.branching L)^3) w
    let squareSelected := (Finset.univ : Finset Qsquare.PacketIndex).filter
      (fun u => (⟨u.1,⟨origSquare u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ squarePackets)
    let S := grid.fixedPathResidualPackets tops slope precision cut packets assigned
      (fun u => stop u.1) (ShiftedBlocks.endpoint shift) (count-1) (slope top)
    let Q := P.referenceFamily t (slope top) R (C+(SourceParameters.branching L)^2) w F
      hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel t (slope top) R (C+(SourceParameters.branching L)^2) w
    let selected := (Finset.univ : Finset Q.PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S)
    z ∉ (Qsquare.restrictPackets squareSelected).physicalReferenceBad
      (Qsquare.restrictedAlternate (fun j l => alt j (origSquare j l)) squareSelected)
      (Qsquare.restrictedAlternate_bound (fun j l => alt j (origSquare j l))
        (fun j l => hAlt j (origSquare j l)) squareSelected)
      (slope top) (w/P.topLength) (fun j l => b j (origSquare j l)) v f
      (fun j l u => T (assigned ⟨j,⟨origSquare j l,u.val⟩⟩)) L A (q+8) (2*q+9) s →
    z ∉ (Q.restrictPackets selected).physicalReferenceBad
      (Q.restrictedAlternate (fun j l => alt j (orig j l)) selected)
      (Q.restrictedAlternate_bound (fun j l => alt j (orig j l))
        (fun j l => hAlt j (orig j l)) selected)
      (slope top) (w/P.topLength) (fun j l => b j (orig j l)) v f
      (fun j l u => T (assigned ⟨j,⟨orig j l,u.val⟩⟩)) L A (q+8) (2*q+9) (2*q+11) →
    let n := grid.shiftedPathMass tops slope precision cut weight shift top z
    let _finish := firstMassStop n count (L^A_M)
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A
    let level := ShiftedBlocks.endpoint shift
    let transition := grid.sourceTransition tops slope precision cut weight
      (SourceParameters.blockCount L) (grid.sourceBoundaryGap L) phase z
    let base := grid.sourcePacketBase tops slope precision cut weight assigned
      (fun u => stop u.1) (value z) a z
    let _W := fun j => grid.packetAmplitude
      (packets.filter fun u => assigned u ∉ grid.cellTops tops slope precision cut
        (level (j+1)) (grid.index (level (j+1)) (slope top)))
      (fun u => slope (assigned u)) (fun u => stop u.1) base transition
      (level j) (grid.index (level j) (slope top))
    let _amp := grid.sourceShiftedPathAmplitude tops slope precision cut weight
      (SourceParameters.blockCount L) (grid.sourceBoundaryGap L) packets assigned
      (fun u => stop u.1) value phase a shift top z
    ∀ (origin y x : ℝ), z = (x,y+slope top*x) →
    let line := sourceReverseLineGrid grid L origin hw shift count
    let mass := fun xx => grid.shiftedPathMass tops slope precision cut weight
      shift top (xx,y+slope top*xx)
    let marked := fun j i => sourceMarkedCell
      (line.cell (ShiftedBlocks.reverseLevel shift count (ShiftedBlocks.reverseIndex count j)) i)
      (fun xx => mass xx j) (fun xx => mass xx j-mass xx (j+1)) (L^A_M)
    x ∈ line.root → 1 ≤ L^(A+2) →
    (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
    ∀ (A0 : ℝ), 0 ≤ A0 → A0 ≤ L^qEnv → ∀ (hC0 : 0 ≤ C),
      (∀ u ∈ packets, P.length u.1 ≤ (T (assigned u)).length) →
      (∀ u ∈ tops, grid.eligible cut (precision u) 0) →
      (∀ u ∈ tops, weight u z ≤ Cweight) →
      Real.log (max 1 (∑ u ∈ tops, weight u z)) ≤ 3*L →
      Real.log (n 0) ≤ 3*L →
      grid.mass tops slope precision cut weight 0 (grid.index 0 (slope top)) z ≤ L^Cmass*Nmass →
    let hwideLocal : C*w ≤ P.width := by
      have hb : 0 ≤ ((SourceParameters.branching L:ℝ)^2)*w := mul_nonneg (sq_nonneg _) hw.le
      nlinarith only [hwide,hb]
    let Qtop := P.assignedReferenceFamily packets assigned T t (fun u => (T u).length)
      C w F hw hC0 hF hwideLocal hfrequency
    let origTop := P.assignedReferenceOriginalLabel packets assigned T t (fun u => (T u).length)
      C w F hw hC0 hF hwideLocal hfrequency
    let altTop := P.assignedReferenceAlternate packets assigned T t (fun u => (T u).length)
      C w F hw hC0 hF hwideLocal hfrequency alt
    let altTopBound := P.assignedReferenceAlternate_bound packets assigned T t (fun u => (T u).length)
      C w F hw hC0 hF hwideLocal hfrequency alt hAlt;
      (∀ u ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N →
        ‖((Qtop u).withProfile (altTop u) (altTopBound u)).rawInterval
          (fun j l item => P.physicalMultiplierCoefficient t b v f j (origTop u j l) item.val)
          0 lower upper z.1 (z.2-(T u).slope*z.1)‖ ≤ A0*(weight u z)^8) →
    grid.sourceActivePathValue tops slope precision cut weight (SourceParameters.blockCount L)
      (grid.sourceBoundaryGap L) packets assigned (fun u => stop u.1) value phase a α
      (Real.sqrt L) (L^A_M) shift top count z ≤
      (Real.exp 3*(1+(L^(qEnv+6))^(Real.sqrt L)*(L^A_M+1)^(α-1)))*
        ∏ j ∈ Finset.range count, reverseMarkedValue line (ShiftedBlocks.reverseLevel shift count)
          count marked (fun j xx => grid.sourceShiftedPathPrediction tops slope precision cut weight
            (SourceParameters.blockCount L) (grid.sourceBoundaryGap L) packets assigned
            (fun u => stop u.1) value phase a (Real.sqrt L) μ shift top (xx,y+slope top*xx) j) j x

theorem eventually_assigned_parent_marked_path_bound
    (q qEnv D Cmass A_M Cweight : ℝ) (hq : 0 ≤ q) (hD : 0 ≤ D) (hCmass : 0 ≤ Cmass)
    (hAM : 0 < A_M) (hchoice : 4*(max (3*q+13) (2*q+17)+3/2) ≤ A_M)
    (hCweight : 1 ≤ Cweight) (Klocal Hlocal : ℕ) :
    ∀ᶠ L : ℝ in atTop, assignedParentMarkedPathBoundAt q qEnv D Cmass A_M Cweight L Klocal Hlocal := by
  filter_upwards [eventually_original_parent_marked_path_bound q D Cmass (qEnv+6) A_M
    hq hD hCmass hAM hchoice Klocal Hlocal,
    eventually_assigned_original_node_envelope Cweight qEnv hCweight,
    eventually_assigned_original_offchild Cweight qEnv hCweight,
    eventually_ge_atTop (5:ℝ)] with L hmarked hnode hoff hL
  unfold assignedParentMarkedPathBoundAt
  intro N κ Label Item _ _ P horder hP alt hAlt t a d radius hd hradius hlocal
    b hb hb1 hsupp v hv f hf hf1 τ grid tops T A s w R C F hw hR slope precision
    hbranch hK shift hzero hp top htop hRtop hcone hF hwide hfrequency hparentCone hparentWide
    cut stop weight count phase hz Z Nmass α μ ha ha1 hZ hZL hphase hN hlogN
    hα hα3 hμ hrelation z packets assigned hassigned heligible hangle
    squarePackets Qsquare origSquare squareSelected S Q orig selected hsquareEvent hreference n finish value level transition base W amp
    origin y x hzpoint line mass marked hx hKw hwidth A0 hA0 hA0q hC0 hpacketShort
    hrootEligible hweight htotal hlog hroot hwideLocal Qtop origTop altTop altTopBound hinterval
  have hL0 : 0 < L := by linarith
  have hKbL := source_blockCount_le_square hL
  let M := fun u => grid.lastEligible cut (precision u) (div_pos hw (T u).length_pos)
  have hM u (hu : u ∈ tops) : grid.eligible cut (precision u) (M u) :=
    grid.eligible_lastEligible cut (precision u) (div_pos hw (T u).length_pos) (hrootEligible u hu)
  have hMmax u (hu : u ∈ tops) j (hj : grid.eligible cut (precision u) j) : j ≤ M u :=
    (grid.eligible_iff_le_lastEligible cut (precision u) (div_pos hw (T u).length_pos)
      (hrootEligible u hu) j).mp hj
  have hcondition u (hu : u ∈ packets) :
      P.referenceCondition t (T (assigned u)).slope (T (assigned u)).length C w u.1 u.2.1 := by
    refine ⟨hpacketShort u hu,?_⟩
    simpa only [mul_div_assoc] using hangle u hu
  have hn := hnode τ tops T N κ Label Item P packets assigned t (fun u => (T u).length)
    C w F hw hC0 hF hwideLocal hfrequency alt hAlt b v f grid cut (L^(A+2)) D
    (zero_lt_one.trans_le hKw) hassigned hpacketShort hcondition hzero
    (SourceParameters.blockCount L) hK hKbL (grid.sourceBoundaryGap L) phase M hM hMmax
    a Z A0 A ha ha1 hZ hZL hA0 hA0q (fun _ _ j _ => hz j) (fun _ _ j _ => hphase j)
    z hweight htotal hinterval
  have hw' := hoff τ tops T N κ Label Item P packets assigned t (fun u => (T u).length)
    C w F hw hC0 hF hwideLocal hfrequency alt hAlt b v f grid cut D hD
    hassigned hpacketShort hcondition hzero
    (SourceParameters.blockCount L) hK hKbL (grid.sourceBoundaryGap L) phase M hM hMmax
    a Z A0 A ha ha1 hZ hZL hA0 hA0q (fun _ _ j _ => hz j) (fun _ _ j _ => hphase j)
    z hweight htotal hinterval
  exact hmarked N κ Label Item P horder hP alt hAlt t a d radius hd hradius hlocal
    b hb hb1 hsupp v hv f hf hf1 τ grid tops T A s w R C F hw hR
    hbranch hK shift hzero hp top htop hRtop hcone hF hwide hfrequency hparentCone hparentWide
    phase hz Z Nmass α μ ha ha1 hZ hZL hphase hN hlogN hα hα3 hμ hrelation
    z packets assigned hassigned heligible hangle hsquareEvent hreference origin y x hzpoint hx hKw hwidth
    (L^(qEnv+6)) (Real.rpow_nonneg hL0.le _) hlog hroot hn hw'

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
