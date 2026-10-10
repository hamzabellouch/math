import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalFullResidual
import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalUnaryEndpoint
import OAI.Analysis.LipschitzHilbert.Trees.SourceShiftedReferenceVariation
import OAI.Analysis.LipschitzHilbert.Trees.SourceStoppedMassPower
import OAI.Analysis.LipschitzHilbert.Trees.SourceMarkedResidual
import OAI.Analysis.LipschitzHilbert.Packets.SourcePacketStoppedBound
import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictableDecay

namespace OAI

/-! The two literal physical reference events discharge the square and
variation inputs of the stopped path estimate. The propagated unary
residual and mass power estimates follow from the active mass path itself.
The remaining local hypotheses concern marking and off-child amplitudes. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable

/-- The exact physical stopped-path statement at one manuscript scale.
Separating its dependent data from the eventual proof keeps elaboration local. -/
def physicalStoppedBoundAt (q D Cmass qoff A_M L : ℝ) (Klocal Hlocal : ℕ) : Prop :=
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
    ∀ (τ : Type*) (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
      (T : τ → SlopeBox) (A s w R C F : ℝ) (hw : 0 < w) (hR : 0 < R),
      (grid.branching:ℝ) = SourceParameters.step L →
    ∀ (hK : 0 < SourceParameters.blockCount L) (shift : Fin (SourceParameters.blockCount L)),
      (∀ j : Fin N, grid.eligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (w/P.length j) 0) → (∀ top ∈ tops, 0 ≤ precision top) →
    ∀ (top : τ), top ∈ tops → precision top = w/R →
    ∀ (hcone : 0 ≤ C+(SourceParameters.branching L)^2) (hF : 0 ≤ F)
      (hwide : (C+(SourceParameters.branching L)^2)*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
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
    let short := packets.filter (fun u => P.length u.1 ≤ R)
    let S := grid.fixedPathResidualPackets tops slope precision cut packets assigned
      (fun u => stop u.1) (ShiftedBlocks.endpoint shift) (count-1) (slope top)
    let Q := P.referenceFamily t (slope top) R (C+(SourceParameters.branching L)^2) w F
      hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel t (slope top) R (C+(SourceParameters.branching L)^2) w
    let selected := (Finset.univ : Finset Q.PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S)
    z ∉ (P.restrictPackets short).physicalReferenceBad
      (P.restrictedAlternate alt short) (P.restrictedAlternate_bound alt hAlt short)
      t a b v f (fun j l u => T (assigned ⟨j,⟨l,u.val⟩⟩)) L A (q+8) (2*q+9) s →
    z ∉ (Q.restrictPackets selected).physicalReferenceBad
      (Q.restrictedAlternate (fun j l => alt j (orig j l)) selected)
      (Q.restrictedAlternate_bound (fun j l => alt j (orig j l))
        (fun j l => hAlt j (orig j l)) selected)
      (slope top) a (fun j l => b j (orig j l)) v f
      (fun j l u => T (assigned ⟨j,⟨orig j l,u.val⟩⟩)) L A (q+8) (2*q+9) (2*q+11) →
    let n := grid.shiftedPathMass tops slope precision cut weight shift top z
    let finish := firstMassStop n count (L^A_M)
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A
    let level := ShiftedBlocks.endpoint shift
    let transition := grid.sourceTransition tops slope precision cut weight
      (SourceParameters.blockCount L) (grid.sourceBoundaryGap L) phase z
    let base := grid.sourcePacketBase tops slope precision cut weight assigned
      (fun u => stop u.1) (value z) a z
    let W := fun j => grid.packetAmplitude
      (packets.filter fun u => assigned u ∉ grid.cellTops tops slope precision cut
        (level (j+1)) (grid.index (level (j+1)) (slope top)))
      (fun u => slope (assigned u)) (fun u => stop u.1) base transition
      (level j) (grid.index (level j) (slope top))
    let amp := grid.sourceShiftedPathAmplitude tops slope precision cut weight
      (SourceParameters.blockCount L) (grid.sourceBoundaryGap L) packets assigned
      (fun u => stop u.1) value phase a shift top z
    ∀ (H : ℕ) (marked : ℕ → Prop) (Cex : ℝ), level count ≤ H → 0 ≤ Cex →
      Real.log (n 0) ≤ 3*L →
      grid.mass tops slope precision cut weight 0 (grid.index 0 (slope top)) z ≤ L^Cmass*Nmass →
      (∀ j < count, marked j → L^A_M < n j) →
      (∀ j < finish, marked j → (1/4:ℝ) ≤ n j-n (j+1)) →
      (∀ j < finish, ¬marked j → n j-n (j+1) < 1 →
        ‖W j‖ ≤ (L^qoff*Real.exp (-L*Real.log L))*(n j-n (j+1))) →
      (∀ j < finish, ¬marked j → 1 ≤ n j-n (j+1) → n (j+1) ≤ L^A_M) →
      (∀ j < finish, ¬marked j → 1 ≤ n j-n (j+1) → n j ≤ L^A_M+1) →
      (∀ j < finish, ¬marked j → 1 ≤ n j-n (j+1) → ‖amp j‖ ≤ Cex*n j) →
    grid.sourceActivePathValue tops slope precision cut weight (SourceParameters.blockCount L)
      (grid.sourceBoundaryGap L) packets assigned (fun u => stop u.1) value phase a α
      (Real.sqrt L) (L^A_M) shift top count z ≤
      (Real.exp 3*(1+Cex^(Real.sqrt L)*(L^A_M+1)^(α-1)))*
        ∏ j ∈ Finset.range count, if marked j then
          grid.sourceShiftedPathPrediction tops slope precision cut weight
            (SourceParameters.blockCount L) (grid.sourceBoundaryGap L) packets assigned
            (fun u => stop u.1) value phase a (Real.sqrt L) μ shift top z j else 1

theorem eventually_physical_stopped_bound
    (q D Cmass qoff A_M : ℝ) (hq : 0 ≤ q) (hD : 0 ≤ D) (hCmass : 0 ≤ Cmass)
    (hAM : 0 < A_M) (hchoice : 4*(max (3*q+13) (2*q+17)+3/2) ≤ A_M)
    (Klocal Hlocal : ℕ) :
    ∀ᶠ L : ℝ in atTop, physicalStoppedBoundAt q D Cmass qoff A_M L Klocal Hlocal := by
  have hchoice' : 4*(max (3*q+13) ((2*q+11)+6)+3/2) ≤ A_M := by
    simpa only [show (2*q+11)+6 = 2*q+17 by ring] using hchoice
  filter_upwards [eventually_physical_full_residual_square q D hq hD Klocal Hlocal,
    eventually_selected_active_physical_unary_tail Cmass hCmass,
    AngularGrid.eventually_source_packet_stopped_bound (3*q+13) (2*q+11) qoff 6 A_M hAM hchoice',
    (tendsto_rpow_atTop hAM).eventually_ge_atTop 4,eventually_ge_atTop (9:ℝ)]
    with L hsquare htail hbound hM hL
  unfold physicalStoppedBoundAt
  intro N κ Label Item _ _ P horder hP alt hAlt t a d radius hd hradius hlocal
    b hb hb1 hsupp v hv f hf hf1 τ grid tops slope precision T A s w R C F hw hR
    hbranch hK shift hzero hp top htop hprecision hcone hF hwide hfrequency
    cut stop weight count phase hz Z Nmass α μ ha ha1 hZ hZL hphase hN hlogN
    hα hα3 hμ hrelation z packets assigned hassigned heligible hangle
    short S Q orig selected hshort hreference n finish value level transition base W amp
    H marked Cex hH hCex hlog hroot hmarked hdrop hW hexstop hexmass hexamp
  let profile := P.selectedPhysicalPrefix alt hAlt t b v f
    (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A S stop z
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hKL := source_blockCount_le_square (show 5 ≤ L by linarith)
  have hwpos (top : τ) (z : ℝ×ℝ) : 0 < weight top z :=
    (T top).weight_pos (Real.rpow_pos_of_pos hL0 _) D z
  have hterminal : ¬grid.eligible cut (precision top) (ShiftedBlocks.endpoint shift count) := by
    rw [hprecision]
    exact grid.firstIneligibleShiftedBlock_spec cut (w/R) (div_pos hw hR) hK shift
  have hnlast : n count ≤ L^A_M := by
    rw [show n count = 0 from grid.shiftedPathMass_terminal_zero tops slope precision cut
      weight shift top count hterminal z]
    positivity
  have hfinish := (firstMassStop_spec n count (L^A_M) hnlast).1
  have hnanti := grid.shiftedPathMass_antitone tops slope precision cut weight hp
    (fun top z => (hwpos top z).le) hK shift top htop z
  have hS : ∀ u ∈ S, P.referenceCondition t (slope top) R
      (C+(SourceParameters.branching L)^2) w u.1 u.2.1 := by
    intro u hu
    obtain ⟨huP,j,hj,hstop,hchild⟩ := Finset.mem_filter.mp hu
    have href : grid.eligible cut (w/R) (ShiftedBlocks.endpoint shift (j+1)) := by
      apply grid.eligible_before_firstIneligibleShiftedBlock
      omega
    have hcell := ((grid.mem_cellTops _ _ _ _ _ _ _).mp hchild).2.1
    have hg := grid.residual_packet_length_and_cone hw (SourceParameters.branching_pos L)
      (P.length_pos u.1) hR (hzero u.1) hstop.2 href hcell (hangle u huP)
    exact ⟨hg.1.le,by simpa only [mul_div_assoc] using hg.2⟩
  have hvariation : finiteCubicVariation (fun k => profile (min k H)) (2*H) ≤
      (L^(2*q+11))^3 := by
    exact P.referenceFamily_selected_good_bound t (slope top) R
      (C+(SourceParameters.branching L)^2) w F hw hcone hF hwide hfrequency
      alt hAlt b v f (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A S hS stop
      (grid.source_length_stopping_antitone cut hw P.length P.length_pos P.length_antitone)
      a (q+8) (2*q+9) (2*q+11) z hreference H
  have hfull := hsquare N κ Label Item P horder hP alt hAlt t a d radius hd hradius hlocal
    b hb hb1 hsupp v hv f hf hf1 τ grid tops slope precision T A s w R hw hR hbranch hK
    shift hzero hp phase hz a ha ha1 z packets assigned hassigned heligible hshort (slope top)
  apply hbound τ P.PacketIndex (ℝ×ℝ) κ
    (SourceParameters.blockCount L) (EuclideanSpace ℂ κ) grid tops slope precision
    cut weight hp hwpos (SourceParameters.blockCount L) hK (grid.sourceBoundaryGap L)
    packets assigned (fun u => stop u.1) value phase a α μ hz hrelation hassigned heligible
    hK shift top htop z count H hH hterminal marked profile Cex hα
    (hα3.trans ((Real.le_sqrt (by norm_num) hL0.le).mpr (by nlinarith))) hμ hCex
    hlog hmarked hdrop
  · exact marked_prefix_square_le _ count _ hfinish marked hfull
  · intro j hj
    exact stopped_mass_power_le_exp_sqrt n count (L^A_M) L α hL1
      (Real.rpow_nonneg hL0.le _) hnanti hnlast hα hα3 hlog hj
  · exact hvariation
  · exact hW
  · intro e fEnd hef hfEnd hdiff _ j hj
    exact htail N κ Label Item P alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) A τ grid tops slope precision cut weight hp hwpos
      (SourceParameters.blockCount L) hK hKL shift (grid.sourceBoundaryGap L) packets assigned
      stop phase a Z Nmass ha ha1 hZ hZL hN hlogN z count top htop hterminal
      (L^A_M) hM H hH hroot (fun k _ => hz k) (fun k _ => hphase k) e fEnd hef hfEnd hdiff j hj
  · exact hexstop
  · exact hexmass
  · exact hexamp

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
