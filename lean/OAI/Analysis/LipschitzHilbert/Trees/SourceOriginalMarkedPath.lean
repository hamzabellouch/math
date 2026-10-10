import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalStoppedBound
import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedStoppedInputs
import OAI.Analysis.LipschitzHilbert.Trees.SourceStoppedMarking
import OAI.Analysis.LipschitzHilbert.Trees.SourceMarkedIntegral

namespace OAI

/-! The actual source cell marks and local original-packet estimates
supply the remaining hypotheses of the stopped-path theorem. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable

def originalMarkedPathBoundAt (q D Cmass qoff A_M L : ℝ) (Klocal Hlocal : ℕ) : Prop :=
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
    ∀ (Cex : ℝ), 0 ≤ Cex → Real.log (n 0) ≤ 3*L →
      grid.mass tops slope precision cut weight 0 (grid.index 0 (slope top)) z ≤ L^Cmass*Nmass →
      (∀ level cell, ‖grid.sourcePacketAmplitude tops slope precision cut weight
        (SourceParameters.blockCount L) (grid.sourceBoundaryGap L) packets assigned
        (fun u => stop u.1) (value z) phase a z level cell‖ ≤
          Cex*grid.mass tops slope precision cut weight level cell z) →
      (∀ lower upper, lower ≤ upper → ∀ sr,
        grid.mass tops slope precision cut weight lower (grid.index lower sr) z-
          grid.mass tops slope precision cut weight upper (grid.index upper sr) z < 1 →
        ‖grid.sourcePacketAmplitude tops slope precision cut weight
          (SourceParameters.blockCount L) (grid.sourceBoundaryGap L)
          (packets.filter (fun u => assigned u ∉ grid.cellTops tops slope precision cut
            upper (grid.index upper sr))) assigned (fun u => stop u.1) (value z)
          phase a z lower (grid.index lower sr)‖ ≤
          (L^qoff*Real.exp (-L*Real.log L))*(
            grid.mass tops slope precision cut weight lower (grid.index lower sr) z-
            grid.mass tops slope precision cut weight upper (grid.index upper sr) z)) →
    grid.sourceActivePathValue tops slope precision cut weight (SourceParameters.blockCount L)
      (grid.sourceBoundaryGap L) packets assigned (fun u => stop u.1) value phase a α
      (Real.sqrt L) (L^A_M) shift top count z ≤
      (Real.exp 3*(1+Cex^(Real.sqrt L)*(L^A_M+1)^(α-1)))*
        ∏ j ∈ Finset.range count, reverseMarkedValue line (ShiftedBlocks.reverseLevel shift count)
          count marked (fun j xx => grid.sourceShiftedPathPrediction tops slope precision cut weight
            (SourceParameters.blockCount L) (grid.sourceBoundaryGap L) packets assigned
            (fun u => stop u.1) value phase a (Real.sqrt L) μ shift top (xx,y+slope top*xx) j) j x

theorem eventually_original_marked_path_bound
    (q D Cmass qoff A_M : ℝ) (hq : 0 ≤ q) (hD : 0 ≤ D) (hCmass : 0 ≤ Cmass)
    (hAM : 0 < A_M) (hchoice : 4*(max (3*q+13) (2*q+17)+3/2) ≤ A_M)
    (Klocal Hlocal : ℕ) :
    ∀ᶠ L : ℝ in atTop, originalMarkedPathBoundAt q D Cmass qoff A_M L Klocal Hlocal := by

  filter_upwards [eventually_physical_stopped_bound q D Cmass qoff A_M hq hD hCmass
    hAM hchoice Klocal Hlocal,
    AngularGrid.eventually_source_stopped_marking D A_M hD hAM.le, eventually_ge_atTop (1:ℝ)]
    with L hphysical hmark hL
  unfold originalMarkedPathBoundAt
  intro N κ Label Item _ _ P horder hP alt hAlt t a d radius hd hradius hlocal
    b hb hb1 hsupp v hv f hf hf1 τ grid tops T A s w R C F hw hR slope precision
    hbranch hK shift hzero hp top htop hRtop hcone hF hwide hfrequency
    cut stop weight count phase hz Z Nmass α μ ha ha1 hZ hZL hphase hN hlogN
    hα hα3 hμ hrelation z packets assigned hassigned heligible hangle
    short S Q orig selected hshort hreference n finish value level transition base W amp
    origin y x hzpoint line mass marked hx hKw hwidth Cex hCex hlog hroot hnode hoff
  subst R
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hprecision : precision top = w/(T top).length := rfl
  have hterminal : ¬grid.eligible cut (precision top) (ShiftedBlocks.endpoint shift count) := by
    rw [hprecision]
    exact grid.firstIneligibleShiftedBlock_spec cut (w/(T top).length) (div_pos hw hR) hK shift
  have hwpos (u : τ) (zz : ℝ×ℝ) : 0 < weight u zz :=
    (T u).weight_pos (zero_lt_one.trans_le hKw) D zz
  have he := grid.source_stopped_local_envelope tops slope precision cut weight
    (fun u zz => (hwpos u zz).le) (SourceParameters.blockCount L) (grid.sourceBoundaryGap L)
    packets assigned (fun u => stop u.1) value phase a hK shift top z count
    (L^A_M) Cex (L^qoff*Real.exp (-L*Real.log L))
    (Real.rpow_nonneg hL0.le _) (by positivity)
    hterminal hnode hoff
  have hm := hmark τ grid tops T w (L^(A+2)) hw hKw hbranch hwidth
    hK shift top origin y
  have hmx := hm x (by simpa only [count,line] using hx)
  have hm0 : ∀ j < count, marked j
      (line.index (ShiftedBlocks.reverseLevel shift count (ShiftedBlocks.reverseIndex count j)) x).val →
        L^A_M < n j ∧ (1/4:ℝ) ≤ n j-n (j+1) := by
    simpa only [mass,n,hzpoint,count,line,marked,slope,precision,weight,cut] using hmx.1
  have hm1 : ∀ j < count, ¬marked j
      (line.index (ShiftedBlocks.reverseLevel shift count (ShiftedBlocks.reverseIndex count j)) x).val →
        1 ≤ n j-n (j+1) → n j ≤ L^A_M+1 ∧ n (j+1) ≤ L^A_M := by
    simpa only [mass,n,hzpoint,count,line,marked,slope,precision,weight,cut] using hmx.2
  have hnlast : n count ≤ L^A_M := by
    rw [show n count = 0 from grid.shiftedPathMass_terminal_zero tops slope precision cut
      weight shift top count hterminal z]
    exact Real.rpow_nonneg hL0.le _
  have hfinish : finish ≤ count := (firstMassStop_spec n count (L^A_M) hnlast).1
  have h := hphysical N κ Label Item P horder hP alt hAlt t a d radius hd hradius hlocal
    b hb hb1 hsupp v hv f hf hf1 τ grid tops slope precision T A s w (T top).length C F hw hR
    hbranch hK shift hzero hp top htop hprecision hcone hF hwide hfrequency
    phase hz Z Nmass α μ ha ha1 hZ hZL hphase hN hlogN hα hα3 hμ hrelation
    z packets assigned hassigned heligible hangle hshort hreference
    (level count) (fun j => marked j
      (line.index (ShiftedBlocks.reverseLevel shift count (ShiftedBlocks.reverseIndex count j)) x).val)
    Cex le_rfl hCex hlog hroot
    (fun j hj hm => (hm0 j hj hm).1)
    (fun j hj hm => (hm0 j (lt_of_lt_of_le hj hfinish) hm).2)
    (fun j hj _ hd => he.2 j hj hd)
    (fun j hj hm hd => (hm1 j (lt_of_lt_of_le hj hfinish) hm hd).2)
    (fun j hj hm hd => (hm1 j (lt_of_lt_of_le hj hfinish) hm hd).1)
    (fun j _ _ _ => he.1 j)
  simpa only [reverseMarkedValue,FiniteLineGrid.markedValue,hzpoint] using h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
