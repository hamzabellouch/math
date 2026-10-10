import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedPlaneIntegral
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataPathRegularity
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedParentMarkedBound

namespace OAI
/-! Literal physical reference events imply the original per-top plane bound.
The stopped-path comparison and all inhabited-model transports are proved
before applying the plane integral theorem. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_assigned_parent_physical_plane_integral
    (pProfile qEnv Cmass Cweight F c0 A_M : ℝ) (Dweight Kcount Hcount : ℕ)
    (hpProfile : 0 ≤ pProfile) (hqEnv : 0 ≤ qEnv) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hAM : 0 < A_M) (hchoice : 4*(max (3*pProfile+13) (2*pProfile+17)+3/2) ≤ A_M)
    (hDweight : 2 < (Dweight:ℝ)) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype κ]
      (tops : Finset τ) (T : τ → SlopeBox)
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (oldSlope cone w : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone)
      (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (∀ k, c0/w ≤ |P.frequency k|) →
      (F*cone+2)*P.referenceEnvelopeConstant ≤ L^pProfile →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 →
        |s-(oldSlope+P.rowSlope j l)| ≤ cone*(w/P.length j)) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (maskExponent shortVariation : ℝ), 0 ≤ maskExponent →
    let Kw := L^(maskExponent+2)
    let R := fun t => (T t).length
    let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt
    let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt
    ∀ (hwideResidual : (cone+(SourceParameters.branching L)^2)*w ≤ P.width)
      (hwideParent : (cone+(SourceParameters.branching L)^3)*w ≤ P.width),
    cone ≤ Kcount →
    (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) Hcount) →
    (∀ t ∈ tops, P.width ≤ Kw*(T t).width) →
    3+2*(8*Dweight+1) ≤ P.order →
    (∀ t ∈ tops, P.scale = 4*(Kw*(T t).width)) →
    (∀ u ∈ packets, |P.actualX u.1 u.2.1 u.2.2-(T (assigned u)).x|+P.length u.1 ≤
      Kw*(T (assigned u)).length) →
    (∀ u ∈ packets,
      |P.actualZ u.1 u.2.1 u.2.2+(oldSlope-(T (assigned u)).slope)*P.actualX u.1 u.2.1 u.2.2-
        ((T (assigned u)).y-(T (assigned u)).slope*(T (assigned u)).x)|+P.width ≤
      Kw*(T (assigned u)).width) →
    (∀ u ∈ packets, assigned u ∈ tops) →
    (∀ u ∈ packets, P.length u.1 ≤ (T (assigned u)).length) →
    (∀ u ∈ packets, P.referenceCondition oldSlope (T (assigned u)).slope
      (R (assigned u)) cone w u.1 u.2.1) →
    ∀ (g : AngularGrid), (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
      (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
      (∀ t ∈ tops, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) 0) →
    ∀ (hKb : 0 < SourceParameters.blockCount L), (SourceParameters.blockCount L:ℝ) ≤ L^2 →
    ∀ (shift : Fin (SourceParameters.blockCount L)) (phase : Fin (SourceParameters.blockCount L) → ℂ)
      (a Z A Dphase Nmass α : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → (∀ k, ‖phase k‖ ≤ Z) →
      (∀ k, k ≠ shift → (phase k).re = 0) →
      (phase shift).re = PhaseCombinatorics.phaseMu Dphase (Real.sqrt L) →
      0 ≤ A → A ≤ L^qEnv → 2 ≤ Dphase → 0 < Nmass → Real.log Nmass ≤ 2*L →
      1 ≤ α → α ≤ 3 → (α-1)/Real.sqrt L ≤ 1/12 →
      Real.sqrt L*PhaseCombinatorics.phaseMu Dphase (Real.sqrt L) = α-1 →
    ∀ (top : τ), top ∈ tops →
    ∀ (good : Set (ℝ×ℝ)), MeasurableSet good →
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let slope := fun t => (T t).slope
    let precision := fun t => w/(T t).length
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let stop := fun j : Fin N => g.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let original := P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent
    let phaseAll := fun k => phase (ShiftedBlocks.tag hKb k)
    let count := g.firstIneligibleShiftedBlock cut (precision top)
      (div_pos hw (T top).length_pos) hKb shift
    let active := g.sourceActivePathValue tops slope precision cut weight
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
      (fun u => stop u.1) original phaseAll a α (Real.sqrt L) (L^A_M) shift top count
    let cost := 1+(L^(qEnv+6))^(Real.sqrt L)*(L^A_M+1)^(α-1)
    (∀ z ∈ good, ∀ t ∈ tops, weight t z ≤ Cweight) →
    (∀ z ∈ good, Real.log (max 1 (∑ t ∈ tops, weight t z)) ≤ 3*L) →
    (∀ z ∈ good, (∑ t ∈ tops, weight t z) ≤ L^Cmass*Nmass) →
    (∀ z ∈ good, ∀ t ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N → ∀ yy,
      |yy-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      let V := ((Q t).withProfile (alts t) (halt t)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig t j l) u.val)
        0 lower upper
      ‖V z.1 yy‖+(T t).width*
        ‖covariantSignal P.frequency (fun k zz => V z.1 zz k) yy‖ ≤ A*(weight t z)^8) →
    (∀ j < count, ∀ z ∈ good, ∀ I : Finset τ, I ⊆ tops →
      (∀ t ∈ I, (T t).radius z ≤ L^(maskExponent+2)) →
      (∀ t ∈ I, precision t ≤ g.sourceGap L (ShiftedBlocks.endpoint shift (j+1))/
        (SourceParameters.branching L)^2) →
      (∀ t ∈ I, ∀ u ∈ I, |slope t-slope u| ≤ SourceParameters.branching L*
        g.sourceGap L (ShiftedBlocks.endpoint shift (j+1))) →
      (∀ t ∈ I, ∀ u ∈ I, t ≠ u →
        g.sourceGap L (ShiftedBlocks.endpoint shift (j+1)) ≤ |slope t-slope u|) →
      (I.card:ℝ) ≤ Dphase/100) →
    let squarePackets := sourceReferencePackets packets (fun u => P.length u.1)
      (fun u => oldSlope+P.rowSlope u.1 u.2.1) (R top) (slope top)
      (cone+(SourceParameters.branching L)^3) w
    let Qsquare := P.referenceFamily oldSlope (slope top) (R top)
      (cone+(SourceParameters.branching L)^3) w F hw
      (add_nonneg hcone (pow_nonneg (SourceParameters.branching_pos L).le 3)) hF hwideParent hfrequency
    let origSquare := P.referenceOriginalLabel oldSlope (slope top) (R top)
      (cone+(SourceParameters.branching L)^3) w
    let squareSelected := (Finset.univ : Finset Qsquare.PacketIndex).filter
      (fun u => (⟨u.1,⟨origSquare u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ squarePackets)
    let S := g.fixedPathResidualPackets tops slope precision cut packets assigned
      (fun u => stop u.1) (ShiftedBlocks.endpoint shift) (count-1) (slope top)
    let Qref := P.referenceFamily oldSlope (slope top) (R top)
      (cone+(SourceParameters.branching L)^2) w F hw (by positivity) hF hwideResidual hfrequency
    let origRef := P.referenceOriginalLabel oldSlope (slope top) (R top)
      (cone+(SourceParameters.branching L)^2) w
    let selected := (Finset.univ : Finset Qref.PacketIndex).filter
      (fun u => (⟨u.1,⟨origRef u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S)
    (∀ z ∈ good, z ∉ (Qsquare.restrictPackets squareSelected).physicalReferenceBad
      (Qsquare.restrictedAlternate (fun j l => alt j (origSquare j l)) squareSelected)
      (Qsquare.restrictedAlternate_bound (fun j l => alt j (origSquare j l))
        (fun j l => hAlt j (origSquare j l)) squareSelected)
      (slope top) (w/P.topLength) (fun j l => b j (origSquare j l)) v f
      (fun j l u => T (assigned ⟨j,⟨origSquare j l,u.val⟩⟩))
      L maskExponent (pProfile+8) (2*pProfile+9) shortVariation) →
    (∀ z ∈ good, z ∉ (Qref.restrictPackets selected).physicalReferenceBad
      (Qref.restrictedAlternate (fun j l => alt j (origRef j l)) selected)
      (Qref.restrictedAlternate_bound (fun j l => alt j (origRef j l))
        (fun j l => hAlt j (origRef j l)) selected)
      (slope top) (w/P.topLength) (fun j l => b j (origRef j l)) v f
      (fun j l u => T (assigned ⟨j,⟨origRef j l,u.val⟩⟩))
      L maskExponent (pProfile+8) (2*pProfile+9) (2*pProfile+11)) →
    Integrable (good.indicator (fun z => weight top z*active z)) (volume.prod volume) ∧
      (∫ z, good.indicator (fun z => weight top z*active z) z ∂volume.prod volume) ≤
        Real.exp (4+2*(Dweight:ℝ))*cost*(∫ z, weight top z ∂volume.prod volume) := by
  filter_upwards [eventually_assigned_model_plane_integral pProfile qEnv Cmass Cweight F c0 A_M
    Dweight Kcount Hcount hpProfile hqEnv hCmass hCweight hF hc0 hAM.le hDweight,
    eventually_assigned_parent_marked_path_bound pProfile qEnv (Dweight:ℝ) Cmass A_M Cweight
      hpProfile (by linarith) hCmass hAM hchoice hCweight Kcount Hcount,
    eventually_ge_atTop (256:ℝ)] with L hplane hmarked hL
  intro τ κ _ tops T N Label Item _ P packets assigned oldSlope cone w hw hcone hwide
    hfrequency hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 maskExponent shortVariation hmask
    Kw R Q orig alts halt hwideResidual hwideParent hconeK hlocal hwidth horder hscale hX hZ
    hassigned hshort hcondition g hbranch htopWidth hzero hroot hKb hKbL shift phase
    a Z A Dphase Nmass α ha ha1 hZ0 hZL hphase hother hreal hA hAq hD hNmass hlogN
    hα hα3 hμ hrelation top htop good hgood cut slope precision weight stop original phaseAll
    count active cost hweight htotal hmass hconc hcount
    squarePackets Qsquare origSquare squareSelected S Qref origRef selected hsquareEvent hrefEvent
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hKw : 1 ≤ Kw := Real.one_le_rpow hL1 (by linarith)
  have hwp (t : τ) (z : ℝ×ℝ) : 0 < weight t z :=
    (T t).weight_pos (zero_lt_one.trans_le hKw) (Dweight:ℝ) z
  have hwp0 (t : τ) (z : ℝ×ℝ) : 0 ≤ weight t z := (hwp t z).le
  have hactive : Measurable active :=
    P.physicalMaskedPath_measurable alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent g tops T w cut Kw
      (Dweight:ℝ) (zero_lt_one.trans_le hKw) (SourceParameters.blockCount L)
      (g.sourceBoundaryGap L) packets assigned (fun u => stop u.1) phaseAll
      a α (Real.sqrt L) (L^A_M) shift top count
  have hactive0 (z : ℝ×ℝ) (_hz : z ∈ good) : 0 ≤ active z :=
    g.sourceActivePathValue_nonneg tops slope precision cut weight hwp0
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
      (fun u => stop u.1) original phaseAll a α (Real.sqrt L) (L^A_M) shift top count z
  have hprecision (t : τ) (_ht : t ∈ tops) : 0 ≤ precision t :=
    (div_pos hw (T t).length_pos).le
  have hpacketOrder : 6 ≤ P.order := by
    have hd : 2 < Dweight := by exact_mod_cast hDweight
    omega
  have hP0 : P.referenceEnvelopeConstant ≤ L^pProfile := by
    have hc : 0 ≤ P.referenceEnvelopeConstant := P.referenceEnvelopeConstant_pos.le
    have hfac : 1 ≤ F*cone+2 := by nlinarith [mul_nonneg hF hcone]
    exact (le_mul_of_one_le_left hc hfac).trans hP
  have hphase0 (k : ℕ) : 0 ≤ (phaseAll k).re := by
    dsimp only [phaseAll]
    by_cases he : ShiftedBlocks.tag hKb k = shift
    · rw [he,hreal]
      exact (source_phaseMu_small (by linarith) hL).1.le
    · rw [hother _ he]
  have heligible (u : P.PacketIndex) (hu : u ∈ packets) :
      g.eligible cut (precision (assigned u)) (stop u.1) := by
    have hle : precision (assigned u) ≤ w/P.length u.1 :=
      div_le_div_of_nonneg_left hw.le (P.length_pos u.1) (hshort u hu)
    exact (mul_le_mul_of_nonneg_right hle (by positivity)).trans
      (g.eligible_lastEligible cut (w/P.length u.1) (div_pos hw (P.length_pos u.1)) (hzero u.1))
  have hangle (u : P.PacketIndex) (hu : u ∈ packets) :
      |oldSlope+P.rowSlope u.1 u.2.1-slope (assigned u)| ≤ cone*(w/P.length u.1) := by
    simpa only [mul_div_assoc] using (hcondition u hu).2
  apply hplane τ κ tops T N Label Item P packets assigned oldSlope cone w hw hcone hwide
    hfrequency hfrequencyLo hP alt hAlt b hb hb1 v hv f hf hf1 maskExponent hmask
    hconeK hlocal hwidth horder hscale hX hZ hassigned hshort hcondition
    g hbranch htopWidth hzero hroot hKb hKbL shift phase a Z A Dphase Nmass α
    ha ha1 hZ0 hZL hphase hother hreal hA hAq hD hNmass hlogN top htop good hgood
    hactive hactive0 hweight htotal hmass hconc hcount
  intro k y x hx hz
  let z : ℝ×ℝ := (x,y+slope top*x)
  have hnpos : 0 < g.shiftedPathMass tops slope precision cut weight shift top z 0 := by
    apply g.shiftedPathMass_pos tops slope precision cut weight hwp shift top htop z 0
    simpa only [ShiftedBlocks.endpoint_zero] using hroot top htop
  have hnle := g.shiftedPathMass_le_total tops slope precision cut weight hwp0 shift top z 0
  have hnlog : Real.log (g.shiftedPathMass tops slope precision cut weight shift top z 0) ≤ 3*L :=
    (Real.log_le_log hnpos (hnle.trans (le_max_right 1 _))).trans (htotal z hz)
  have hmass0 : g.mass tops slope precision cut weight 0 (g.index 0 (slope top)) z ≤
      L^Cmass*Nmass :=
    (g.mass_le_total tops slope precision cut weight hwp0 0 (g.index 0 (slope top)) z).trans (hmass z hz)
  have hbnd := hmarked N κ Label Item P hpacketOrder hP0 alt hAlt oldSlope a
    (fun j => w/P.length j) (fun _ => cone) (fun j => div_pos hw (P.length_pos j))
    (fun _ => hconeK) hlocal b hb hb1 hsupp v hv f hf hf1 τ g tops T maskExponent
    shortVariation w (T top).length cone F hw (T top).length_pos hbranch hKb shift hzero
    hprecision top htop rfl (by positivity) hF hwideResidual hfrequency
      (add_nonneg hcone (pow_nonneg (SourceParameters.branching_pos L).le 3)) hwideParent
    phaseAll hphase0 Z Nmass α (PhaseCombinatorics.phaseMu Dphase (Real.sqrt L))
    ha ha1 hZ0 hZL (fun j => hphase _) hNmass hlogN hα hα3 hμ hrelation
    z packets assigned hassigned heligible hangle (hsquareEvent z hz) (hrefEvent z hz)
    (sourceLineScale g L w (ShiftedBlocks.endpoint shift count)*k) y x rfl hx hKw htopWidth
    A hA hAq hcone hshort hroot (hweight z hz) (htotal z hz) hnlog hmass0
    (by
      intro t ht lower upper hlu hu
      have hc := hconc z hz t ht lower upper hlu hu (z.2-(T t).slope*z.1) (by simpa using (T t).width_pos.le)
      exact (le_add_of_nonneg_right (mul_nonneg (T t).width_pos.le (norm_nonneg _))).trans hc)
  exact hbnd

end LipschitzHilbert.PacketLatticeData

end

end OAI
