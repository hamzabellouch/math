import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedParentCentralInputs
import OAI.Analysis.LipschitzHilbert.Trees.SourceTypeUniformCentral

namespace OAI

/-! The original-packet central gain with one numerical threshold chosen
before the finite types and packet family. The fixed-family theorem is
retained separately; the proof uses the type-uniform moment chain. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable

theorem eventually_assigned_parent_central_gain
    (pProfile qEnv Cmass Cweight F c0 A_M d m decay : ℝ) (Dweight Kcount Hcount : ℕ)
    (hpProfile : 0 ≤ pProfile) (hqEnv : 0 ≤ qEnv) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hAM : 0 < A_M) (hchoice : 4*(max (3*pProfile+13) (2*pProfile+17)+3/2) ≤ A_M)
    (hDweight : 2 < (Dweight:ℝ)) (hd : 0 ≤ d) (hm : 0 ≤ m)
    (hqm : 2*(qEnv+6)+2 ≤ m) (hCmassM : Cmass ≤ m) (hdecay : 0 ≤ decay) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item),
    ∀ (tops : Finset τ) (T : τ → SlopeBox)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (oldSlope cone w : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone)
      (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (∀ k, c0/w ≤ |P.frequency k|) →
      (F*cone+2)*P.absoluteConstant ≤ L^pProfile →
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
    ∀ (Dphase Nmass A : ℝ), 2 ≤ Dphase → Dphase ≤ L^d → 0 < Nmass → Real.log Nmass ≤ 2*L →
      0 ≤ A → A ≤ L^qEnv →
    let p := Real.sqrt L
    let mu := PhaseCombinatorics.phaseMu Dphase p
    let a := mu/(SourceParameters.blockCount L:ℝ)
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let stop := fun j : Fin N => g.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let original := P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent
    let countTop := fun shift => g.sourceTopTerminalCount T cut w hw hKb shift
    let count := fun shift => tops.sup (countTop shift)
    ∀ (Z0 : Set (ℝ×ℝ)) (bad : τ → Set (ℝ×ℝ)), MeasurableSet Z0 →
      (∀ t ∈ tops, MeasurableSet (bad t)) →
    let good := sourceGoodPathSet Z0 tops weight bad L
    (∀ z ∈ Z0, ∀ t ∈ tops, weight t z ≤ Cweight) →
    (∀ z ∈ Z0, Real.log (max 1 (∑ t ∈ tops, weight t z)) ≤ 3*L) →
    (∀ z ∈ Z0, (∑ t ∈ tops, weight t z) ≤ L^Cmass*Nmass) →
    (∀ z ∈ Z0, ∀ t ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N → ∀ yy,
      |yy-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      let V := ((Q t).withProfile (alts t) (halt t)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig t j l) u.val)
        0 lower upper
      ‖V z.1 yy‖+(T t).width*
        ‖covariantSignal P.frequency (fun k zz => V z.1 zz k) yy‖ ≤ A*(weight t z)^8) →
    (∀ shift, ∀ j < count shift, ∀ z ∈ Z0, ∀ I : Finset τ, I ⊆ tops →
      (∀ t ∈ I, (T t).radius z ≤ L^(maskExponent+2)) →
      (∀ t ∈ I, w/(T t).length ≤ g.sourceGap L (ShiftedBlocks.endpoint shift (j+1))/
        (SourceParameters.branching L)^2) →
      (∀ t ∈ I, ∀ u ∈ I, |(T t).slope-(T u).slope| ≤ SourceParameters.branching L*
        g.sourceGap L (ShiftedBlocks.endpoint shift (j+1))) →
      (∀ t ∈ I, ∀ u ∈ I, t ≠ u →
        g.sourceGap L (ShiftedBlocks.endpoint shift (j+1)) ≤ |(T t).slope-(T u).slope|) →
      (I.card:ℝ) ≤ Dphase/100) →
    let squarePackets := fun t => sourceReferencePackets packets (fun u => P.length u.1)
      (fun u => oldSlope+P.rowSlope u.1 u.2.1) (R t) (T t).slope
      (cone+(SourceParameters.branching L)^3) w
    let Qsquare := fun t => P.referenceFamily oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^3) w F hw
      (add_nonneg hcone (pow_nonneg (SourceParameters.branching_pos L).le 3)) hF hwideParent hfrequency
    let origSquare := fun t => P.referenceOriginalLabel oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^3) w
    let squareSelected := fun t => (Finset.univ : Finset (Qsquare t).PacketIndex).filter
      (fun u => (⟨u.1,⟨origSquare t u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ squarePackets t)
    let S := fun shift t => g.fixedPathResidualPackets tops (fun u => (T u).slope)
      (fun u => w/(T u).length) cut packets assigned (fun u => stop u.1)
      (ShiftedBlocks.endpoint shift) (countTop shift t-1) (T t).slope
    let Qref := fun t => P.referenceFamily oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^2) w F hw (by positivity) hF hwideResidual hfrequency
    let origRef := fun t => P.referenceOriginalLabel oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^2) w
    let selected := fun shift t => (Finset.univ : Finset (Qref t).PacketIndex).filter
      (fun u => (⟨u.1,⟨origRef t u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S shift t)
    (∀ t ∈ tops, ∀ z ∈ Z0 \ bad t, z ∉ ((Qsquare t).restrictPackets (squareSelected t)).physicalReferenceBad
      ((Qsquare t).restrictedAlternate (fun j l => alt j (origSquare t j l)) (squareSelected t))
      ((Qsquare t).restrictedAlternate_bound (fun j l => alt j (origSquare t j l))
        (fun j l => hAlt j (origSquare t j l)) (squareSelected t))
      (T t).slope (w/P.topLength) (fun j l => b j (origSquare t j l)) v f
      (fun j l u => T (assigned ⟨j,⟨origSquare t j l,u.val⟩⟩))
      L maskExponent (pProfile+8) (2*pProfile+9) shortVariation) →
    (∀ shift, ∀ t ∈ tops, ∀ z ∈ Z0 \ bad t, z ∉ ((Qref t).restrictPackets (selected shift t)).physicalReferenceBad
      ((Qref t).restrictedAlternate (fun j l => alt j (origRef t j l)) (selected shift t))
      ((Qref t).restrictedAlternate_bound (fun j l => alt j (origRef t j l))
        (fun j l => hAlt j (origRef t j l)) (selected shift t))
      (T t).slope (w/P.topLength) (fun j l => b j (origRef t j l)) v f
      (fun j l u => T (assigned ⟨j,⟨origRef t j l,u.val⟩⟩))
      L maskExponent (pProfile+8) (2*pProfile+9) (2*pProfile+11)) →
    ∀ (start Fmass : ℝ), 0 < Fmass → L/2 ≤ Real.log Nmass →
      (volume.prod volume) Z0 ≠ ∞ → (volume.prod volume).real Z0 ≤ Fmass →
      (∀ t ∈ tops, start ≤ (T t).slope ∧ (T t).slope ≤ start+g.rootWidth) →
      (∑ t ∈ tops, ∫ z, weight t z ∂volume.prod volume) ≤ L^m*Nmass^2*Fmass →
    let W := fun z => ∑ s ∈ packets,
      ((g.sourceBoundaryCoefficient tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut weight (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
        (stop s.1) (assigned s) a z : ℝ):ℂ) • original z s
    IntegrableOn (fun z => ‖W z‖) good (volume.prod volume) ∧
      (∫ z in good, ‖W z‖ ∂volume.prod volume) ≤ L^(-decay)*Nmass*Fmass := by
  filter_upwards [eventually_assigned_parent_central_inputs pProfile qEnv Cmass Cweight F c0 A_M
    Dweight Kcount Hcount hpProfile hqEnv hCmass hCweight hF hc0 hAM hchoice hDweight,
    AngularGrid.eventually_source_central_from_paths_types
      (qEnv+6) A_M 0
      (Real.exp (4+2*(Dweight:ℝ))) d m decay
      (by linarith) hAM.le (by norm_num) (Real.exp_pos _).le hd hm hqm hdecay,
    eventually_ge_atTop (256:ℝ)] with L hinputs hcentral hL
  intro τ κ _ N Label Item _ P tops T packets assigned oldSlope cone w hw hcone hwide
    hfrequency hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 maskExponent shortVariation
    hmask Kw R Q orig alts halt hwideResidual hwideParent hconeK hlocal hwidth horder hscale hX hZ
    hassigned hshort hcondition g hbranch htopWidth hzero hroot hKb hKbL Dphase Nmass A
    hD hDL hNmass hlogN hA hAq p mu a cut weight stop
    original countTop count Z0 bad hZ0 hbad good hweight htotal hmass hconc hcount
    squarePackets Qsquare origSquare squareSelected S Qref origRef selected hsquareEvent hrefEvent start Fmass hFmass hloglo
    hZ0finite hmeasure hslope hweightTotal W
  have hL1 : 1 ≤ L := by linarith
  have hKw : 0 < Kw := Real.rpow_pos_of_pos (by linarith) _
  have hresult := hinputs τ κ tops T N Label Item P packets assigned oldSlope cone w hw hcone hwide
    hfrequency hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 maskExponent shortVariation
    hmask hwideResidual hwideParent hconeK hlocal hwidth horder hscale hX hZ hassigned hshort hcondition
    g hbranch htopWidth hzero hroot hKb hKbL Dphase Nmass A hD hNmass hlogN hA hAq
    Z0 bad hZ0 hbad hweight htotal hmass hconc hcount hsquareEvent hrefEvent
  obtain ⟨hgood,hsub,hcrude,hpaths⟩ := hresult
  have hfinite : (volume.prod volume) good ≠ ∞ :=
    ne_top_of_le_ne_top hZ0finite (measure_mono hsub)
  have : IsFiniteMeasure ((volume.prod volume).restrict good) :=
    isFiniteMeasure_restrict.mpr hfinite
  have hmeasureGood : ((volume.prod volume).restrict good).real univ ≤ Fmass := by
    rw [measureReal_restrict_apply_univ]
    exact (measureReal_mono hsub hZ0finite).trans hmeasure
  have hp (t : τ) (_ht : t ∈ tops) : 0 ≤ w/(T t).length :=
    (div_pos hw (T t).length_pos).le
  have hwpos (t : τ) (z : ℝ×ℝ) : 0 < weight t z := (T t).weight_pos hKw _ z
  have hwint (t : τ) (_ht : t ∈ tops) : Integrable (weight t) (volume.prod volume) :=
    (T t).weight_integrable hKw hDweight
  have hwmeas (t : τ) : Measurable (weight t) := ((T t).continuous_weight hKw _).measurable
  have hvalue (s : P.PacketIndex) : Measurable (fun z => original z s) :=
    (P.physicalMaskedValue_continuous alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent s).measurable
  have heligible (s : P.PacketIndex) (hs : s ∈ packets) :
      g.eligible cut (w/(T (assigned s)).length) (stop s.1) := by
    have hle : w/(T (assigned s)).length ≤ w/P.length s.1 :=
      div_le_div_of_nonneg_left hw.le (P.length_pos s.1) (hshort s hs)
    exact (mul_le_mul_of_nonneg_right hle (by positivity)).trans
      (g.eligible_lastEligible cut (w/P.length s.1) (div_pos hw (P.length_pos s.1)) (hzero s.1))
  have hterminal (i : Fin (SourceParameters.blockCount L)) :
      ∀ t ∈ tops, ¬g.eligible cut (w/(T t).length) (ShiftedBlocks.endpoint i (count i)) := by
    apply g.source_common_terminal tops (fun t => w/(T t).length) cut hp hKb i (countTop i)
    intro t _
    exact g.firstIneligibleShiftedBlock_spec cut (w/(T t).length)
      (div_pos hw (T t).length_pos) hKb i
  have hmass' (z : ℝ×ℝ) (hz : z ∈ good) :
      (∑ t ∈ tops, weight t z) ≤ L^m*Nmass := by
    apply (hmass z (hsub hz)).trans
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hL1 hCmassM) hNmass.le
  have hc := hcentral τ P.PacketIndex (ℝ×ℝ) κ Dphase (by linarith) hDL (volume.prod volume) g tops
    (fun t => (T t).slope) (fun t => w/(T t).length) cut weight hp hwpos hwint hwmeas
    (g.sourceBoundaryGap L) packets assigned (fun s => stop s.1) original hvalue hassigned heligible
    start Nmass Fmass hNmass hFmass hloglo hlogN hslope good hgood hmeasureGood hmass'
    hweightTotal hKb (fun i eta z hz c => hcrude i eta z hz 0 c) count (fun _ _ => bad)
    hterminal (by
      intro i eta heta
      obtain ⟨hnode,hbadMass,hint⟩ := hpaths i eta heta
      refine ⟨?_,hbadMass,?_,?_⟩
      · intro z hz j _ c
        exact hnode z hz (ShiftedBlocks.endpoint i j) c
      · intro t ht
        exact (hint t ht).1
      · intro t ht
        simpa only [Real.rpow_zero,mul_one] using (hint t ht).2)
  exact hc

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
