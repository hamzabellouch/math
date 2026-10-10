import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedParentCentralGain
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataActualReferenceArea

namespace OAI

/-! The actual parent/continuing reference union supplies every reference
event used in the original-packet central estimate. One good set is chosen
before all phases, and retains both its area and weighted bad-mass bounds. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_actual_reference_central_gain (hVariation : LepingleInput)
    (pProfile qEnv Cmass Cweight F c0 A_M d m decay maskExponent cStar cEta CEta cb Cb Lip cone : ℝ) (Dweight Kcount Hcount : ℕ)
    (hpProfile : 0 ≤ pProfile) (hqEnv : 0 ≤ qEnv) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hAM : 0 < A_M) (hchoice : 4*(max (3*pProfile+13) (2*pProfile+17)+3/2) ≤ A_M)
    (hDweight : 2 < (Dweight:ℝ)) (hd : 0 ≤ d) (hm : 0 ≤ m)
    (hqm : 2*(qEnv+6)+2 ≤ m) (hCmassM : Cmass ≤ m) (hdecay : 0 ≤ decay)
    (hMask : 1 < maskExponent) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hLip : 0 ≤ Lip)
    (hgap : cStar < cEta*cb) (hcone : 0 ≤ cone) (hconeK : cone ≤ Kcount) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item),
    ∀ (tops : Finset τ) (T : τ → SlopeBox)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (oldSlope w : ℝ) (hw : 0 < w)
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
    (∀ j l k s t, ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(w/P.length j))) →
    (∀ j l k s, b j l k s ≠ 0 →
      cb*w/P.length j ≤ |s-(oldSlope+P.rowSlope j l)| ∧
        |s-(oldSlope+P.rowSlope j l)| ≤ Cb*w/P.length j) →
    (∀ j l u k xi eta,
      planarAngularFourier (P.physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
    (∀ j l u k xi eta,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
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
    ∀ (Z0 : Set (ℝ×ℝ)), MeasurableSet Z0 →
    let wide : ∀ i : Option (Fin (SourceParameters.blockCount L)),
        (cone+(SourceParameters.branching L)^(if i.isNone then 3 else 2))*w ≤ P.width := by
      intro i
      cases i with
      | none => exact hwideParent
      | some i => exact hwideResidual
    let bad := P.actualReferenceBad alt hAlt L oldSlope cone w F hw hcone hF wide hfrequency
      b v f g tops T packets assigned hKb maskExponent pProfile
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
    ∀ (start Fmass : ℝ), 0 < Fmass → L/2 ≤ Real.log Nmass →
      (volume.prod volume) Z0 ≠ ∞ → (volume.prod volume).real Z0 ≤ Fmass →
      (∀ t ∈ tops, start ≤ (T t).slope ∧ (T t).slope ≤ start+g.rootWidth) →
      (∑ t ∈ tops, ∫ z, weight t z ∂volume.prod volume) ≤ L^m*Nmass^2*Fmass →
    let W := fun z => ∑ s ∈ packets,
      ((g.sourceBoundaryCoefficient tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut weight (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
        (stop s.1) (assigned s) a z : ℝ):ℂ) • original z s
    Integrable (sourceBadPathMass tops weight bad) (volume.prod volume) ∧
      (∫ z, sourceBadPathMass tops weight bad z ∂volume.prod volume) ≤
        (∑ t ∈ tops, (T t).length*(T t).width)*Real.exp (-10*L) ∧
      MeasurableSet good ∧ good ⊆ Z0 ∧
      (volume.prod volume) (Z0 \ good) ≤ ENNReal.ofReal
        ((∑ t ∈ tops, (T t).length*(T t).width)*Real.exp (-9*L)) ∧
      IntegrableOn (fun z => ‖W z‖) good (volume.prod volume) ∧
      (∫ z in good, ‖W z‖ ∂volume.prod volume) ≤ L^(-decay)*Nmass*Fmass := by
  filter_upwards [eventually_assigned_parent_central_gain pProfile qEnv Cmass Cweight F c0
      A_M d m decay Dweight Kcount Hcount hpProfile hqEnv hCmass hCweight hF hc0 hAM hchoice
      hDweight hd hm hqm hCmassM hdecay,
    eventually_actual_reference_area hVariation (Dweight:ℝ) (maskExponent+2) pProfile
      maskExponent F cStar cEta CEta cb Cb cone Lip Kcount Hcount
      hDweight hpProfile hMask hF hcStar hcEta hCEta hcb hCb hcone hLip hgap,
    SourceParameters.eventually_branching_ge (max 1 Cb),
    eventually_ge_atTop (256:ℝ)] with L hcentral harea0 hBlarge hL
  intro τ κ _ N Label Item _ P tops T packets assigned oldSlope w hw hwide hfrequency
    hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 hmotion hactive hspectrum haltSpectrum
    Kw R Q orig alts halt hwideResidual hwideParent hlocal hwidth horder hscale hX hZ
    hassigned hshort hcondition g hbranch htopWidth hzero hroot hKb hKbL Dphase Nmass A
    hD hDL hNmass hlogN hA hAq p mu a cut weight stop original countTop count
    Z0 hZ0 wide bad good hweight htotal hmass hconc hcount start Fmass hFmass hloglo
    hZ0finite hmeasure hslope hweightTotal W
  have hL1 : 1 ≤ L := by linarith
  have hKw : 1 ≤ Kw := Real.one_le_rpow hL1 (by linarith)
  have hfactor : 1 ≤ F*cone+2 := by nlinarith [mul_nonneg hF hcone]
  have hPabs : P.referenceEnvelopeConstant ≤ L^pProfile :=
    (le_mul_of_one_le_left P.referenceEnvelopeConstant_pos.le hfactor).trans hP
  have hDw : 2 < Dweight := by exact_mod_cast hDweight
  have horder6 : 6 ≤ P.order := by omega
  have hB : 1 ≤ SourceParameters.branching L := (le_max_left _ _).trans hBlarge
  have hCbB : Cb ≤ SourceParameters.branching L := (le_max_right _ _).trans hBlarge
  have hband : Cb*w ≤ P.width := by
    apply (mul_le_mul_of_nonneg_right (show Cb ≤ cone+(SourceParameters.branching L)^3 from ?_) hw.le).trans hwideParent
    exact (hCbB.trans (le_self_pow₀ hB (by norm_num))).trans (le_add_of_nonneg_left hcone)
  have hsupport : ∀ j l k s, b j l k s ≠ 0 →
      |s-(oldSlope+P.rowSlope j l)| ≤ (Kcount:ℝ)*(w/P.length j) := by
    intro j l k s hs
    exact (hsupp j l k s hs).trans
      (mul_le_mul_of_nonneg_right hconeK (div_pos hw (P.length_pos j)).le)
  have hpacketAngle : ∀ u ∈ packets,
      |oldSlope+P.rowSlope u.1 u.2.1-(T (assigned u)).slope| ≤ cone*(w/P.length u.1) := by
    intro u hu
    calc
      _ ≤ cone*w/P.length u.1 := (hcondition u hu).2
      _ = _ := by ring
  have ha := harea0 Kw hKw le_rfl N κ τ Label Item P horder6 hPabs alt hAlt oldSlope w hw
    wide hfrequency hband b hb hb1 hsupport hmotion hlocal hactive v hv f hf hf1 hspectrum haltSpectrum
    g tops T packets assigned hKb hshort hpacketAngle
    (fun u hu => htopWidth (assigned u) (hassigned u hu)) Z0 hZ0
  have hc := hcentral τ κ N Label Item P tops T packets assigned oldSlope cone w hw hcone hwide
    hfrequency hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 maskExponent (2*pProfile+11)
    (by linarith) hwideResidual hwideParent hconeK hlocal hwidth horder hscale hX hZ hassigned hshort hcondition
    g hbranch htopWidth hzero hroot hKb hKbL Dphase Nmass A hD hDL hNmass hlogN hA hAq
    Z0 bad hZ0 (fun t _ => P.actualReferenceBad_measurable alt hAlt L oldSlope cone w F hw hcone hF
      wide hfrequency b v f g tops T packets assigned hKb maskExponent pProfile t)
    hweight htotal hmass hconc hcount
    (by
      intro t _ z hz
      exact ha.2.2.2.2.2 t z hz.2 none)
    (by
      intro shift t _ z hz
      exact ha.2.2.2.2.2 t z hz.2 (some shift))
    start Fmass hFmass hloglo hZ0finite hmeasure hslope hweightTotal
  exact ⟨ha.1,ha.2.1,ha.2.2.1,ha.2.2.2.1,ha.2.2.2.2.1,hc.1,hc.2⟩

end LipschitzHilbert.PacketLatticeData

end

end OAI
