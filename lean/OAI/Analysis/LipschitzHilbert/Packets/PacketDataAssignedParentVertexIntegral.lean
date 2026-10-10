import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedParentPhysicalPlane
import OAI.Analysis.LipschitzHilbert.Trees.SourceVertexPlaneParameters
import OAI.Analysis.LipschitzHilbert.Trees.SourceSharedGoodPath

namespace OAI

/-! Actual simplex vertices satisfy the physical plane hypotheses.
The original per-top packet integrals consequently hold on one common
measurable good set, with only that top's bad event removed, and with
the common terminal count used by finite-tree interpolation. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_assigned_parent_vertex_integral
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
    ∀ (Dphase Nmass A : ℝ), 2 ≤ Dphase → 0 < Nmass → Real.log Nmass ≤ 2*L →
      0 ≤ A → A ≤ L^qEnv →
    ∀ (shift : Fin (SourceParameters.blockCount L))
      (eta : Fin (SourceParameters.blockCount L) → ℝ),
      Real.sqrt (∑ j, (eta j)^2) ≤ L^2 →
    let p := Real.sqrt L
    let mu := PhaseCombinatorics.phaseMu Dphase p
    let alpha := 2+PhaseCombinatorics.phaseParameter Dphase
    let a := mu/(SourceParameters.blockCount L:ℝ)
    let phase := phaseTubePoint (Pi.single shift mu) eta
    let phaseAll := fun j => phase (ShiftedBlocks.tag hKb j)
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let stop := fun j : Fin N => g.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let original := P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent
    let countTop := g.sourceTopTerminalCount T cut w hw hKb shift
    let count := tops.sup countTop
    let cost := 1+(L^(qEnv+6))^p*(L^A_M+1)^(alpha-1)
    ∀ (good : Set (ℝ×ℝ)) (bad : τ → Set (ℝ×ℝ)), MeasurableSet good →
      (∀ t ∈ tops, MeasurableSet (bad t)) →
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
    let S := fun t => g.fixedPathResidualPackets tops (fun u => (T u).slope)
      (fun u => w/(T u).length) cut packets assigned (fun u => stop u.1)
      (ShiftedBlocks.endpoint shift) (countTop t-1) (T t).slope
    let Qref := fun t => P.referenceFamily oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^2) w F hw (by positivity) hF hwideResidual hfrequency
    let origRef := fun t => P.referenceOriginalLabel oldSlope (T t).slope (R t)
      (cone+(SourceParameters.branching L)^2) w
    let selected := fun t => (Finset.univ : Finset (Qref t).PacketIndex).filter
      (fun u => (⟨u.1,⟨origRef t u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S t)
    (∀ t ∈ tops, ∀ z ∈ good \ bad t, z ∉ ((Qsquare t).restrictPackets (squareSelected t)).physicalReferenceBad
      ((Qsquare t).restrictedAlternate (fun j l => alt j (origSquare t j l)) (squareSelected t))
      ((Qsquare t).restrictedAlternate_bound (fun j l => alt j (origSquare t j l))
        (fun j l => hAlt j (origSquare t j l)) (squareSelected t))
      (T t).slope (w/P.topLength) (fun j l => b j (origSquare t j l)) v f
      (fun j l u => T (assigned ⟨j,⟨origSquare t j l,u.val⟩⟩))
      L maskExponent (pProfile+8) (2*pProfile+9) shortVariation) →
    (∀ t ∈ tops, ∀ z ∈ good \ bad t, z ∉ ((Qref t).restrictPackets (selected t)).physicalReferenceBad
      ((Qref t).restrictedAlternate (fun j l => alt j (origRef t j l)) (selected t))
      ((Qref t).restrictedAlternate_bound (fun j l => alt j (origRef t j l))
        (fun j l => hAlt j (origRef t j l)) (selected t))
      (T t).slope (w/P.topLength) (fun j l => b j (origRef t j l)) v f
      (fun j l u => T (assigned ⟨j,⟨origRef t j l,u.val⟩⟩))
      L maskExponent (pProfile+8) (2*pProfile+9) (2*pProfile+11)) →
    ∀ top ∈ tops,
      Integrable ((good \ bad top).indicator (fun z => weight top z*
        g.sourceActivePathValue tops (fun t => (T t).slope) (fun t => w/(T t).length)
          cut weight (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
          (fun u => stop u.1) original phaseAll a alpha p (L^A_M) shift top count z))
        (volume.prod volume) ∧
      (∫ z, (good \ bad top).indicator (fun x => weight top x*
        g.sourceActivePathValue tops (fun t => (T t).slope) (fun t => w/(T t).length)
          cut weight (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
          (fun u => stop u.1) original phaseAll a alpha p (L^A_M) shift top count x) z
        ∂volume.prod volume) ≤
        Real.exp (4+2*(Dweight:ℝ))*cost*(∫ z, weight top z ∂volume.prod volume) := by
  filter_upwards [eventually_assigned_parent_physical_plane_integral pProfile qEnv Cmass Cweight F c0 A_M
    Dweight Kcount Hcount hpProfile hqEnv hCmass hCweight hF hc0 hAM hchoice hDweight,
    eventually_ge_atTop (256:ℝ)] with L hplane hL
  intro τ κ _ tops T N Label Item _ P packets assigned oldSlope cone w hw hcone hwide
    hfrequency hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 maskExponent shortVariation
    hmask Kw R Q orig alts halt hwideResidual hwideParent hconeK hlocal hwidth horder hscale hX hZ
    hassigned hshort hcondition g hbranch htopWidth hzero hroot hKb hKbL Dphase Nmass A
    hD hNmass hlogN hA hAq shift eta heta p mu alpha a phase phaseAll cut weight stop
    original countTop count cost good bad hgood hbad hweight htotal hmass hconc hcount
    squarePackets Qsquare origSquare squareSelected S Qref origRef selected hsquareEvent hrefEvent
  have hparams := source_vertex_plane_parameters L Dphase (SourceParameters.blockCount L)
    hL hD hKb shift eta heta
  change 0 ≤ a ∧ a ≤ 1 ∧ 1 ≤ alpha ∧ alpha ≤ 3 ∧ (alpha-1)/p ≤ 1/12 ∧
    p*mu = alpha-1 ∧ (∀ j, ‖phase j‖ ≤ 2*L^2) ∧
    (∀ j, j ≠ shift → (phase j).re = 0) ∧ (phase shift).re = mu at hparams
  obtain ⟨ha,ha1,halpha,halpha3,hmu,hrelation,hphase,hother,hreal⟩ := hparams
  have hKw : 0 < Kw := Real.rpow_pos_of_pos (by linarith) _
  have hM : 0 ≤ L^A_M := Real.rpow_nonneg (by linarith) _
  apply g.source_top_shared_good_common_integral tops T cut w Kw (Dweight:ℝ) hw hKw
    (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
    (fun u => stop u.1) original phaseAll a alpha p (L^A_M) hM hKb shift
    (fun t => good \ bad t) good bad hgood hbad (fun _ _ => Set.Subset.rfl)
    (volume.prod volume) (Real.exp (4+2*(Dweight:ℝ))*cost)
  intro top htop
  have hct : countTop top ≤ count := Finset.le_sup htop
  exact hplane τ κ tops T N Label Item P packets assigned oldSlope cone w hw hcone hwide
    hfrequency hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 maskExponent shortVariation
    hmask hwideResidual hwideParent hconeK hlocal hwidth horder hscale hX hZ hassigned hshort hcondition
    g hbranch htopWidth hzero hroot hKb hKbL shift phase a (2*L^2) A Dphase Nmass alpha
    ha ha1 (by positivity) le_rfl hphase hother hreal hA hAq hD hNmass hlogN
    halpha halpha3 hmu hrelation top htop (good \ bad top) (hgood.diff (hbad top htop))
    (fun z hz => hweight z hz.1) (fun z hz => htotal z hz.1) (fun z hz => hmass z hz.1)
    (fun z hz => hconc z hz.1)
    (fun j hj z hz => hcount j (hj.trans_le hct) z hz.1)
    (hsquareEvent top htop) (hrefEvent top htop)

end LipschitzHilbert.PacketLatticeData

end

end OAI
