import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedParentVertexIntegral
import OAI.Analysis.LipschitzHilbert.Trees.SourceVertexPlaneParameters
import OAI.Analysis.LipschitzHilbert.Trees.SourceSharedGoodPath
import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedTubeEnvelope
import OAI.Analysis.LipschitzHilbert.Trees.SourceGoodPathBudget

namespace OAI

/-! The actual concentration and reference good set supplies every local
input used by central interpolation: the original node bounds, weighted
bad-path budget and common-count original vertex integrals. No moment,
path-product or plane estimate is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable

theorem eventually_assigned_parent_central_inputs
    (pProfile qEnv Cmass Cweight F c0 A_M : ℝ) (Dweight Kcount Hcount : ℕ)
    (hpProfile : 0 ≤ pProfile) (hqEnv : 0 ≤ qEnv) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hAM : 0 < A_M) (hchoice : 4*(max (3*pProfile+13) (2*pProfile+17)+3/2) ≤ A_M)
    (hDweight : 2 < (Dweight:ℝ)) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype κ]
      (tops : Finset τ) (T : τ → SlopeBox)
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : SourceLabeledLattice N κ Label Item)
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
    ∀ (Dphase Nmass A : ℝ), 2 ≤ Dphase → 0 < Nmass → Real.log Nmass ≤ 2*L →
      0 ≤ A → A ≤ L^qEnv →
    let p := Real.sqrt L
    let mu := PhaseCombinatorics.phaseMu Dphase p
    let alpha := 2+PhaseCombinatorics.phaseParameter Dphase
    let a := mu/(SourceParameters.blockCount L:ℝ)
    let phase := fun (shift : Fin (SourceParameters.blockCount L)) eta j =>
      phaseTubePoint (Pi.single shift mu) eta (ShiftedBlocks.tag hKb j)
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let stop := fun j : Fin N => g.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let original := P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent
    let countTop := fun shift => g.sourceTopTerminalCount T cut w hw hKb shift
    let count := fun shift => tops.sup (countTop shift)
    let cost := 1+(L^(qEnv+6))^p*(L^A_M+1)^(alpha-1)
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
    MeasurableSet good ∧ good ⊆ Z0 ∧
    (∀ (shift : Fin (SourceParameters.blockCount L))
      (eta' : Fin (SourceParameters.blockCount L) → ℝ) z, z ∈ good → ∀ level cell,
      ‖g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut weight (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
        (fun u => stop u.1) (original z)
        (phase shift eta')
        a z level cell‖ ≤
          L^(2*(qEnv+6))*(1+Real.sqrt (∑ j, (eta' j)^2))*
            g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
              cut weight level cell z) ∧
    ∀ (shift : Fin (SourceParameters.blockCount L)) (eta : Fin (SourceParameters.blockCount L) → ℝ),
      Real.sqrt (∑ j, (eta j)^2) ≤ L^2 →
    (∀ z ∈ good, ∀ level cell,
      ‖g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut weight (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
        (fun u => stop u.1) (original z) (phase shift eta) a z level cell‖ ≤
          L^(qEnv+6)*g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
            cut weight level cell z) ∧
    (∀ z ∈ good, cost*(∑ t ∈ tops.filter (fun t => z ∈ bad t), weight t z) ≤ 1/2) ∧
    ∀ top ∈ tops,
      Integrable ((good \ bad top).indicator (fun z => weight top z*
        g.sourceActivePathValue tops (fun t => (T t).slope) (fun t => w/(T t).length)
          cut weight (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
          (fun u => stop u.1) original (phase shift eta) a alpha p (L^A_M) shift top (count shift) z))
        (volume.prod volume) ∧
      (∫ z, (good \ bad top).indicator (fun x => weight top x*
        g.sourceActivePathValue tops (fun t => (T t).slope) (fun t => w/(T t).length)
          cut weight (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
          (fun u => stop u.1) original (phase shift eta) a alpha p (L^A_M) shift top (count shift) x) z
        ∂volume.prod volume) ≤
        Real.exp (4+2*(Dweight:ℝ))*cost*(∫ z, weight top z ∂volume.prod volume) := by
  filter_upwards [eventually_assigned_parent_vertex_integral pProfile qEnv Cmass Cweight F c0 A_M
    Dweight Kcount Hcount hpProfile hqEnv hCmass hCweight hF hc0 hAM hchoice hDweight,
    eventually_assigned_original_node_envelope Cweight qEnv hCweight,
    eventually_assigned_original_tube_envelope Cweight qEnv hCweight,
    eventually_source_stop_cost_small (qEnv+6) A_M (by linarith) hAM.le,
    eventually_ge_atTop (256:ℝ)] with L hvertex hnode htube hbudget hL
  intro τ κ _ tops T N Label Item _ P packets assigned oldSlope cone w hw hcone hwide
    hfrequency hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 maskExponent shortVariation
    hmask Kw R Q orig alts halt hwideResidual hwideParent hconeK hlocal hwidth horder hscale hX hZ
    hassigned hshort hcondition g hbranch htopWidth hzero hroot hKb hKbL Dphase Nmass A
    hD hNmass hlogN hA hAq p mu alpha a phase cut weight stop
    original countTop count cost Z0 bad hZ0 hbad good hweight htotal hmass hconc hcount
    squarePackets Qsquare origSquare squareSelected S Qref origRef selected hsquareEvent hrefEvent
  have hL1 : 1 ≤ L := by linarith
  have hKw : 0 < Kw := Real.rpow_pos_of_pos (by linarith) _
  have hmu0 : 0 ≤ mu := (source_phaseMu_small (by linarith) hL).1.le
  have hmu1 : mu ≤ 1 := (source_phaseMu_small (by linarith) hL).2.trans (by norm_num)
  have hKreal : (1:ℝ) ≤ SourceParameters.blockCount L := by
    exact_mod_cast (show 1 ≤ SourceParameters.blockCount L from hKb)
  have ha : 0 ≤ a := div_nonneg hmu0 (zero_le_one.trans hKreal)
  have ha1 : a ≤ 1 := (div_le_self hmu0 hKreal).trans hmu1
  have htheta := PhaseCombinatorics.phaseParameter_range (by linarith : 1 ≤ Dphase)
  change 0 < PhaseCombinatorics.phaseParameter Dphase ∧
    PhaseCombinatorics.phaseParameter Dphase ≤ 1/3 at htheta
  have halpha : 1 ≤ alpha := by dsimp only [alpha]; linarith [htheta.1]
  have halpha3 : alpha ≤ 3 := by dsimp only [alpha]; linarith [htheta.2]
  have hwpos (t : τ) (z : ℝ×ℝ) : 0 < weight t z := (T t).weight_pos hKw _ z
  have hw0 (t : τ) (z : ℝ×ℝ) : 0 ≤ weight t z := (hwpos t z).le
  have hwmeas (t : τ) : Measurable (weight t) := ((T t).continuous_weight hKw _).measurable
  have hbadMass : Measurable (sourceBadPathMass tops weight bad) :=
    Finset.measurable_sum tops (fun t ht => (hwmeas t).indicator (hbad t ht))
  have hgood : MeasurableSet good :=
    hZ0.inter (measurableSet_le hbadMass measurable_const)
  have hsub : good ⊆ Z0 := Set.inter_subset_left
  have hraw (z : ℝ×ℝ) (hz : z ∈ good) (t : τ) (ht : t ∈ tops)
      (lower upper : ℕ) (hlu : lower ≤ upper) (hu : upper ≤ N) :
      ‖((Q t).withProfile (alts t) (halt t)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig t j l) u.val)
        0 lower upper z.1 (z.2-(T t).slope*z.1)‖ ≤ A*(weight t z)^8 := by
    have hc := hconc z (hsub hz) t ht lower upper hlu hu
      (z.2-(T t).slope*z.1) (by simpa using (T t).width_pos.le)
    exact (le_add_of_nonneg_right (mul_nonneg (T t).width_pos.le (norm_nonneg _))).trans hc
  let M := fun t => g.lastEligible cut (w/(T t).length) (div_pos hw (T t).length_pos)
  have hM (t : τ) (ht : t ∈ tops) : g.eligible cut (w/(T t).length) (M t) :=
    g.eligible_lastEligible cut (w/(T t).length) (div_pos hw (T t).length_pos) (hroot t ht)
  have hMmax (t : τ) (ht : t ∈ tops) (j : ℕ)
      (hj : g.eligible cut (w/(T t).length) j) : j ≤ M t :=
    (g.eligible_iff_le_lastEligible cut (w/(T t).length)
      (div_pos hw (T t).length_pos) (hroot t ht) j).mp hj
  have hre (shift : Fin (SourceParameters.blockCount L)) (eta' : Fin (SourceParameters.blockCount L) → ℝ) (j : ℕ) :
      0 ≤ (phaseTubePoint (Pi.single shift mu) eta' (ShiftedBlocks.tag hKb j)).re :=
    sourceShiftSimplex_phase_re (Pi.single shift mu) eta'
      (sourceShiftSimplex_vertex hmu0 shift) _
  refine ⟨hgood,hsub,?_,?_⟩
  · intro shift eta' z hz level cell
    let r := Real.sqrt (∑ j, (eta' j)^2)
    let Z := mu+r
    have hr : 0 ≤ r := Real.sqrt_nonneg _
    have hZ0 : 0 ≤ Z := add_nonneg hmu0 hr
    have hZr : Z ≤ 1+r := by dsimp only [Z]; linarith
    have hnorm (j : ℕ) :
        ‖phaseTubePoint (Pi.single shift mu) eta' (ShiftedBlocks.tag hKb j)‖ ≤ Z :=
      sourceShiftSimplex_phase_norm (Pi.single shift mu) eta'
        (sourceShiftSimplex_vertex hmu0 shift) _
    have ht := htube τ tops T N κ Label Item P packets assigned oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt b v f g cut Kw (Dweight:ℝ) hKw
      hassigned hshort hcondition hzero (SourceParameters.blockCount L) hKb hKbL
      (g.sourceBoundaryGap L)
      (fun j => phaseTubePoint (Pi.single shift mu) eta' (ShiftedBlocks.tag hKb j))
      M hM hMmax a Z A maskExponent r ha ha1 hZ0 hr hZr hA hAq
      (fun _ _ j _ => hre shift eta' j) (fun _ _ j _ => hnorm j) z
      (hweight z (hsub hz)) (htotal z (hsub hz)) (hraw z hz) level cell
    apply ht.trans
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith : qEnv+4 ≤ 2*(qEnv+6)))
        (by positivity)
    · exact g.mass_nonnegative tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut weight hw0 level cell z
  · intro shift eta heta
    have hparams := source_vertex_plane_parameters L Dphase (SourceParameters.blockCount L)
      hL hD hKb shift eta heta
    change 0 ≤ a ∧ a ≤ 1 ∧ 1 ≤ alpha ∧ alpha ≤ 3 ∧ (alpha-1)/p ≤ 1/12 ∧
      p*mu = alpha-1 ∧ (∀ j, ‖phaseTubePoint (Pi.single shift mu) eta j‖ ≤ 2*L^2) ∧
      (∀ j, j ≠ shift → (phaseTubePoint (Pi.single shift mu) eta j).re = 0) ∧
      (phaseTubePoint (Pi.single shift mu) eta shift).re = mu at hparams
    obtain ⟨_,_,_,_,_,_,hphase,_,_⟩ := hparams
    refine ⟨?_,?_,?_⟩
    · intro z hz level cell
      exact hnode τ tops T N κ Label Item P packets assigned oldSlope R cone w F
        hw hcone hF hwide hfrequency alt hAlt b v f g cut Kw (Dweight:ℝ) hKw
        hassigned hshort hcondition hzero (SourceParameters.blockCount L) hKb hKbL
        (g.sourceBoundaryGap L) (phase shift eta) M hM hMmax a (2*L^2) A maskExponent
        ha ha1 (by positivity) le_rfl hA hAq
        (fun _ _ j _ => hre shift eta j) (fun _ _ j _ => hphase _)
        z (hweight z (hsub hz)) (htotal z (hsub hz)) (hraw z hz) level cell
    · intro z hz
      have hmassBad : (∑ t ∈ tops.filter (fun t => z ∈ bad t), weight t z) ≤ Real.exp (-L) := by
        rw [←sourceBadPathMass_eq_filter]
        exact hz.2
      exact (mul_le_mul_of_nonneg_left hmassBad (by dsimp only [cost]; positivity)).trans
        (hbudget alpha halpha halpha3)
    · exact hvertex τ κ tops T N Label Item P packets assigned oldSlope cone w hw hcone hwide
        hfrequency hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 maskExponent shortVariation
        hmask hwideResidual hwideParent hconeK hlocal hwidth horder hscale hX hZ hassigned hshort hcondition
        g hbranch htopWidth hzero hroot hKb hKbL Dphase Nmass A hD hNmass hlogN hA hAq shift eta heta
        good bad hgood hbad (fun z hz => hweight z (hsub hz)) (fun z hz => htotal z (hsub hz))
        (fun z hz => hmass z (hsub hz)) (fun z hz => hconc z (hsub hz))
        (fun j hj z hz => hcount shift j hj z (hsub hz))
        (fun t ht z hz => hsquareEvent t ht z ⟨hsub hz.1,hz.2⟩)
        (fun t ht z hz => hrefEvent shift t ht z ⟨hsub hz.1,hz.2⟩)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
