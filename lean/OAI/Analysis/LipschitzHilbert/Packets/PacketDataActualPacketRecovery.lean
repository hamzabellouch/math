import OAI.Analysis.LipschitzHilbert.Packets.PacketDataActualReferenceCentral
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataPacketRecovery
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedBoundaryGain
import OAI.Analysis.LipschitzHilbert.Trees.SourceTotalWeightBudget

namespace OAI

/-! The original packet sum is recovered from a reference exception for every
common grid translation. Central and averaged boundary budgets follow from
the energy, fixed-set, mask, and geometric/concentration hypotheses on the
popular collection. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_actual_packet_recovery (hVariation : LepingleInput)
    (qEnergy sArea pProfile qEnv Cmass Cweight F c0 A_M d m decay maskExponent cStar cEta CEta cb Cb Lip cone : ℝ) (Dweight Kcount Hcount : ℕ)
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
    ∀ (_hwideResidual : (cone+(SourceParameters.branching L)^2)*w ≤ P.width)
      (_hwideParent : (cone+(SourceParameters.branching L)^3)*w ≤ P.width),
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
    ∀ (_hKb : 0 < SourceParameters.blockCount L), (SourceParameters.blockCount L:ℝ) ≤ L^2 →
    ∀ (Dphase Nmass A : ℝ), 2 ≤ Dphase → Dphase ≤ L^d → 0 < Nmass → Real.log Nmass ≤ 2*L →
      0 ≤ A → A ≤ L^qEnv →
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let original := P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent
    ∀ (Z0 : Set (ℝ×ℝ)), MeasurableSet Z0 →
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
    (∀ z ∈ Z0, ∀ rho : ℝ, 0 < rho → ∀ I : Finset τ, I ⊆ tops →
      (∀ t ∈ I, (T t).radius z ≤ L^(maskExponent+2)) →
      (∀ t ∈ I, w/(T t).length ≤ rho/(SourceParameters.branching L)^2) →
      (∀ t ∈ I, ∀ u ∈ I, |(T t).slope-(T u).slope| ≤ SourceParameters.branching L*rho) →
      (∀ t ∈ I, ∀ u ∈ I, t ≠ u → rho ≤ |(T t).slope-(T u).slope|) →
      (I.card:ℝ) ≤ Dphase/100) →
    ∀ (start Fmass : ℝ), 0 < Fmass → L/2 ≤ Real.log Nmass →
      (volume.prod volume) Z0 ≠ ∞ → (volume.prod volume).real Z0 ≤ Fmass →
      (∀ t ∈ tops, start ≤ (T t).slope ∧ (T t).slope ≤ start+g.rootWidth) →
      (∑ t ∈ tops, ∫ z, weight t z ∂volume.prod volume) ≤ L^m*Nmass^2*Fmass →
    ∀ (Fset Eset : Set (ℝ×ℝ)), MeasurableSet Fset →
      (volume.prod volume) Fset ≠ ∞ → Fmass = (volume.prod volume).real Fset →
      Z0 ⊆ Fset → (volume.prod volume).real Eset = Nmass^2*Fmass →
    let originalSum := fun z => ∑ u ∈ packets,
      P.crossPacketValue alt hAlt oldSlope b v f z u
    let maskedSum := fun z => ∑ u ∈ packets, original z u
    (∫ z, ‖originalSum z‖^2 ∂volume.prod volume) ≤
      (L^qEnergy)^2*(volume.prod volume).real Eset →
    (volume.prod volume).real (Fset\Z0) ≤ (L^(-qEnergy-(decay+1)))^2*Fmass →
    (∑ t ∈ tops, (T t).length*(T t).width) ≤ L^sArea*(volume.prod volume).real Eset →
    (∫ z in Z0, ‖originalSum z-maskedSum z‖ ∂volume.prod volume) ≤
      L^(-(decay+1))*Nmass*Fmass →
    (∫ z in Fset, ‖originalSum z‖ ∂volume.prod volume) ≤ L^(-decay)*Nmass*Fmass := by
  filter_upwards [eventually_actual_reference_central_gain hVariation
      pProfile qEnv Cmass Cweight F c0 A_M d m (decay+1) maskExponent cStar cEta CEta cb Cb Lip cone
      Dweight Kcount Hcount hpProfile hqEnv hCmass hCweight hF hc0 hAM hchoice hDweight hd hm
      hqm hCmassM (by linarith) hMask hcStar hcEta hCEta hcb hCb hLip hgap hcone hconeK,
    eventually_physical_packet_recovery qEnergy sArea decay,
    eventually_assigned_boundary_gain (Dweight:ℝ) qEnv m (decay+1) hDweight,
    eventually_ge_atTop (256:ℝ)] with L hcentralGain hrecover hboundaryGain hL
  intro τ κ _ N Label Item _ P tops T packets assigned oldSlope w hw hwide hfrequency
    hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 hmotion hactive hspectrum haltSpectrum
    Kw R Q orig alts halt hwideResidual hwideParent hlocal hwidth horder hscale hX hZ
    hassigned hshort hcondition g hbranch htopWidth hzero hroot hKb hKbL Dphase Nmass A
    hD hDL hNmass hlogN hA hAq weight original
    Z0 hZ0 hweight htotal hmass hconc hcount start Fmass hFmass hloglo
    hZ0finite hmeasure hslope hweightTotal Fset Eset hFset hFfinite hFmassEq hZ0F hratio
    originalSum maskedSum henergy hfixed harea hmask
  let a := PhaseCombinatorics.phaseMu Dphase (Real.sqrt L)/(SourceParameters.blockCount L:ℝ)
  let cut := g.rootWidth/(SourceParameters.branching L)^2
  let stop := fun j : Fin N => g.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
  let wide : ∀ i : Option (Fin (SourceParameters.blockCount L)),
      (cone+(SourceParameters.branching L)^(if i.isNone then 3 else 2))*w ≤ P.width := by
    intro i
    cases i with
    | none => exact hwideParent
    | some i => exact hwideResidual
  have hL1 : 1 ≤ L := by linarith
  have hKw : 0 < Kw := Real.rpow_pos_of_pos (by linarith) _
  have hmu := source_phaseMu_small (by linarith : 1 ≤ Dphase) hL
  have ha : 0 ≤ a := div_nonneg hmu.1.le (Nat.cast_nonneg _)
  have ha1 : a ≤ 1 := by
    apply (div_le_iff₀ (by exact_mod_cast hKb : (0:ℝ) < SourceParameters.blockCount L)).mpr
    have hK1 : (1:ℝ) ≤ SourceParameters.blockCount L := by exact_mod_cast hKb
    simpa only [one_mul] using (hmu.2.trans (by linarith : (1/12:ℝ) ≤ SourceParameters.blockCount L))
  let bad := fun origin => P.actualReferenceBad alt hAlt L oldSlope cone w F hw hcone hF wide
    hfrequency b v f (g.withOrigin origin) tops T packets assigned hKb maskExponent pProfile
  let good := fun origin => sourceGoodPathSet Z0 tops weight (bad origin) L
  let central := fun origin z => ∑ s ∈ packets,
    (((g.withOrigin origin).sourceBoundaryCoefficient tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cut weight (SourceParameters.blockCount L)
      (g.sourceBoundaryGap L) (stop s.1) (assigned s) a z : ℝ):ℂ) • original z s
  have hc (origin : ℝ) :
      MeasurableSet (good origin) ∧ good origin ⊆ Z0 ∧
      (volume.prod volume) (Z0\good origin) ≤ ENNReal.ofReal
        ((∑ t ∈ tops, (T t).length*(T t).width)*Real.exp (-9*L)) ∧
      (∫ z in good origin, ‖central origin z‖ ∂volume.prod volume) ≤
        L^(-(decay+1))*Nmass*Fmass := by
    have h := hcentralGain τ κ N Label Item P tops T packets assigned oldSlope w hw hwide
      hfrequency hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 hmotion hactive
      hspectrum haltSpectrum hwideResidual hwideParent hlocal hwidth horder hscale hX hZ
      hassigned hshort hcondition (g.withOrigin origin) hbranch htopWidth hzero hroot hKb hKbL
      Dphase Nmass A hD hDL hNmass hlogN hA hAq Z0 hZ0 hweight htotal hmass hconc
      (by
        intro shift j hj z hz I hI hrad hprec hcluster hsep
        exact hcount z hz _ (g.sourceGap_pos L _) I hI hrad hprec hcluster hsep)
      start Fmass hFmass hloglo hZ0finite hmeasure hslope hweightTotal
    exact ⟨h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.2⟩
  have hmassInt : (∫ z in Z0, ∑ t ∈ tops, weight t z ∂volume.prod volume) ≤
      L^m*Nmass*Fmass := by
    apply (source_testing_weight_integral tops T Kw (Dweight:ℝ) L Cmass Nmass Fmass
      hKw hDweight (by linarith) hNmass.le Z0 hZ0 hZ0finite hmeasure hmass).2.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hL1 hCmassM) hNmass.le) hFmass.le
  have hbnd := hboundaryGain τ κ N Label Item P packets assigned tops T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f g maskExponent cut Kw hbranch hKw
    (SourceParameters.blockCount L) hKb hassigned hshort hcondition hzero hroot
    a Nmass Fmass ha ha1 hNmass.le hFmass.le Z0 hZ0 htotal hmassInt
    (by
      intro z hz t ht lower upper hlu hu
      have h := hconc z hz t ht lower upper hlu hu (z.2-(T t).slope*z.1)
        (by simpa only [sub_self,abs_zero] using (T t).width_pos.le)
      have hn : 0 ≤ (T t).width * ‖covariantSignal P.frequency
          (fun k yy => ((Q t).withProfile (alts t) (halt t)).rawInterval
            (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig t j l) u.val)
            0 lower upper z.1 yy k) (z.2-(T t).slope*z.1)‖ :=
        mul_nonneg (T t).width_pos.le (norm_nonneg _)
      exact (le_add_of_nonneg_right hn).trans (h.trans
        (mul_le_mul_of_nonneg_right hAq (by positivity))))
  have hNexp : Nmass ≤ Real.exp (2*L) := (Real.log_le_iff_le_exp hNmass).mp hlogN
  have hmove (origin : ℝ) : (volume.prod volume).real (Z0\good origin) ≤
      L^sArea*(volume.prod volume).real Eset*Real.exp (-9*L) := by
    have hn : 0 ≤ (∑ t ∈ tops, (T t).length*(T t).width)*Real.exp (-9*L) := by
      apply mul_nonneg _ (Real.exp_pos _).le
      exact Finset.sum_nonneg fun t _ => mul_nonneg (T t).length_pos.le (T t).width_pos.le
    have h := ENNReal.toReal_mono (by simp) (hc origin).2.2.1
    rw [ENNReal.toReal_ofReal hn] at h
    exact h.trans (mul_le_mul_of_nonneg_right harea (Real.exp_pos _).le)
  have hr := hrecover τ κ N Label Item P alt hAlt oldSlope b v f packets assigned tops T g
    w cut Kw (Dweight:ℝ) maskExponent a hw hKw ha hassigned hshort hzero
    (SourceParameters.blockCount L) hKb (g.sourceBoundaryGap L)
    Fset Eset Z0 good hFset hZ0 (fun origin => (hc origin).1) hFfinite hZ0F
    (fun origin => (hc origin).2.1) Nmass hNmass.le
    (by simpa only [←hFmassEq] using hratio) hNexp henergy
    (by simpa only [←hFmassEq] using hfixed) hmove
    (by simpa only [←hFmassEq] using hmask)
    (by intro origin; simpa only [←hFmassEq] using (hc origin).2.2.2)
    hbnd.2.1 (by simpa only [←hFmassEq] using hbnd.2.2)
  simpa only [←hFmassEq] using hr

end LipschitzHilbert.PacketLatticeData

end

end OAI
