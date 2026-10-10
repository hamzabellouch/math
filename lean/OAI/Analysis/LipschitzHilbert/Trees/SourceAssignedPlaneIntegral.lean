import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedPlanePath
import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedLabelCountAt
import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedModelInterval
import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedSupportedPath
import OAI.Analysis.LipschitzHilbert.Trees.SourcePlaneWeightCost

namespace OAI

/-! The original marked-packet estimate passes through the inhabited
assigned model to an actual plane integral. All model geometry,
coefficients, masks and prediction products are identified explicitly. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable

theorem eventually_assigned_model_plane_integral
    (pProfile qEnv Cmass Cweight F c0 A_M : ℝ) (Dweight Kcount Hcount : ℕ)
    (hpProfile : 0 ≤ pProfile) (hqEnv : 0 ≤ qEnv) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hAM : 0 ≤ A_M) (hDweight : 2 < (Dweight:ℝ)) :
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
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (maskExponent : ℝ), 0 ≤ maskExponent →
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
    let H := sourceLineScale g L w (ShiftedBlocks.endpoint shift count)
    let line := fun k : ℤ => sourceReverseLineGrid g L (H*k) hw shift count
    let active := g.sourceActivePathValue tops slope precision cut weight
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
      (fun u => stop u.1) original phaseAll a α (Real.sqrt L) (L^A_M) shift top count
    let n := fun y x => g.shiftedPathMass tops slope precision cut weight shift top (x,y+slope top*x)
    let beta := fun y j x => g.sourceShiftedPathPrediction tops slope precision cut weight
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L) packets assigned
      (fun u => stop u.1) original phaseAll a (Real.sqrt L)
      (PhaseCombinatorics.phaseMu Dphase (Real.sqrt L)) shift top (x,y+slope top*x) j
    let marked := fun k y j i => sourceMarkedCell
      ((line k).cell (ShiftedBlocks.reverseLevel shift count (ShiftedBlocks.reverseIndex count j)) i)
      (fun x => n y x j) (fun x => n y x j-n y x (j+1)) (L^A_M)
    let cost := 1+(L^(qEnv+6))^(Real.sqrt L)*(L^A_M+1)^(α-1)
    Measurable active → (∀ z ∈ good, 0 ≤ active z) →
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
    (∀ (k : ℤ) (y x : ℝ), x ∈ (line k).root → (x,y+slope top*x) ∈ good →
      active (x,y+slope top*x) ≤ (Real.exp 3*cost)*
        ∏ j ∈ Finset.range count, reverseMarkedValue (line k) (ShiftedBlocks.reverseLevel shift count)
          count (marked k y) (beta y) j x) →
    Integrable (good.indicator (fun z => weight top z*active z)) (volume.prod volume) ∧
      (∫ z, good.indicator (fun z => weight top z*active z) z ∂volume.prod volume) ≤
        Real.exp (4+2*(Dweight:ℝ))*cost*(∫ z, weight top z ∂volume.prod volume) := by
  filter_upwards [AngularGrid.eventually_source_supported_selector_plane_integral
    pProfile qEnv Cmass Cweight F c0 A_M Dweight ((2*Kcount+1)*Hcount) hpProfile hqEnv hCmass
    hCweight hF hc0 hAM hDweight,eventually_ge_atTop (1:ℝ)] with L hplane hL
  intro τ κ _ tops T N Label Item _ P packets assigned oldSlope cone w hw hcone hwide
    hfrequency hfrequencyLo hP alt hAlt b hb hb1 v hv f hf hf1 maskExponent hmask
    Kw R Q orig alts halt hconeK hlocal hwidth horder hscale hX hZ hassigned hshort hcondition
    g hbranch htopWidth hzero hroot hKb hKbL shift phase a Z A Dphase Nmass α
    ha ha1 hZ0 hZL hphase hother hreal hA hAq hD hNmass hlogN top htop good hgood
    cut slope precision weight stop original phaseAll count H line active n beta marked cost
    hactive hactive0 hweight htotal hmass hconc hcount hpath
  let model := P.assignedInhabitedReference packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hKw : 1 ≤ Kw := Real.one_le_rpow hL (by linarith)
  let modelAlt := fun t => (Q t).inhabitedAlternate (alts t)
  let modelAltBound := fun t => (Q t).inhabitedAlternate_bound (alts t) (halt t)
  let selector := fun t j (l : (model t).labels j) =>
    b j (orig t j ((Q t).inhabitedOriginalLabel j l))
  have hslots (t : τ) (_ht : t ∈ tops) (j : Fin N) :
      ((model t).labels j).card ≤ (2*Kcount+1)*Hcount := by
    apply P.assignedReference_inhabited_label_count_at packets assigned t oldSlope
      (T t).slope (R t) cone w F hw hcone hF hwide hfrequency
      j (w/P.length j) cone Hcount Kcount (div_pos hw (P.length_pos j)) hconeK (hlocal j)
    intro l u hu he
    have hc := (hcondition ⟨j,⟨l,u⟩⟩ hu).2
    simpa only [he,mul_div_assoc] using hc
  have hmodel (t : τ) (_ht : t ∈ tops) : (model t).constant ≤ L^pProfile := by
    rw [P.assignedInhabitedReference_constant packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency t]
    exact hP
  have hgeom (t : τ) (ht : t ∈ tops) :
      SourceSupportedLabeledTopGeometry (model t) (T t) Kw Dweight := by
    apply P.assignedInhabitedReference_supportedTopGeometry packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency t Kw Dweight (hwidth t ht) horder (hscale t ht)
    · intro u hu he
      simpa only [he] using hX u hu
    · intro u hu he
      simpa only [he] using hZ u hu
  let M := fun t => g.lastEligible cut (precision t) (div_pos hw (T t).length_pos)
  have hM t (ht : t ∈ tops) : g.eligible cut (precision t) (M t) :=
    g.eligible_lastEligible cut (precision t) (div_pos hw (T t).length_pos) (hroot t ht)
  have hMmax t (ht : t ∈ tops) j (hj : g.eligible cut (precision t) j) : j ≤ M t :=
    (g.eligible_iff_le_lastEligible cut (precision t) (div_pos hw (T t).length_pos) (hroot t ht) j).mp hj
  have hinterval (t : τ) (lower upper : ℕ) (hlu : lower ≤ upper) :
      ((model t).withProfile (modelAlt t) (modelAltBound t)).rawInterval
        ((model t).physicalMultiplierCoefficient (T t).slope (selector t) v f) 0 lower upper =
      ((Q t).withProfile (alts t) (halt t)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig t j l) u.val)
        0 lower upper := by
    funext x y
    exact P.assignedInhabitedRawInterval_original packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt b v f t 0 lower upper hlu x y
  have hcost : 0 ≤ Real.exp 3*cost := by dsimp [cost]; positivity
  have hp := hplane τ κ tops T N (fun j => τ×P.labels j) (P.AssignedTopItem packets assigned)
    model hslots hmodel modelAlt modelAltBound Kw hKw hgeom selector
    (fun t j l k => hb j _ k) (fun t j l k s => hb1 j _ k s) v hv f hf hf1
    g w hw hbranch htopWidth
    (fun t _ j l u => P.assignedInhabitedReference_short packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency hshort t j l u)
    (fun _ _ => hzero) hKb hKbL shift M hM hMmax phase a Z A maskExponent Dphase Nmass
    ha ha1 hZ0 hZL hphase hother hreal hA hAq hmask hD hNmass hlogN P.frequency
    hfrequencyLo hfrequency (fun _ _ => rfl) top htop (hroot top htop)
    good hgood active hactive hactive0 (Real.exp 3*cost) hcost hweight htotal hmass
    (by
      intro z hz t ht lower upper hlu hu yy hyy
      rw [hinterval t lower upper hlu]
      exact hconc z hz t ht lower upper hlu hu yy hyy)
    hcount
    (by
      intro k y x hx hz
      have hb := hpath k y x hx hz
      have heq := P.assignedInhabitedMarkedProduct_original packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency alt hAlt b v f L maskExponent g tops precision cut weight
        (SourceParameters.blockCount L) (g.sourceBoundaryGap L) hassigned hcondition
        (fun _ j => stop j) phaseAll a (Real.sqrt L)
        (PhaseCombinatorics.phaseMu Dphase (Real.sqrt L)) shift top count
        (line k) (ShiftedBlocks.reverseLevel shift count) (marked k y) y x
      exact hb.trans_eq (congrArg (fun r => (Real.exp 3*cost)*r) heq))
  refine ⟨hp.1,?_⟩
  exact source_plane_bound_by_weight (T top) Kw (Dweight:ℝ) cost _
    (zero_lt_one.trans_le hKw) hp.2

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
