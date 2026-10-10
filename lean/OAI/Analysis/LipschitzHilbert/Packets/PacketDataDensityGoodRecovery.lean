import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDensitySelectorGoodSet
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDensityJetNormalization
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataActualPacketRecovery
import OAI.Analysis.LipschitzHilbert.Trees.SourceParentWidth

namespace OAI

/-! The common concentration set gives popular recovery. The deleted-area
and mask losses, global weight budget and numerical parameters follow from
the common-set estimates and the density forest. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem source_density_recovery_of_good_set
    (hVariation : LepingleInput)
    (cStar cEta CEta cb Cb F c0 cone Lip aDensity p0 qEnergy decay : ℝ)
    (D K H : ℕ)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta)
    (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hcone : 0 ≤ cone) (hconeK : cone ≤ K) (hLip : 0 ≤ Lip)
    (haDensity : 0 ≤ aDensity) (hp0 : 0 ≤ p0) (hqEnergy : 0 ≤ qEnergy)
    (hdecay : 0 ≤ decay) (hD : 4 ≤ D)
    (hgap : cStar < cEta*cb)
    (A Cn Ct : ℝ) (haA : aDensity+3 < A) (hA : 2 < A) (hCn : 0 < Cn) (hCt : 0 < Ct) :

    let loss := 2*(qEnergy+decay+1)
    ∀ᶠ L : ℝ in atTop,
    ∀ (κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (oldSlope w tau : ℝ)
      (hw : 0 < w) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      P.scale = 4*(L^(A+2)*P.width) → P.ratioBound = 4*L^(A+2) →
      (2^P.order*P.profileBound)*3^(2*P.order) ≤ L^p0 →
      6+2*(8*D+1) ≤ P.order →
    ∀ (Eset Fset : Set (ℝ×ℝ)) (field : Plane → ℝ)
      (forest : PacketDensityForest P packets oldSlope L aDensity cone w tau Eset
        (fun z => field (planeCoordinates z))),
      let T := forest.top
      let assigned := forest.assigned
      (∀ i, |(T i).slope| ≤ 1) →
    ∀ (l r : ℝ), LipschitzWith 1 field → 600*(r-l) ≤ 1 →
      (∀ z ∈ Eset, z.1 ∈ Icc l r) → (∀ z ∈ Fset, z.1 ∈ Icc l r) →
      MeasurableSet Fset → (volume.prod volume) Fset ≠ ∞ →
      0 < (volume.prod volume).real Fset →
    ∀ (ratio widthScale : ℝ), 0 < ratio → L/2 ≤ Real.log ratio → Real.log ratio ≤ 2*L →
      (volume.prod volume).real Eset = ratio^2*(volume.prod volume).real Fset →
      Real.exp (L^(9/10:ℝ)) ≤ widthScale → widthScale ≤ 2*Real.exp (L^(9/10:ℝ)) →
      P.width = widthScale*w → 0 ≤ tau → tau ≤ Real.exp (-(L^(97/100:ℝ))) →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 → |s-(oldSlope+P.rowSlope j l)| ≤ cone*(w/P.length j)) →
      (∀ j l k s t, ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(w/P.length j))) →
      (∀ j l k s, b j l k s ≠ 0 →
        cb*w/P.length j ≤ |s-(oldSlope+P.rowSlope j l)| ∧
          |s-(oldSlope+P.rowSlope j l)| ≤ Cb*w/P.length j) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) H) →
      (∀ k, c0/w ≤ |P.frequency k|) →
      (∀ j l u k xi eta,
        planarAngularFourier (P.physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
          |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l u k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
          |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (g : AngularGrid) (start : ℝ), (g.branching:ℝ) = SourceParameters.step L →
      (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
      (∀ i, start ≤ (T i).slope ∧ (T i).slope ≤ start+g.rootWidth) →
      (∫ z, ‖∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q‖^2
        ∂volume.prod volume) ≤ (L^qEnergy)^2*(volume.prod volume).real Eset →
      let R := fun i => (T i).length
      let Q := fun top => (P.assignedTopFamily packets assigned top).referenceFamily
        oldSlope (T top).slope (R top) cone w F hw hcone hF hwide hfrequency
      let orig := fun top j (l : (Q top).labels j) =>
        ((P.assignedTopFamily packets assigned top).referenceOriginalLabel
          oldSlope (T top).slope (R top) cone w j l).val.2
      let a := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        alt j (orig top j l) u.val k
      let ha := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        hAlt j (orig top j l) u.val k
      ∀ G : Set (ℝ×ℝ), (MeasurableSet G ∧ G ⊆ Fset ∧
        (volume.prod volume) (Fset\G) ≤ ENNReal.ofReal (L^(-loss)*(volume.prod volume).real Fset) ∧
        (∀ z ∈ G, ∀ i, (T i).weight (L^(A+2)) (D:ℝ) z ≤ (2:ℝ)^D) ∧
        (∀ z ∈ G, Real.log (max 1 (∑ i, (T i).weight (L^(A+2)) (D:ℝ) z)) ≤ 3*L) ∧
        (∀ z ∈ G, (∑ i, (T i).weight (L^(A+2)) (D:ℝ) z) ≤ ratio*L^Cn) ∧
        (∀ top lower upper, lower ≤ upper → upper ≤ N → ∀ z ∈ G, ∀ yy,
          |yy-(z.2-(T top).slope*z.1)| ≤ (T top).width →
          let V := ((Q top).withProfile (a top) (ha top)).rawInterval
            (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig top j l) u.val)
            0 lower upper
          ‖V z.1 yy‖+(T top).width*‖covariantSignal P.frequency
            (fun k y => V z.1 y k) yy‖ ≤ L^(2*(p0+2*(aDensity+3)+1)+8)*((T top).weight (L^(A+2)) (D:ℝ) z)^8) ∧
        let original := fun z => ∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q
        let masked := fun z => ∑ q ∈ packets, P.physicalMaskedValue alt hAlt oldSlope b v f
          (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z q
        IntegrableOn (fun z => ‖original z-masked z‖) G (volume.prod volume) ∧
        (∫ z in G, ‖original z-masked z‖ ∂volume.prod volume) ≤
          L^(-loss)*ratio*(volume.prod volume).real Fset ∧
        ∀ z ∈ G, ∀ rho : ℝ, 0 < rho → ∀ I : Finset forest.keepers,
          (∀ i ∈ I, (T i).radius z ≤ L^(A+2)) →
          (∀ i ∈ I, w/(T i).length ≤ rho/(SourceParameters.branching L)^2) →
          (∀ i ∈ I, ∀ j ∈ I, |(T i).slope-(T j).slope| ≤ SourceParameters.branching L*rho) →
          (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope-(T j).slope|) →
          (I.card:ℝ) ≤ L^Ct/100) →
      (∫ z in Fset, ‖∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q‖
        ∂volume.prod volume) ≤ L^(-decay)*ratio*(volume.prod volume).real Fset := by
  intro loss
  let pProfile := p0+2*(A+2)+2
  let qEnv := 2*(p0+2*(aDensity+3)+1)+8
  let m := max (max (2*(qEnv+6)+2) Cn) (aDensity+2*(A+2)+2)
  let AM := 4*(max (3*pProfile+13) (2*pProfile+17)+3/2)
  have hpProfile : 0 ≤ pProfile := by dsimp [pProfile]; linarith only [hp0,hA]
  have hqEnv : 0 ≤ qEnv := by dsimp [qEnv]; linarith only [hp0,haDensity]
  have hAM : 0 < AM := by
    have h := le_max_left (3*pProfile+13) (2*pProfile+17)
    dsimp [AM]
    linarith only [h,hpProfile]
  have hm : 0 ≤ m := le_trans (by linarith only [hqEnv] : 0 ≤ 2*(qEnv+6)+2)
    ((le_max_left _ _).trans (le_max_left _ _))
  have hqm : 2*(qEnv+6)+2 ≤ m := (le_max_left _ _).trans (le_max_left _ _)
  have hCnm : Cn ≤ m := (le_max_right _ _).trans (le_max_left _ _)
  have hDreal : 2 < (D:ℝ) := by exact_mod_cast (by omega : 2 < D)
  have hweight : (1:ℝ) ≤ 2^D := one_le_pow₀ (by norm_num)
  have hrec := eventually_actual_packet_recovery hVariation
    qEnergy (aDensity+1) pProfile qEnv Cn ((2:ℝ)^D) F c0 AM (Ct+1) m decay A
    cStar cEta CEta cb Cb Lip cone D K H
    hpProfile hqEnv hCn.le hweight hF hc0 hAM (le_refl _)
    hDreal (by linarith only [hCt]) hm hqm hCnm hdecay (by linarith only [hA])
    hcStar hcEta hCEta hcb hCb hLip hgap hcone hconeK
  have hglobal := eventually_source_global_weight_integral (D:ℝ) (A+2) (aDensity+1) hDreal
  filter_upwards [hrec,hglobal,SourceParameters.eventually_parent_reference_width cone,
    eventually_ge_atTop (max 16 (F*cone+2))] with L hrecover hglobal hparent hlarge
  intro κ _ N Label Item _ P packets oldSlope w tau hw hwide hfrequency hscale hratioBound hprofile horder
    Eset Fset field forest T assigned hslopes l r hfield hstrip hEstrip hFstrip hFset hFfinite hFpositive
    ratio widthScale hratio hloglow hloghigh hratioEq hwidthLow hwidthHigh hwidthEq htimeLow htimeHigh
    alt hAlt b hb hb1 hsupp hmotion hactive hlocal hfrequencyLo hspectrum haltSpectrum
    v hv f hf hf1 g start hbranch hzero hslope henergy R Q orig a ha G hGbounds
  rcases hGbounds with ⟨hG,hGF,hGarea,hweightG,hlogG,hcountG,hconcG,hintG,hmaskG,hsepG⟩
  have hL16 : 16 ≤ L := (le_max_left _ _).trans hlarge
  have hfactor : F*cone+2 ≤ L := (le_max_right _ _).trans hlarge
  have hL1 : 1 ≤ L := by linarith only [hL16]
  have hLp : 0 < L := by linarith only [hL16]
  have hwidePair := hparent widthScale w P.width hwidthLow hw hwidthEq
  have hGfinite : (volume.prod volume) G ≠ ∞ := measure_ne_top_of_subset hGF hFfinite
  have hGmeasure : (volume.prod volume).real G ≤ (volume.prod volume).real Fset :=
    measureReal_mono hGF hFfinite
  have hGfixed : (volume.prod volume).real (Fset\G) ≤
      (L^(-qEnergy-(decay+1)))^2*(volume.prod volume).real Fset := by
    have ht := ENNReal.toReal_mono (by simp) hGarea
    rw [ENNReal.toReal_ofReal (by positivity)] at ht
    have heq : L^(-loss) = (L^(-qEnergy-(decay+1)))^2 := by
      rw [← Real.rpow_two,← Real.rpow_mul hLp.le]
      congr 1
      dsimp [loss]
      ring
    exact heq ▸ ht
  have hmask : (∫ z in G, ‖(∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q)-
      ∑ q ∈ packets, P.physicalMaskedValue alt hAlt oldSlope b v f
        (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z q‖ ∂volume.prod volume) ≤
      L^(-(decay+1))*ratio*(volume.prod volume).real Fset :=
    hmaskG.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hL1 (by dsimp [loss]; linarith only [hqEnergy,hdecay])) hratio.le)
      measureReal_nonneg)
  have hgeom := forest.mask_geometry hL1 (by linarith only [haA] : aDensity+3 ≤ A+2)
  have hglobalBudget : (∑ i : forest.keepers, ∫ z, (T i).weight (L^(A+2)) (D:ℝ) z
      ∂volume.prod volume) ≤ L^m*ratio^2*(volume.prod volume).real Fset := by
    have h := hglobal forest.keepers Finset.univ T ratio ((volume.prod volume).real Fset)
      hratio.le measureReal_nonneg
        (forest.area_budget (by linarith only [hL16]) ratio _ measureReal_nonneg hratioEq.le)
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hL1
        (by dsimp [m]; linarith [le_max_right (max (2*(qEnv+6)+2) Cn) (aDensity+2*(A+2)+2)]))
        (sq_nonneg ratio)) measureReal_nonneg)
  have hcore1 := hrecover forest.keepers κ N Label Item P Finset.univ T packets assigned oldSlope w hw hwide
    hfrequency hfrequencyLo
    (P.mask_referenceEnvelopeConstant_of_ratio hL16 (by linarith only [hA]) hF hcone hfactor hratioBound hprofile)
    alt hAlt b hb hb1 hsupp v hv f hf hf1 hmotion hactive hspectrum haltSpectrum
  have hcore2 := hcore1 hwidePair.2 hwidePair.1 hlocal
    (by
      intro i _
      rw [forest.width]
      exact le_mul_of_one_le_left P.width_pos.le (Real.one_le_rpow hL1 (by linarith only [hA])))
    (by omega)
    (by
      intro i _
      change P.scale = 4*(L^(A+2)*(forest.top i).width)
      rw [forest.width]
      exact hscale)
    hgeom.1 hgeom.2 (fun _ _ => Finset.mem_univ _) (fun q hq => (forest.reference q hq).1)
    forest.reference g hbranch
    (by
      intro i _
      rw [forest.width]
      have h := hwidePair.2
      nlinarith only [h, mul_nonneg hcone hw.le])
    hzero
    (by
      intro i _
      have h := hzero i.val.val.1
      simp only [AngularGrid.eligible,pow_zero,mul_one]
      apply (div_le_div_of_nonneg_left hw.le (P.length_pos _) (forest.seed_short i)).trans
      simpa only [AngularGrid.eligible,pow_zero,mul_one] using h)
  have hcore3 := hcore2 (SourceParameters.blockCount_pos (by linarith only [hL16])) (source_blockCount_le_square (by linarith only [hL16]))
    (2*L^Ct) ratio (L^qEnv)
    (by nlinarith only [Real.one_le_rpow hL1 hCt.le])
    (by
      calc
        _ ≤ L*L^Ct := mul_le_mul_of_nonneg_right (by linarith only [hL16] : (2:ℝ) ≤ L) (Real.rpow_nonneg hLp.le _)
        _ = L^(Ct+1) := by rw [Real.rpow_add hLp,Real.rpow_one]; ring)
    hratio (hloghigh.trans (by linarith only [hL16])) (Real.rpow_nonneg hLp.le _) (le_refl _)
  have hcore4 := hcore3 G hG
    (by intro z hz i _; exact hweightG z hz i)
    hlogG
    (by intro z hz; simpa only [mul_comm] using hcountG z hz)
    (by intro z hz i _ lower upper hlu hup yy hyy; exact hconcG i lower upper hlu hup z hz yy hyy)
    (by
      intro z hz rho hrho I _ hrad hprec hcluster hsep
      exact (hsepG z hz rho hrho I hrad hprec hcluster hsep).trans
        (by have hp := Real.rpow_nonneg hLp.le Ct; linarith only [hp]))
  exact hcore4 start ((volume.prod volume).real Fset) hFpositive hloglow hGfinite hGmeasure
    (fun i _ => hslope i) hglobalBudget
    Fset Eset hFset hFfinite rfl hGF hratioEq henergy hGfixed
    (by
      rw [hratioEq]
      simpa only [SlopeBox.area,mul_assoc] using
        (forest.area_budget (by linarith only [hL16]) ratio _ measureReal_nonneg hratioEq.le)) hmask

end LipschitzHilbert.PacketLatticeData

end

end OAI
