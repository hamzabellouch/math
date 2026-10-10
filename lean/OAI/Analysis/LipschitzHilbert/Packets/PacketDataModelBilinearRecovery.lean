import OAI.Analysis.LipschitzHilbert.Packets.PacketDataHighDensityEnergyRecovery
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataIntrinsicDensityPairing
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataModelRestriction

namespace OAI

/-! The complete low/high density assembly for the actual finite
bilinear model in a direction chart. The high family is constructed
from the original collection; no energy or counting premise remains. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq

theorem source_model_bilinear_recovery
    (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cb F c0 cone Lip Cv aDensity p0 decay : ℝ)
    (D K H J₀ : ℕ)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta)
    (hcb : 0 < cb) (hcbQuarter : cb ≤ 1/4) (hCv : 0 ≤ Cv) (hCb : 0 ≤ Cb) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hcone : 1 ≤ cone) (hconeK : cone ≤ K) (hLip : 0 ≤ Lip)
    (haDensity : 0 ≤ aDensity) (hp0 : 0 ≤ p0)
    (hdecay : 0 ≤ decay) (hbudget : 4*(3*p0+4+decay)≤aDensity) (hD : 4 ≤ D)
    (hgap : cStar < cEta*cb) (hJ : 2*cone+1 ≤ (2:ℝ)^J₀) :
    ∃ CD CS CT LD LS LT : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧ 0<LD ∧ 0<LS ∧ 0<LT ∧ ∃ A L0 : ℝ, aDensity+3 < A ∧ 16 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (w tau : ℝ), 0 < w →
      P.scale = 4*(L^(A+2)*P.width) → P.ratioBound = 4*L^(A+2) →
      (2^P.order*P.profileBound)*3^(2*P.order) ≤ L^p0 →
      6+2*(8*D+1) ≤ P.order → packets.Nonempty →
    ∀ (d : OrdinaryModelConfig P packets),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
      d.w=w → d.tau=tau → d.unitModelCost CD CS CT≤L → d.unitModelCost LD LS LT≤L →
    ∀ (Eset Fset : Set (ℝ×ℝ)) (field : Plane → ℝ)
      (cell : ∀ j, P.labels j → ℤ) (grid : ℤ), cell=d.cell → grid=d.grid →
      MeasurableSet Eset → (volume.prod volume) Eset ≠ ∞ →
      (∀ q ∈ packets, 0+P.rowSlope q.1 q.2.1 ∈
        scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      (∀ q ∈ packets, scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) ⊆ Icc (-1) 1) →
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
      (_hMargin : ∀ q∈packets, ∀ k xi et,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        Set.Icc (-xi/et-d.margin*(d.w/P.length q.1)) (-xi/et+d.margin*(d.w/P.length q.1))⊆
          scaledAngularCell (d.w/P.topLength) d.grid q.1.val (d.cell q.1 q.2.1))
      (_hBin : ∀ q∈packets, ∀ k xi et,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
          |et-P.frequency k|≤d.Cv/P.width)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ), b=d.selector →
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 → |s-(0+P.rowSlope j l)| ≤ cone*(w/P.length j)) →
      (∀ j l k s t, ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(w/P.length j))) →
      (∀ j l k s, b j l k s ≠ 0 →
        cb*w/P.length j ≤ |s-(0+P.rowSlope j l)| ∧
          |s-(0+P.rowSlope j l)| ≤ Cb*w/P.length j) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => 0+P.rowSlope j l) (w/P.length j) H) →
      (∀ k, c0/w ≤ |P.frequency k|) → (∀ k, |P.frequency k| ≤ F/w) →
      (∀ j l u k xi eta,
        planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta) ≠ 0 →
          |xi+(0+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l u k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l u k) (xi,eta) ≠ 0 →
          |xi+(0+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
      (∀ z, z∉Eset → f z=0) →
    ∀ (g : AngularGrid), (g.branching:ℝ) = SourceParameters.step L →
      (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
      2 ≤ g.rootWidth →
    ∀ (test : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable test → (∀ z, ‖test z‖≤1) →
      (∀ z, z∉Fset → test z=0) →
      Integrable (fun z => inner ℂ
        (∑ q∈packets, P.crossPacketValue alt hAlt 0 b
          (fun z => field (planeCoordinates z)) f z q) (test z)) (volume.prod volume) ∧
      ‖∫ z, inner ℂ (∑ q∈packets, P.crossPacketValue alt hAlt 0 b
        (fun z => field (planeCoordinates z)) f z q) (test z) ∂volume.prod volume‖≤
          2*L^(-decay)*ratio*(volume.prod volume).real Fset := by
  obtain ⟨CD,CS,CT,hCD,hCS,hCT,A,L0,haA,hL0,hHigh⟩ := source_high_density_energy_recovery
    hVariation hLL cStar cEta CEta cb Cb F c0 cone Lip Cv aDensity p0 decay D K H J₀
    hcStar hcEta hCEta hcb hcbQuarter hCv hCb hF hc0 hcone hconeK hLip haDensity hp0
    hdecay hD hgap hJ
  obtain ⟨LD,LS,LT,hLD,hLS,hLT,hLow⟩ := exists_intrinsic_density_pairing hVariation
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hgap
  refine ⟨CD,CS,CT,LD,LS,LT,hCD,hCS,hCT,hLD,hLS,hLT,A,L0,haA,hL0,?_⟩
  intro L hL κ _ N Label Item _ P packets w tau hw hscale hratioBound hprofile horder hpackets
    d heq₁ heq₂ heq₃ heq₄ heq₅ hwEq htauEq hunitHigh hunitLow
    Eset Fset field cell grid hcellEq hgridEq hEset hEfinite hcell hcellrange
    l r hfield hstrip hEstrip hFstrip hFset hFfinite hFpositive
    ratio widthScale hratio hloglow hloghigh hratioEq hwidthLow hwidthHigh hwidthEq htimeLow htimeHigh
    alt hAlt hMargin hBin b hbEq hb hb1 hsupp hmotion hactive hlocal hfrequencyLo hfrequency
    hspectrum haltSpectrum f hf hf1 hfs g hbranch hzero hrootWidth test htest htest1 htests
  let v : ℝ×ℝ → ℝ := fun z => field (planeCoordinates z)
  have hv : Measurable v := (product_slope_lipschitz field hfield).continuous.measurable
  have hLtwo : 2≤L := by linarith only [hL0.trans hL]
  have hLone : 1≤L := (by norm_num : (1:ℝ)≤2).trans hLtwo
  have hLp : 0<L := zero_lt_one.trans_le hLone
  let eta := L^(-aDensity)
  have heta : 0<eta := Real.rpow_pos_of_pos hLp _
  let high := packets.filter (fun q => eta<P.ordinaryDensity 0 cell grid w tau Eset v q)
  let low := packets\high
  have hhigh : high⊆packets := Finset.filter_subset _ _
  have hlow : low⊆packets := Finset.sdiff_subset
  have hdhigh (q : P.PacketIndex) (hq : q∈high) :
      L^(-aDensity)<P.ordinaryDensity 0 cell grid w tau Eset v q := (Finset.mem_filter.mp hq).2
  have hdlow (q : P.PacketIndex) (hq : q∈low) :
      P.ordinaryDensity 0 d.cell d.grid d.w d.tau Eset v q≤eta := by
    have hq' := Finset.mem_sdiff.mp hq
    have hn : ¬eta<P.ordinaryDensity 0 cell grid w tau Eset v q := by
      intro hn
      exact hq'.2 (Finset.mem_filter.mpr ⟨hq'.1,hn⟩)
    simpa only [hcellEq,hgridEq,hwEq,htauEq] using le_of_not_gt hn
  have halt : ∀ j l a k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤d.cStar/P.length j ∧ d.cEta≤d.w*et ∧ d.w*et≤d.CEta := by
    intro j l a k xi et hn
    simpa only [zero_add,heq₁,heq₂,heq₃,hwEq] using haltSpectrum j l a k xi et hn
  have hlowPair := hLow N κ Label Item P packets d heq₁ heq₂ heq₃ heq₄ heq₅
    alt hAlt halt hMargin hBin L p0 hLtwo hp0 hunitLow hprofile low hlow
    f test hf htest hf1 htest1 Eset Fset hEset hFset hEfinite hFfinite hfs htests v hv eta heta hdlow
  rw [←hbEq] at hlowPair
  let V := fun (S : Finset P.PacketIndex) (z : ℝ×ℝ) =>
    ∑ q∈S, P.crossPacketValue alt hAlt 0 b v f z q
  have hhighInt : IntegrableOn (V high) Fset (volume.prod volume) :=
    (memLp_one_iff_integrable.mp (P.crossSum_memLp alt hAlt 0 b v f 1 high)).integrableOn
  have hhighBound : (∫ z in Fset, ‖V high z‖ ∂volume.prod volume)≤
      L^(-decay)*ratio*(volume.prod volume).real Fset := by
    by_cases hn : high.Nonempty
    · let dh := d.restrict high hhigh
      exact hHigh L hL κ N Label Item P high w tau hw hscale hratioBound hprofile horder hn
        dh heq₁ heq₂ heq₃ heq₄ heq₅ hwEq htauEq hunitHigh
        Eset Fset field cell grid hEset hEfinite hdhigh
        (fun q hq => hcell q (hhigh hq)) (fun q hq => hcellrange q (hhigh hq))
        l r hfield hstrip hEstrip hFstrip hFset hFfinite hFpositive
        ratio widthScale hratio hloglow hloghigh hratioEq hwidthLow hwidthHigh hwidthEq htimeLow htimeHigh
        alt hAlt (fun q hq => hMargin q (hhigh hq)) (fun q hq => hBin q (hhigh hq))
        b hbEq hb hb1 hsupp hmotion hactive hlocal hfrequencyLo hfrequency hspectrum haltSpectrum
        v hv f hf hf1 hfs g hbranch hzero hrootWidth
    · have hz : high=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [V,hz,Finset.sum_empty,norm_zero,integral_zero]
      positivity
  have hhighPair := supported_inner_integral_le (volume.prod volume) Fset hFset
    (V high) test hhighInt htest htest1 htests
  have hroot : Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real Eset)=
      ratio*(volume.prod volume).real Fset := by
    rw [hratioEq,Real.sqrt_mul (sq_nonneg ratio),Real.sqrt_sq hratio.le]
    calc
      _ = ratio*(Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real Fset)) := by ring
      _ = _ := by rw [Real.mul_self_sqrt measureReal_nonneg]
  have hpower : L^(3*p0+4)*eta^(1/4:ℝ)≤L^(-decay) := by
    dsimp only [eta]
    rw [←Real.rpow_mul hLp.le,←Real.rpow_add hLp]
    exact Real.rpow_le_rpow_of_exponent_le hLone (by linarith only [hbudget])
  have hlowBound : ‖∫ z, inner ℂ (V low z) (test z) ∂volume.prod volume‖≤
      L^(-decay)*ratio*(volume.prod volume).real Fset := by
    apply hlowPair.2.trans
    calc
      _ = (L^(3*p0+4)*eta^(1/4:ℝ))*
          (Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real Eset)) := by ring
      _ ≤ L^(-decay)*(Real.sqrt ((volume.prod volume).real Fset)*Real.sqrt ((volume.prod volume).real Eset)) :=
        mul_le_mul_of_nonneg_right hpower (by positivity)
      _ = _ := by rw [hroot]; ring
  have hsplit (z : ℝ×ℝ) : V packets z=V low z+V high z := by
    exact (Finset.sum_sdiff hhigh (f:=fun q => P.crossPacketValue alt hAlt 0 b v f z q)).symm
  have hpairSplit (z : ℝ×ℝ) : inner ℂ (V packets z) (test z)=
      inner ℂ (V low z) (test z)+inner ℂ (V high z) (test z) := by rw [hsplit,inner_add_left]
  have hInt : Integrable (fun z => inner ℂ (V packets z) (test z)) (volume.prod volume) :=
    (hlowPair.1.add hhighPair.1).congr (Filter.Eventually.of_forall (fun z => (hpairSplit z).symm))
  refine ⟨hInt,?_⟩
  calc
    _ = ‖(∫ z, inner ℂ (V low z) (test z) ∂volume.prod volume)+
        (∫ z, inner ℂ (V high z) (test z) ∂volume.prod volume)‖ := by
      rw [←integral_add hlowPair.1 hhighPair.1]
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall hpairSplit)
    _ ≤ ‖∫ z, inner ℂ (V low z) (test z) ∂volume.prod volume‖+
        ‖∫ z, inner ℂ (V high z) (test z) ∂volume.prod volume‖ := norm_add_le _ _
    _ ≤ (L^(-decay)*ratio*(volume.prod volume).real Fset)+
        (L^(-decay)*ratio*(volume.prod volume).real Fset) :=
      add_le_add hlowBound (hhighPair.2.trans hhighBound)
    _ = _ := by ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
