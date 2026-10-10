import OAI.Analysis.LipschitzHilbert.Packets.PacketDataHighDensityPopularRecovery
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataIntrinsicCrossEnergy

namespace OAI

/-! Popular recovery for the actual high-density sum. The energy bound
follows from ordinary model estimates. The hypotheses concern explicit
packet geometry and a bounded supported input. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem source_high_density_energy_recovery
    (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cb F c0 cone Lip Cv aDensity p0 decay : ℝ)
    (D K H J₀ : ℕ)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta)
    (hcb : 0 < cb) (hcbQuarter : cb ≤ 1/4) (hCv : 0 ≤ Cv) (hCb : 0 ≤ Cb) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hcone : 1 ≤ cone) (hconeK : cone ≤ K) (hLip : 0 ≤ Lip)
    (haDensity : 0 ≤ aDensity) (hp0 : 0 ≤ p0)
    (hdecay : 0 ≤ decay) (hD : 4 ≤ D)
    (hgap : cStar < cEta*cb) (hJ : 2*cone+1 ≤ (2:ℝ)^J₀) :
    ∃ CD CS CT : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧ ∃ A L0 : ℝ, aDensity+3 < A ∧ 16 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (w tau : ℝ), 0 < w →
      P.scale = 4*(L^(A+2)*P.width) → P.ratioBound = 4*L^(A+2) →
      (2^P.order*P.profileBound)*3^(2*P.order) ≤ L^p0 →
      6+2*(8*D+1) ≤ P.order → packets.Nonempty →
    ∀ (d : OrdinaryModelConfig P packets),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
      d.w=w → d.tau=tau → d.unitModelCost CD CS CT≤L →
    ∀ (Eset Fset : Set (ℝ×ℝ)) (field : Plane → ℝ)
      (cell : ∀ j, P.labels j → ℤ) (grid : ℤ),
      MeasurableSet Eset → (volume.prod volume) Eset ≠ ∞ →
      (∀ q ∈ packets, L^(-aDensity) < P.ordinaryDensity 0 cell grid w tau Eset
        (fun z => field (planeCoordinates z)) q) →
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
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
      (∀ z, z∉Eset → f z=0) →
    ∀ (g : AngularGrid), (g.branching:ℝ) = SourceParameters.step L →
      (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
      2 ≤ g.rootWidth →
      (∫ z in Fset, ‖∑ q ∈ packets, P.crossPacketValue alt hAlt 0 b v f z q‖
        ∂volume.prod volume) ≤ L^(-decay)*ratio*(volume.prod volume).real Fset := by
  obtain ⟨CD,CS,CT,hCD,hCS,hCT,hEnergy⟩ := exists_intrinsic_cross_energy hVariation
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hgap
  obtain ⟨A,Lbase,haA,hLbase,hmain⟩ := source_high_density_popular_recovery
    hVariation hLL cStar cEta CEta cb Cb F c0 cone Lip aDensity p0 (3*p0+6) decay D K H J₀
    hcStar hcEta hCEta hcb.le hCb hF hc0 hcone hconeK hLip haDensity hp0
    (by positivity) hdecay hD hgap hJ
  refine ⟨CD,CS,CT,hCD,hCS,hCT,A,max Lbase (ordinaryDensityUpper^(1/4:ℝ)),haA,
    hLbase.trans (le_max_left _ _),?_⟩
  intro L hL κ _ N Label Item _ P packets w tau hw hscale hratioBound hprofile horder hpackets
    d heq₁ heq₂ heq₃ heq₄ heq₅ hwEq htauEq hunit
    Eset Fset field cell grid hEset hEfinite hdensity hcell hcellrange
    l r hfield hstrip hEstrip hFstrip hFset hFfinite hFpositive
    ratio widthScale hratio hloglow hloghigh hratioEq hwidthLow hwidthHigh hwidthEq htimeLow htimeHigh
    alt hAlt hMargin hBin b hbEq hb hb1 hsupp hmotion hactive hlocal hfrequencyLo hfrequency
    hspectrum haltSpectrum v hv f hf hf1 hfs g hbranch hzero hrootWidth
  have hLb : Lbase≤L := (le_max_left _ _).trans hL
  have hLtwo : 2≤L := by linarith [hLbase.trans hLb]
  have hU : ordinaryDensityUpper^(1/4:ℝ)≤L := (le_max_right _ _).trans hL
  have halt : ∀ j l a k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤d.cStar/P.length j ∧ d.cEta≤d.w*et ∧ d.w*et≤d.CEta := by
    intro j l a k xi et hn
    simpa only [zero_add,heq₁,heq₂,heq₃,hwEq] using haltSpectrum j l a k xi et hn
  have henergy := hEnergy N κ Label Item P packets d heq₁ heq₂ heq₃ heq₄ heq₅ alt hAlt
    halt hMargin hBin L p0 hLtwo hp0 hunit hU hprofile packets (Finset.Subset.refl _)
    f hf hf1 Eset hEset hEfinite hfs v hv
  rw [←hbEq] at henergy
  exact hmain L hLb κ N Label Item P packets 0 w tau hw hscale hratioBound hprofile horder hpackets
    Eset Fset field cell grid hEset hEfinite hdensity hcell hcellrange
    l r hfield hstrip hEstrip hFstrip hFset hFfinite hFpositive
    ratio widthScale hratio hloglow hloghigh hratioEq hwidthLow hwidthHigh hwidthEq htimeLow htimeHigh
    alt hAlt b hb hb1 hsupp hmotion hactive hlocal hfrequencyLo hfrequency hspectrum haltSpectrum
    v hv f hf hf1 g hbranch hzero hrootWidth henergy

end LipschitzHilbert.PacketLatticeData

end

end OAI
