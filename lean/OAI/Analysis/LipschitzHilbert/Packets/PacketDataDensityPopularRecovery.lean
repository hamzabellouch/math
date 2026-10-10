import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDensitySelectorGoodSet
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDensityGoodRecovery
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDensityJetNormalization
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataActualPacketRecovery
import OAI.Analysis.LipschitzHilbert.Trees.SourceParentWidth

namespace OAI

/-! Popular recovery from an actual density forest. The common good set,
its deleted area, the mask error, all count/concentration hypotheses, and
the global weight budget are constructed before invoking recovery. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem source_density_popular_recovery
    (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cb F c0 cone Lip aDensity p0 qEnergy decay : ℝ)
    (D K H J₀ : ℕ)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta)
    (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hcone : 0 ≤ cone) (hconeK : cone ≤ K) (hLip : 0 ≤ Lip)
    (haDensity : 0 ≤ aDensity) (hp0 : 0 ≤ p0) (hqEnergy : 0 ≤ qEnergy)
    (hdecay : 0 ≤ decay) (hD : 4 ≤ D)
    (hgap : cStar < cEta*cb) (hJ : 2*cone+1 ≤ (2:ℝ)^J₀) :
    ∃ A L0 : ℝ, aDensity+3 < A ∧ 16 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (oldSlope w tau : ℝ), 0 < w →
      P.scale = 4*(L^(A+2)*P.width) → P.ratioBound = 4*L^(A+2) →
      (2^P.order*P.profileBound)*3^(2*P.order) ≤ L^p0 →
      6+2*(8*D+1) ≤ P.order →
    ∀ (Eset Fset : Set (ℝ×ℝ)) (field : Plane → ℝ)
      (forest : PacketDensityForest P packets oldSlope L aDensity cone w tau Eset
        (fun z => field (planeCoordinates z))),
      let T := forest.top
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
      (∀ k, c0/w ≤ |P.frequency k|) → (∀ k, |P.frequency k| ≤ F/w) →
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
      (∫ z in Fset, ‖∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q‖
        ∂volume.prod volume) ≤ L^(-decay)*ratio*(volume.prod volume).real Fset := by
  let loss := 2*(qEnergy+decay+1)
  obtain ⟨A,Cn,Ct,Lgood,haA,hA,hCn,hCt,_hLgood,hgood⟩ := source_density_selector_good_set
    hVariation hLL cStar cEta CEta cb Cb F cone hcStar hcEta hCEta hcb hCb hF hcone hgap
    aDensity p0 loss Lip D K H J₀ haDensity hp0 (by dsimp [loss]; linarith only [hqEnergy,hdecay]) hLip hD
    hconeK hJ
  have hfinish := source_density_recovery_of_good_set hVariation
    cStar cEta CEta cb Cb F c0 cone Lip aDensity p0 qEnergy decay D K H
    hcStar hcEta hCEta hcb hCb hF hc0 hcone hconeK hLip haDensity hp0 hqEnergy hdecay hD hgap
    A Cn Ct haA hA hCn hCt
  obtain ⟨L0,hL0⟩ := eventually_atTop.mp
    (hfinish.and ((SourceParameters.eventually_parent_reference_width cone).and
      (eventually_ge_atTop (max Lgood (max 16 (F*cone+2))))))
  refine ⟨A,max L0 16,haA,le_max_right _ _,?_⟩
  intro L hL κ _ N Label Item _ P packets oldSlope w tau hw hscale hratioBound hprofile horder
    Eset Fset field forest T hslopes l r hfield hstrip hEstrip hFstrip hFset hFfinite hFpositive
    ratio widthScale hratio hloglow hloghigh hratioEq hwidthLow hwidthHigh hwidthEq htimeLow htimeHigh
    alt hAlt b hb hb1 hsupp hmotion hactive hlocal hfrequencyLo hfrequency hspectrum haltSpectrum
    v hv f hf hf1 g start hbranch hzero hslope henergy
  have hLbase : L0 ≤ L := (le_max_left _ _).trans hL
  obtain ⟨hfinish,hparent,hlarge⟩ := hL0 L hLbase
  have hLg : Lgood ≤ L := (le_max_left _ _).trans hlarge
  have hL16 : 16 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hfactor : F*cone+2 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hL1 : 1 ≤ L := by linarith only [hL16]
  have hLp : 0 < L := by linarith only [hL16]
  have hwidePair := hparent widthScale w P.width hwidthLow hw hwidthEq
  have hwide : cone*w ≤ P.width := (mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_right (sq_nonneg (SourceParameters.branching L))) hw.le).trans hwidePair.2
  have hratioExp : ratio ≤ Real.exp (2*L) :=
    (Real.log_le_iff_le_exp hratio).mp (hloghigh.trans (by linarith only [hL16]))
  obtain ⟨G,hG,hGF,hGarea,hweightG,hlogG,hcountG,hconcG,hintG,hmaskG,hsepG⟩ :=
    hgood L hLg κ N Label Item P packets oldSlope w tau Eset field forest hprofile horder
      alt hAlt hw hwide hfrequency b hb hb1 hsupp hmotion hactive hlocal v hv f hf hf1
      (fun q _ => hspectrum q.1 q.2.1 q.2.2)
      (fun q _ => haltSpectrum q.1 q.2.1 q.2.2)
      l r hslopes hfield hstrip hEstrip ratio Fset hratio hFset hFfinite hFstrip
      hratioExp hloghigh hratioEq.le widthScale hwidthLow hwidthHigh htimeLow htimeHigh hwidthEq
  exact hfinish κ N Label Item P packets oldSlope w tau hw hwide hfrequency hscale hratioBound hprofile horder
    Eset Fset field forest hslopes l r hfield hstrip hEstrip hFstrip hFset hFfinite hFpositive
    ratio widthScale hratio hloglow hloghigh hratioEq hwidthLow hwidthHigh hwidthEq htimeLow htimeHigh
    alt hAlt b hb hb1 hsupp hmotion hactive hlocal hfrequencyLo hspectrum haltSpectrum
    v hv f hf hf1 g start hbranch hzero hslope henergy G
    ⟨hG,hGF,hGarea,hweightG,hlogG,hcountG,hconcG,hintG,hmaskG,hsepG⟩

end LipschitzHilbert.PacketLatticeData

end

end OAI
