import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDensityPopularRecovery

namespace OAI

/-! High ordinary density supplies the actual popular forest. Its retained
angular cells put every keeper in the source direction chart, so both
the top-direction and root-interval hypotheses of recovery are derived. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem source_high_density_popular_recovery
    (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (cStar cEta CEta cb Cb F c0 cone Lip aDensity p0 qEnergy decay : ℝ)
    (D K H J₀ : ℕ)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta)
    (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hcone : 1 ≤ cone) (hconeK : cone ≤ K) (hLip : 0 ≤ Lip)
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
      6+2*(8*D+1) ≤ P.order → packets.Nonempty →
    ∀ (Eset Fset : Set (ℝ×ℝ)) (field : Plane → ℝ)
      (cell : ∀ j, P.labels j → ℤ) (grid : ℤ),
      MeasurableSet Eset → (volume.prod volume) Eset ≠ ∞ →
      (∀ q ∈ packets, L^(-aDensity) < P.ordinaryDensity oldSlope cell grid w tau Eset
        (fun z => field (planeCoordinates z)) q) →
      (∀ q ∈ packets, oldSlope+P.rowSlope q.1 q.2.1 ∈
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
    ∀ (g : AngularGrid), (g.branching:ℝ) = SourceParameters.step L →
      (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
      2 ≤ g.rootWidth →
      (∫ z, ‖∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q‖^2
        ∂volume.prod volume) ≤ (L^qEnergy)^2*(volume.prod volume).real Eset →
      (∫ z in Fset, ‖∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q‖
        ∂volume.prod volume) ≤ L^(-decay)*ratio*(volume.prod volume).real Fset := by
  obtain ⟨A,Lbase,haA,hLbase,hmain⟩ := source_density_popular_recovery
    hVariation hLL cStar cEta CEta cb Cb F c0 cone Lip aDensity p0 qEnergy decay D K H J₀
    hcStar hcEta hCEta hcb hCb hF hc0 (by linarith only [hcone]) hconeK hLip
    haDensity hp0 hqEnergy hdecay hD hgap hJ
  obtain ⟨Lforest,hLforest,hforest⟩ := exists_packet_density_forest_in_cells aDensity haDensity
  obtain ⟨Lwidth,hwidth⟩ := eventually_atTop.mp
    ((Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop (by norm_num : (0:ℝ)<9/10))).eventually_ge_atTop 12)
  refine ⟨A,max Lbase (max Lforest Lwidth),haA,hLbase.trans (le_max_left _ _),?_⟩
  intro L hL κ _ N Label Item _ P packets oldSlope w tau hw hscale hratioBound hprofile horder hpackets
    Eset Fset field cell grid hEset hEfinite hdensity hcell hcellrange
    l r hfield hstrip hEstrip hFstrip hFset hFfinite hFpositive
    ratio widthScale hratio hloglow hloghigh hratioEq hwidthLow hwidthHigh hwidthEq htimeLow htimeHigh
    alt hAlt b hb hb1 hsupp hmotion hactive hlocal hfrequencyLo hfrequency hspectrum haltSpectrum
    v hv f hf hf1 g hbranch hzero hrootWidth henergy
  have hLb : Lbase ≤ L := (le_max_left _ _).trans hL
  have hLf : Lforest ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLw : Lwidth ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hW : 12*w ≤ P.width := by
    rw [hwidthEq]
    exact mul_le_mul_of_nonneg_right ((hwidth L hLw).trans hwidthLow) hw.le
  obtain ⟨forest,hseed,_⟩ := hforest L hLf N κ Label Item P packets hpackets oldSlope cell grid
    cone w tau hcone hw hW Eset (fun z => field (planeCoordinates z)) hEset hEfinite
    (product_slope_lipschitz field hfield).continuous.measurable hdensity hcell
  have htop (i : forest.keepers) : (forest.top i).slope ∈ Icc (-1:ℝ) 1 :=
    hcellrange i.val.val i.val.property (hseed i)
  exact hmain L hLb κ N Label Item P packets oldSlope w tau hw hscale hratioBound hprofile horder
    Eset Fset field forest (fun i => abs_le.mpr (htop i))
    l r hfield hstrip hEstrip hFstrip hFset hFfinite hFpositive
    ratio widthScale hratio hloglow hloghigh hratioEq hwidthLow hwidthHigh hwidthEq htimeLow htimeHigh
    alt hAlt b hb hb1 hsupp hmotion hactive hlocal hfrequencyLo hfrequency hspectrum haltSpectrum
    v hv f hf hf1 g (-1) hbranch hzero
    (fun i => ⟨(htop i).1,(htop i).2.trans (by linarith only [hrootWidth])⟩) henergy

end LipschitzHilbert.PacketLatticeData

end

end OAI
