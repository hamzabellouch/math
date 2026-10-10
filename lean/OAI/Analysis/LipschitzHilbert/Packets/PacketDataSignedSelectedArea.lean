import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSignedSelectedSynthesis
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedArea
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedCoefficientBound

namespace OAI

/-! The selected top-area estimate for both passes, with ordinary
coefficients defined by their actual integrals. The initial size bound
supplies coefficient control; no selected-energy bound is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_signed_selected_area_bound (hL : LepingleInput)
    (cStar cEta CEta cb : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hcb : 0<cb) (hcb4 : cb≤4) (hspectral : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (negative : Bool) (M Q gap packGap : ℕ),
      ∀ (w tau sigma D epsilon A margin F : ℝ), 0<sigma → 0≤D → cb≤1/4 →
      0<w → w≤P.width → 0≤F →
      (∀ k, |P.frequency k|≤F/w) →
      (cStar/cEta)*(1+1/(2:ℝ)^(gap+1))+1/(2:ℝ)^(gap+1)≤cb/4 →
      (1+cb/4)/(2:ℝ)^packGap≤cb/4 → cb/2≤margin-cStar/cEta →
      2*(1+(1+cb/4))+1/2≤A → cb/4≤Q → 2*cStar/cEta≤Q →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
    ∀ (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (g : ℝ×ℝ → EuclideanSpace ℂ κ) (_hg : MemLp g 2 (volume.prod volume))
      (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (_hc : c=P.ordinaryCoefficient g)
      (initial remaining : Finset P.PacketIndex) (tops : List SlopeBox),
      P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining →
      (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c initial T≤(D*sigma)^2*T.area) →
      (∀ q∈P.selectedPackets negative w cb A cell grid initial tops,
        P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈P.selectedPackets negative w cb A cell grid initial tops, epsilon≤cb*(w/P.length q.1)/4) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
        |xi+P.rowSlope j l*eta|≤cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta) →
      (∀ s∈P.selectedPackets negative w cb A cell grid initial tops, ∀ k xi eta,
        planarAngularFourier (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (xi,eta)≠0 →
        Icc (-xi/eta-margin*(w/P.length s.1)) (-xi/eta+margin*(w/P.length s.1))⊆
          scaledAngularCell (w/P.topLength) grid s.1.val (cell s.1 s.2.1)) →
    (tops.map SlopeBox.area).sum≤
      (2*(selectedNearConstant P gap M Q+
        2*Real.sqrt (2*selectedFarConstant P cb D C packGap M Q))/sigma^2)*
          ∫ z, ‖g z‖^2 ∂volume.prod volume := by
  obtain ⟨C,hC,hSyn⟩ := exists_signed_selected_synthesis_bound hL cStar cEta CEta cb
    hcStar hcEta hCEta hcb hcb4 hspectral
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P negative M Q gap packGap w tau sigma D epsilon A margin F
    hsigma hD hcbquarter hw hwW hF hfreq hgap hpack hmarginSize hA hQ hQnear hlocal cell grid
    g hg c hc initial remaining tops hrun hsize hrow hepsilon hspectrum hmargin
  subst c
  have hcoeff := hrun.selected_coefficient_bound hw hcbquarter D hD hsigma.le hsize
  have hs := hSyn N κ Label Item P negative M Q gap packGap w tau sigma D epsilon A margin F
    hw hwW hF hfreq hgap hpack hmarginSize hA hQ hQnear hlocal cell grid
    (P.ordinaryCoefficient g) initial remaining tops hrun hcoeff hrow hepsilon hspectrum hmargin
  have hAhalf : 1/2≤A := by linarith
  apply hrun.selected_top_area_bound g hg hAhalf hsigma
    (selectedNearConstant P gap M Q+2*Real.sqrt (2*selectedFarConstant P cb D C packGap M Q))
  · unfold selectedNearConstant
    positivity
  · exact hs

end LipschitzHilbert.PacketLatticeData

end

end OAI
