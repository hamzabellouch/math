import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSignedSelectedArea
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSizeTest

namespace OAI

/-! The ordinary two-sided size-selection lemma with an L2 top-area
bound, derived from the actual packet geometry and scalar variation input. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_two_sided_size_selection_with_area (hL : LepingleInput)
    (cStar cEta CEta cb : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hcb : 0<cb) (hcb4 : cb≤4) (hspectral : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M Q gap packGap : ℕ),
      ∀ (w tau sigma D epsilon A margin F : ℝ), 0<sigma → 0≤D → cb≤1/4 → 0<epsilon →
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
      (initial : Finset P.PacketIndex),
      (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c initial T≤(D*sigma)^2*T.area) →
      (∀ q∈initial,
        P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈initial, epsilon≤cb*(w/P.length q.1)/4) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
        |xi+P.rowSlope j l*eta|≤cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta) →
      (∀ s∈initial, ∀ k xi eta,
        planarAngularFourier (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (xi,eta)≠0 →
        Icc (-xi/eta-margin*(w/P.length s.1)) (-xi/eta+margin*(w/P.length s.1))⊆
          scaledAngularCell (w/P.topLength) grid s.1.val (cell s.1 s.2.1)) →
    ∃ positive middle negative remaining,
      P.SizeStoppingRun false w cb tau sigma epsilon A cell grid c initial positive middle ∧
      P.SizeStoppingRun true w cb tau sigma epsilon A cell grid c middle negative remaining ∧
      remaining⊆initial ∧
      (∀ T : SlopeBox, T.width=P.width → T.length≤tau →
        P.unsignedSizeTestEnergy w cb cell grid c remaining T≤sigma^2*T.area) ∧
      (positive.map SlopeBox.area).sum+(negative.map SlopeBox.area).sum≤
        (4*(selectedNearConstant P gap M Q+
          2*Real.sqrt (2*selectedFarConstant P cb D C packGap M Q))/sigma^2)*
            ∫ z, ‖g z‖^2 ∂volume.prod volume := by
  obtain ⟨C,hC,hArea⟩ := exists_signed_selected_area_bound hL cStar cEta CEta cb
    hcStar hcEta hCEta hcb hcb4 hspectral
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M Q gap packGap w tau sigma D epsilon A margin F
    hsigma hD hcbquarter hepsilonPos hw hwW hF hfreq hgap hpack hmarginSize hA hQ hQnear hlocal
    cell grid g hg c hc initial hsize hrow hepsilon hspectrum hmargin
  subst c
  have hAhalf : 1/2≤A := by linarith
  obtain ⟨positive,middle,negative,remaining,hpos,hneg,hrsub,hgood⟩ :=
    P.exists_two_sided_size_selection w cb tau sigma epsilon A hw.le hcb.le hepsilonPos hAhalf
      cell grid (P.ordinaryCoefficient g) initial
  have hsubset (sign : Bool) (R : Finset P.PacketIndex) (ts : List SlopeBox) (hR : R⊆initial) :
      P.selectedPackets sign w cb A cell grid R ts⊆initial := by
    intro q hq
    obtain ⟨p,hp,hqp⟩ := (P.mem_selectedPackets sign w cb A cell grid R ts q).mp hq
    exact hR (P.sizeSelectionRecords_subset sign w cb A cell grid R ts p hp hqp)
  have happly (sign : Bool) (R rem : Finset P.PacketIndex) (ts : List SlopeBox)
      (hrun : P.SizeStoppingRun sign w cb tau sigma epsilon A cell grid (P.ordinaryCoefficient g) R ts rem)
      (hR : R⊆initial) :
      (ts.map SlopeBox.area).sum≤
        (2*(selectedNearConstant P gap M Q+
          2*Real.sqrt (2*selectedFarConstant P cb D C packGap M Q))/sigma^2)*
            ∫ z, ‖g z‖^2 ∂volume.prod volume := by
    apply hArea N κ Label Item P sign M Q gap packGap w tau sigma D epsilon A margin F
      hsigma hD hcbquarter hw hwW hF hfreq hgap hpack hmarginSize hA hQ hQnear hlocal
      cell grid g hg (P.ordinaryCoefficient g) rfl R rem ts hrun
    · intro T hwidth hlen
      exact (P.unsignedSizeTestEnergy_mono w cb cell grid (P.ordinaryCoefficient g) hR T).trans
        (hsize T hwidth hlen)
    · intro q hq
      exact hrow q (hsubset sign R ts hR hq)
    · intro q hq
      exact hepsilon q (hsubset sign R ts hR hq)
    · exact hspectrum
    · intro q hq
      exact hmargin q (hsubset sign R ts hR hq)
  refine ⟨positive,middle,negative,remaining,hpos,hneg,hrsub,hgood,?_⟩
  have hp := happly false initial middle positive hpos (fun _ h => h)
  have hn := happly true middle remaining negative hneg hpos.remaining_subset
  convert add_le_add hp hn using 1
  ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
