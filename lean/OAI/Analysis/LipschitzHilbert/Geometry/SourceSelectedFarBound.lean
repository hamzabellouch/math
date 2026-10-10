import OAI.Analysis.LipschitzHilbert.Geometry.SourceTreeFarEnergy
import OAI.Analysis.LipschitzHilbert.Trees.SourceTrimInteractions
import OAI.Analysis.LipschitzHilbert.Geometry.SourceSelectedInteractionPacking
import OAI.Analysis.LipschitzHilbert.Trees.SourceSelectedTopGeometry

namespace OAI

/-! The far contribution belonging to one actual recorded positive
selection top. The required short-packet packing follows from a combination
of selection order and the original Fourier margins. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_selected_far_gram_bound (hL : LepingleInput)
    (cStar cEta CEta cb : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hcb : 0<cb) (hcb4 : cb≤4) (hspectral : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (M Q farGap packGap : ℕ),
      ∀ (w tau sigma beta epsilon A margin F : ℝ), 0<w → w≤P.width → 0≤F →
      (∀ k, |P.frequency k|≤F/w) →
      (cStar/cEta)*(1+1/(2:ℝ)^farGap)+1/(2:ℝ)^farGap≤cb/4 →
      (1+cb/4)/(2:ℝ)^packGap≤cb/4 → cb/2≤margin-cStar/cEta →
      2*(1+(1+cb/4))+1/2≤A → cb/4≤Q →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
    ∀ (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (initial remaining : Finset P.PacketIndex) (tops : List SlopeBox),
      P.SizeStoppingRun false w cb tau sigma epsilon A cell grid c initial tops remaining →
      (∀ q∈P.selectedPackets false w cb A cell grid initial tops, ‖c q.1 q.2.1 q.2.2‖≤beta) →
      (∀ q∈P.selectedPackets false w cb A cell grid initial tops,
        P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈P.selectedPackets false w cb A cell grid initial tops, epsilon≤cb*(w/P.length q.1)/4) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
        |xi+P.rowSlope j l*eta|≤cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta) →
      (∀ s∈P.selectedPackets false w cb A cell grid initial tops, ∀ k xi eta,
        planarAngularFourier (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (xi,eta)≠0 →
        Icc (-xi/eta-margin*(w/P.length s.1)) (-xi/eta+margin*(w/P.length s.1))⊆
          scaledAngularCell (w/P.topLength) grid s.1.val (cell s.1 s.2.1)) →
    ∀ p∈P.sizeSelectionRecords false w cb A cell grid initial tops,
      ‖∑ s∈P.selectedPackets false w cb A cell grid initial tops,
        ∫ z, inner ℂ (P.packetVector c s z) (P.longPacketSum c p.2 farGap s.1 z)
          ∂volume.prod volume‖^2≤
        (4*P.profileBound*beta)^2*256*
          (82944*SizeStoppingRun.selectedEnvelopePackingConstant cb packGap M Q)^2*
          1296*Real.pi^2*p.1.length*P.width*
            (((3*M:ℕ):ℝ)*C*P.absoluteConstant^2*
              ∑ q∈p.2, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width) := by
  obtain ⟨C,hC,hFar⟩ := exists_tree_far_gram_bound hL cStar cEta CEta cb 1
    hcStar hcEta hCEta hcb.le (by norm_num) hspectral
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M Q farGap packGap w tau sigma beta epsilon A margin F
    hw hwW hF hfreq hfar hpack hmarginSize hA hQ hlocal cell grid c initial remaining tops
    hrun hcoeff hrow hepsilon hspectrum hmargin p hp
  let all := P.selectedPackets false w cb A cell grid initial tops
  let I := P.interactingShortPackets all p.2 farGap
  have hsub : I⊆all := P.interactingShortPackets_subset all p.2 farGap
  have hgeom := hrun.recorded_packet_geometry hw hrow p hp
  have hTnear (q : P.PacketIndex) (hq : q∈p.2) : |P.rowSlope q.1 q.2.1-p.1.slope|≤w/P.length q.1 :=
    (hgeom q hq).2.2.2.2
  have hnear := P.interacting_short_direction all p.2 farGap p.1.slope w cStar cEta CEta cb
    hw hcStar hcEta hfar hTnear hspectrum
  have hIlen := P.interacting_short_length all p.2 farGap p.1.length (fun q hq => (hgeom q hq).1)
  have hIpack := hrun.selected_interacting_box_packing hw hwW hcb cStar cEta CEta margin
    hcStar hcEta farGap packGap M Q hfar hpack hmarginSize hA hQ hlocal hrow hepsilon hspectrum hmargin p hp
  rw [P.far_pairing_restrict_to_interacting]
  have hb := hFar N κ Label Item P M 1 (by norm_num) p.1.slope w p.1.x p.1.y p.1.length F beta
    (SizeStoppingRun.selectedEnvelopePackingConstant cb packGap M Q) hw p.1.length_pos hF
    (by simpa only [one_mul] using hwW) hfreq hlocal c I p.2 farGap
    (fun q hq => (hgeom q hq).1) (fun q hq => (hgeom q hq).2.1)
    (fun q hq => (hgeom q hq).2.2.1) hspectrum
    (fun q hq => by simpa only [one_mul] using (hgeom q hq).2.2.2)
    (fun s hs => hcoeff s (hsub hs))
    (fun s hs => short_direction_shear_bound _ _ cb w _ P.width (P.length_pos s.1) P.width_pos
      hw.le hwW hcb4 (hnear s hs)) hIlen hIpack
  simpa only [show (2*1+1:ℕ)=3 by decide] using hb

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
