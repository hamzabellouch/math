import OAI.Analysis.LipschitzHilbert.Geometry.SourceSelectedFarBound
import OAI.Analysis.LipschitzHilbert.Trees.SourceSelectedQuadratic

namespace OAI

/-! Synthesis energy for the actual positive size-selection run.
All geometric and Gram bounds are derived from the source packet data;
the only analytic input here is the previously cited scalar Lepingle bound. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

def selectedNearConstant (P : SourceLabeledLattice N κ Label Item) (gap M Q : ℕ) : ℝ :=
  ((2*gap+1:ℕ):ℝ)*(((2*Q+1)*M:ℕ):ℝ)*
    ((4*Real.pi)^2*P.profileBound^2*Real.pi^2)

def selectedFarConstant (P : SourceLabeledLattice N κ Label Item)
    (cb D C : ℝ) (packGap M Q : ℕ) : ℝ :=
  (4*P.profileBound*D)^2*256*
    (82944*SizeStoppingRun.selectedEnvelopePackingConstant cb packGap M Q)^2*
      1296*Real.pi^2*(((3*M:ℕ):ℝ)*C*P.absoluteConstant^2)

theorem exists_positive_selected_synthesis_bound (hL : LepingleInput)
    (cStar cEta CEta cb : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hcb : 0<cb) (hcb4 : cb≤4) (hspectral : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (M Q gap packGap : ℕ),
      ∀ (w tau sigma D epsilon A margin F : ℝ), 0<w → w≤P.width → 0≤F →
      (∀ k, |P.frequency k|≤F/w) →
      (cStar/cEta)*(1+1/(2:ℝ)^(gap+1))+1/(2:ℝ)^(gap+1)≤cb/4 →
      (1+cb/4)/(2:ℝ)^packGap≤cb/4 → cb/2≤margin-cStar/cEta →
      2*(1+(1+cb/4))+1/2≤A → cb/4≤Q → 2*cStar/cEta≤Q →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
    ∀ (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (initial remaining : Finset P.PacketIndex) (tops : List SlopeBox),
      P.SizeStoppingRun false w cb tau sigma epsilon A cell grid c initial tops remaining →
      (∀ q∈P.selectedPackets false w cb A cell grid initial tops, ‖c q.1 q.2.1 q.2.2‖≤D*sigma) →
      (∀ q∈P.selectedPackets false w cb A cell grid initial tops,
        P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      (∀ q∈P.selectedPackets false w cb A cell grid initial tops, epsilon≤cb*(w/P.length q.1)/4) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
        |xi+P.rowSlope j l*eta|≤cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta) →
      (∀ s∈P.selectedPackets false w cb A cell grid initial tops, ∀ k xi eta,
        planarAngularFourier (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (xi,eta)≠0 →
        Icc (-xi/eta-margin*(w/P.length s.1)) (-xi/eta+margin*(w/P.length s.1))⊆
          scaledAngularCell (w/P.topLength) grid s.1.val (cell s.1 s.2.1)) →
    let S := P.selectedPackets false w cb A cell grid initial tops
    let K := selectedFarConstant P cb D C packGap M Q
    (∫ z, ‖∑ q∈S, P.packetVector c q z‖^2 ∂volume.prod volume)≤
      (selectedNearConstant P gap M Q+2*Real.sqrt (2*K))*
        ∑ q∈S, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width := by
  obtain ⟨C,hC,hFar⟩ := exists_selected_far_gram_bound hL cStar cEta CEta cb
    hcStar hcEta hCEta hcb hcb4 hspectral
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M Q gap packGap w tau sigma D epsilon A margin F
    hw hwW hF hfreq hgap hpack hmarginSize hA hQ hQnear hlocal cell grid c initial remaining tops
    hrun hcoeff hrow hepsilon hspectrum hmargin
  dsimp only
  have hAhalf : 1/2≤A := by linarith
  apply hrun.selected_gram_energy_of_quadratic hAhalf gap
    (selectedNearConstant P gap M Q) (selectedFarConstant P cb D C packGap M Q)
  · unfold selectedFarConstant
    positivity
  · dsimp only
    simp_rw [P.packetL2_inner]
    exact P.selected_comparable_gram_energy _ c gap w cStar cEta CEta hw hcEta M Q
      hQnear hlocal hspectrum
  · intro p hp
    have hf := hFar N κ Label Item P M Q (gap+1) packGap w tau sigma (D*sigma)
      epsilon A margin F hw hwW hF hfreq hgap hpack hmarginSize hA hQ hlocal cell grid c
      initial remaining tops hrun hcoeff hrow hepsilon hspectrum hmargin p hp
    change ‖P.farPairing c _ p.2 (gap+1)‖^2≤_ at hf
    apply hf.trans_eq
    unfold selectedFarConstant packetEnergySum
    ring

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
