import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedPartial

namespace OAI

/-! Weighted maximal estimates for actual selected trees of unrestricted
packet data. The bounded reference lattice is constructed from the tree's
own angular cone. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData

theorem exists_selected_weighted_tree_maximal (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M Q : ℕ), Cb≤Q →
      ∀ (t w a b r F : ℝ), 0<w → 0<r → 0≤F → Cb*w≤P.width →
      (∀ k, |P.frequency k|≤F/w) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
    ∀ (S : Finset P.PacketIndex) (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ),
      (∀ q∈S, P.length q.1≤r) →
      (∀ q∈S, |P.actualX q.1 q.2.1 q.2.2-a|≤r) →
      (∀ q∈S, |(P.actualZ q.1 q.2.1 q.2.2-b)-t*(P.actualX q.1 q.2.1 q.2.2-a)|≤P.width) →
      (∀ q∈S, ∀ k xi eta, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,eta)≠0 →
        |xi+P.rowSlope q.1 q.2.1*eta|≤cStar/P.length q.1 ∧ cEta≤w*eta ∧ w*eta≤CEta) →
      (∀ q∈S, cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t| ∧
        |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1) →
      let E := fun z => treeProductPolynomial a (b-t*a) r P.width t z^2*
        P.physicalTreeMaximal 0 (P.onPackets S c) z^2
      Integrable E (volume.prod volume) ∧
      (∫ z, E z ∂volume.prod volume)≤(((2*Q+1)*M:ℕ):ℝ)*C*P.referenceEnvelopeConstant^2*
        ∑ q∈S, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width := by
  obtain ⟨C,hC,hmax⟩ := SourceLabeledLattice.exists_weighted_labeled_tree_maximal hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M Q hQ t w a b r F hw hr hF hwide hfreq hlocal
    S c hlen hX hZ hspectrum hangle
  have hnear := fun q hq => (hangle q hq).2
  let T := P.selectedReference S t Cb w F hw hCb hF hwide hfreq hnear
  let d := P.selectedCoefficients S t Cb w F hw hCb hF hwide hfreq hnear c
  have hmem (j : Fin N) (l : T.labels j) (v : P.SelectedItem S j l) :
      (⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ : P.PacketIndex)∈S :=
    P.selectedItem_mem S j l v
  have hcard (j : Fin N) : (T.labels j).card≤(2*Q+1)*M :=
    P.selectedReference_card S t Cb w F hw hCb hF hwide hfreq hnear M Q hQ hlocal j
  have hTY (j : Fin N) (l : T.labels j) (v : P.SelectedItem S j l) :
      |T.actualZ j l v-(b-t*a)|≤T.width := by
    change |(P.selectedReference S t Cb w F hw hCb hF hwide hfreq hnear).actualZ j l v-(b-t*a)|≤P.width
    rw [P.selectedReference_actualZ S t Cb w F hw hCb hF hwide hfreq hnear j l v]
    have he : P.actualZ j (P.selectedOriginalLabel S j l) v.val-
        t*P.actualX j (P.selectedOriginalLabel S j l) v.val-(b-t*a)=
        (P.actualZ j (P.selectedOriginalLabel S j l) v.val-b)-
          t*(P.actualX j (P.selectedOriginalLabel S j l) v.val-a) := by ring
    rw [he]
    exact hZ ⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ (hmem j l v)
  have hspec (j : Fin N) (l : T.labels j) (v : P.SelectedItem S j l)
      (k : κ) (xi eta : ℝ) (h : planarAngularFourier (T.physicalPacket t j l v k) (xi,eta)≠0) :
      |xi+(t+T.rowSlope j l)*eta|≤cStar/T.length j ∧ cEta≤w*eta ∧ w*eta≤CEta :=
    P.selectedReference_spectrum_at S t Cb w F hw hCb hF hwide hfreq hnear cStar cEta CEta
      j l v k xi eta (hspectrum ⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ (hmem j l v) k xi eta) h
  have hs := hmax N κ Label (P.SelectedItem S) T ((2*Q+1)*M) hcard
    t w a (b-t*a) r hw hr d
    (fun j l v => hlen ⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ (hmem j l v))
    (fun j l v => hX ⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ (hmem j l v))
    hTY hspec
    (fun j l v => hangle ⟨j,⟨P.selectedOriginalLabel S j l,v.val⟩⟩ (hmem j l v))
  dsimp only at hs ⊢
  have heval (z : ℝ×ℝ) : T.physicalTreeMaximal t d z=
      P.physicalTreeMaximal 0 (P.onPackets S c) z :=
    P.selectedReference_maximal S t Cb w F hw hCb hF hwide hfreq hnear c z
  have henergy : (∑ j, ∑ l : T.labels j, ∑ v : P.SelectedItem S j l,
      ‖d j l v‖^2*T.length j*T.width)=
        ∑ q∈S, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width :=
    P.selectedReference_energy S t Cb w F hw hCb hF hwide hfreq hnear c
  have hconstant : T.absoluteConstant=P.referenceEnvelopeConstant := rfl
  simp only [heval,henergy,hconstant] at hs
  exact hs

end LipschitzHilbert.PacketLatticeData

end

end OAI
