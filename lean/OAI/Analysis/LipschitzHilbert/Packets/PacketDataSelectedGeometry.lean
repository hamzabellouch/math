import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedReference
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceOrdinaryTree

namespace OAI

/-! The selected reference family retains the original density tests
and spectra. No bound on the unselected slopes is involved. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item) (S : Finset P.PacketIndex)
  (t Cb w F : ℝ) (hw : 0<w) (hCb : 0≤Cb) (hF : 0≤F)
  (hwide : Cb*w≤P.width) (hfrequency : ∀ k, |P.frequency k|≤F/w)
  (hnear : ∀ q∈S, |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1)
local notation "Q" => P.selectedReference S t Cb w F hw hCb hF hwide hfrequency hnear

def selectedCells (cell : ∀ j, P.labels j → ℤ) : ∀ j, (Q).labels j → ℤ :=
  fun j l => cell j (P.selectedOriginalLabel S j l)

theorem selectedReference_densityTile (cell : ∀ j, P.labels j → ℤ)
    (j : Fin N) (l : (Q).labels j) (u : P.SelectedItem S j l) :
    (Q).densityTile t (P.selectedCells S t Cb w F hw hCb hF hwide hfrequency hnear cell) ⟨j,l,u⟩ =
      P.densityTile 0 cell ⟨j,P.selectedOriginalLabel S j l,u.val⟩ := by
  have hx := P.selectedReference_actualX S t Cb w F hw hCb hF hwide hfrequency hnear j l u
  have hz := P.selectedReference_actualZ S t Cb w F hw hCb hF hwide hfrequency hnear j l u
  unfold SourceLabeledLattice.densityTile densityTile
  rw [hx,hz]
  congr 1
  apply Prod.ext
  · rfl
  · dsimp only
    ring

theorem selectedReference_density (cell : ∀ j, P.labels j → ℤ)
    (grid : ℤ) (tau : ℝ) (E : Set (ℝ×ℝ)) (v : ℝ×ℝ → ℝ)
    (j : Fin N) (l : (Q).labels j) (u : P.SelectedItem S j l) :
    (Q).ordinaryDensity t (P.selectedCells S t Cb w F hw hCb hF hwide hfrequency hnear cell)
        grid w tau E v ⟨j,l,u⟩ =
      P.ordinaryDensity 0 cell grid w tau E v ⟨j,P.selectedOriginalLabel S j l,u.val⟩ := by
  unfold SourceLabeledLattice.ordinaryDensity ordinaryDensity
  rw [P.selectedReference_densityTile S t Cb w F hw hCb hF hwide hfrequency hnear cell j l u]
  rfl

theorem selectedReference_slope (j : Fin N) (l : (Q).labels j) :
    t+(Q).rowSlope j l=P.rowSlope j (P.selectedOriginalLabel S j l) := by
  change t+(P.rowSlope j (P.selectedOriginalLabel S j l)-t)=_
  ring

theorem selectedReference_spectrum_at (cStar cEta CEta : ℝ)
    (j : Fin N) (l : (Q).labels j) (u : P.SelectedItem S j l) (k : κ) (xi eta : ℝ)
    (hspectrum : planarAngularFourier
      (P.physicalPacket 0 j (P.selectedOriginalLabel S j l) u.val k) (xi,eta)≠0 →
        |xi+P.rowSlope j (P.selectedOriginalLabel S j l)*eta|≤cStar/P.length j ∧
          cEta≤w*eta ∧ w*eta≤CEta)
    (h : planarAngularFourier ((Q).physicalPacket t j l u k) (xi,eta)≠0) :
    |xi+(t+(Q).rowSlope j l)*eta|≤cStar/(Q).length j ∧ cEta≤w*eta ∧ w*eta≤CEta := by
  have hpacket := P.selectedReference_physicalPacket S t Cb w F hw hCb hF hwide hfrequency hnear j l u k
  have hf := congrArg (fun f : SchwartzMap (ℝ×ℝ) ℂ => planarAngularFourier f (xi,eta)) hpacket
  rw [hf] at h
  rw [P.selectedReference_slope S t Cb w F hw hCb hF hwide hfrequency hnear j l]
  exact hspectrum h

end LipschitzHilbert.PacketLatticeData

end

end OAI
