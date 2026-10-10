import OAI.Analysis.LipschitzHilbert.Packets.PacketLatticeData

namespace OAI

/-! The unrestricted family passes its original spectra to every local
reference lattice without enlarging either frequency strip. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone * w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F / w)
local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

@[simp] theorem referenceFamily_slope (j : Fin N) (l : (Q).labels j) :
    newSlope + (Q).rowSlope j l = oldSlope + P.rowSlope j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) := by
  change newSlope + (P.rowSlope j _ + (oldSlope-newSlope)) = _
  ring

theorem referenceFamily_spectrum_at (cStar cEta CEta : ℝ)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) (k : κ) (xi eta : ℝ)
    (hspectrum : planarAngularFourier (P.physicalPacket oldSlope j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u k) (xi,eta) ≠ 0 →
        |xi + (oldSlope + P.rowSlope j
          (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)) * eta| ≤ cStar/P.length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta)
    (h : planarAngularFourier ((Q).physicalPacket newSlope j l u k) (xi,eta) ≠ 0) :
    |xi + (newSlope + (Q).rowSlope j l) * eta| ≤ cStar/(Q).length j ∧
      cEta ≤ w*eta ∧ w*eta ≤ CEta := by
  have hpacket := P.referenceFamily_physicalPacket oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j l u k
  have hfourier := congrArg (fun f : SchwartzMap (ℝ×ℝ) ℂ => planarAngularFourier f (xi,eta)) hpacket
  rw [hfourier] at h
  rw [P.referenceFamily_slope oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j l]
  exact hspectrum h

theorem referenceFamily_bin_at (radius : ℝ)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) (k : κ) (xi eta : ℝ)
    (hbin : planarAngularFourier (P.physicalPacket oldSlope j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u k) (xi,eta) ≠ 0 →
        |eta-P.frequency k| ≤ radius/P.width)
    (h : planarAngularFourier ((Q).physicalPacket newSlope j l u k) (xi,eta) ≠ 0) :
    |eta-(Q).frequency k| ≤ radius/(Q).width := by
  have hpacket := P.referenceFamily_physicalPacket oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j l u k
  have hfourier := congrArg (fun f : SchwartzMap (ℝ×ℝ) ℂ => planarAngularFourier f (xi,eta)) hpacket
  rw [hfourier] at h
  exact hbin h

/-- The local family carries the original selector as a function of the
physical direction. Only its label type changes. -/
def referenceSelector (b : ∀ j, P.labels j → κ → ℝ → ℂ) :
    ∀ j, (Q).labels j → κ → ℝ → ℂ :=
  fun j l => b j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l)

theorem referenceSelector_support (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (cb Cb : ℝ)
    (hb : ∀ j l k s, b j l k s ≠ 0 →
      cb*w/P.length j ≤ |s-(oldSlope+P.rowSlope j l)| ∧
        |s-(oldSlope+P.rowSlope j l)| ≤ Cb*w/P.length j) :
    ∀ j (l : (Q).labels j) k s,
      P.referenceSelector oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency b j l k s ≠ 0 →
        cb*w/(Q).length j ≤ |s-(newSlope+(Q).rowSlope j l)| ∧
          |s-(newSlope+(Q).rowSlope j l)| ≤ Cb*w/(Q).length j := by
  intro j l k s h
  rw [P.referenceFamily_slope oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j l]
  exact hb j _ k s h

end LipschitzHilbert.PacketLatticeData

end

end OAI
