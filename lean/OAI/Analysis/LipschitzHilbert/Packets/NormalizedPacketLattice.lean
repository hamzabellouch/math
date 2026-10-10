import OAI.Analysis.LipschitzHilbert.Packets.PacketLatticeData
import OAI.Analysis.LipschitzHilbert.Packets.NormalizedPacketProfiles

namespace OAI

/-! The actual Fourier-separated synthesis profiles on arbitrary finite
translated lattices. The slopes have no global shear restriction. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (F : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
  (topLength width scale ratioBound C : ℝ) (order : ℕ)
  (htop : 0<topLength) (hwidth : 0<width) (hC : 0<C) (horder : 3≤order)
  (hratio : 1≤ratioBound) (hscale : |scale/width|≤ratioBound)
  (labels : ∀ j, Finset (Label j))
  (originX originZ theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
  (site : ∀ j (l : labels j), Item j l → ℤ×ℤ)
  (hinj : ∀ j l, Function.Injective (site j l))
  (hprofile : planarProfileConstant (synthesisProfile F q nu) (2*order) ≤ C)

/-- All carrier components share each actual site. The profile bound
comes from the single normalized profile, independently of these data. -/
def normalizedPacketLattice : PacketLatticeData N κ Label Item where
  topLength := topLength
  width := width
  scale := scale
  ratioBound := ratioBound
  profileBound := C
  order := order
  topLength_pos := htop
  width_pos := hwidth
  profileBound_pos := hC
  order_ge_three := horder
  ratioBound_ge_one := hratio
  scale_bound := hscale
  labels := labels
  originX := originX
  originZ := originZ
  rowSlope := theta
  frequency := fun k => 2*Real.pi*center k
  site := site
  site_injective := hinj
  profile := fun _ _ _ _ => synthesisProfile F q nu
  profile_bound := fun _ _ _ _ => hprofile

local notation "P" => normalizedPacketLattice F q nu topLength width scale ratioBound C order
  htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile

theorem normalizedPacketLattice_synthesis (j : Fin N) (l : labels j)
    (u : Item j l) (k : κ) (x : ℝ×ℝ) :
    (P).physicalPacket 0 j l u k x =
      synthesisWave ((P).length j*width)
        (horizontalFrequencyKernel
          (scaledFrequencyWindow F ((P).length j) width (theta j l) (2*Real.pi*center k)
            ((P).length_pos j).ne' hwidth.ne') nu q ((P).length j) (theta j l))
        ((P).actualX j l u,(P).actualZ j l u) x := by
  change physicalPlanarPacket (synthesisProfile F q nu) _ (_+0*_)
    ((P).length j) width (0+theta j l) (2*Real.pi*center k) _ _ x = _
  simp only [zero_mul, add_zero, zero_add]
  exact physical_synthesisProfile F q nu ((P).length j) width (theta j l) (center k)
    ((P).length_pos j).ne' hwidth.ne' ((P).actualX j l u,(P).actualZ j l u) x

def normalizedAnalysisFamily (G : SchwartzMap (ℝ×ℝ) ℂ) :
    ∀ j (l : (P).labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ :=
  fun _ _ _ _ => analysisProfile G q nu

theorem normalizedAnalysisFamily_bound (G : SchwartzMap (ℝ×ℝ) ℂ)
    (hG : planarProfileConstant (analysisProfile G q nu) (2*order) ≤ C) :
    ∀ j (l : (P).labels j) (u : Item j l) k,
      planarProfileConstant (normalizedAnalysisFamily F q nu topLength width scale ratioBound C order
        htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile G
          j l u k) (2*(P).order) ≤ (P).profileBound := by
  intro j l u k
  exact hG

theorem normalizedAnalysisFamily_packet (G : SchwartzMap (ℝ×ℝ) ℂ)
    (j : Fin N) (l : labels j) (u : Item j l) (k : κ) (x : ℝ×ℝ) :
    physicalPlanarPacket
      (normalizedAnalysisFamily F q nu topLength width scale ratioBound C order
        htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile G j l u k)
      ((P).actualX j l u) ((P).actualZ j l u) ((P).length j) width (theta j l)
        (2*Real.pi*center k) ((P).length_pos j).ne' hwidth.ne' x =
      analyzingWave ((P).length j*width)
        (verticalFrequencyKernel
          (scaledFrequencyWindow G ((P).length j) width (theta j l) (2*Real.pi*center k)
            ((P).length_pos j).ne' hwidth.ne') nu q width (center k))
        ((P).actualX j l u,(P).actualZ j l u) x := by
  exact physical_analysisProfile G q nu ((P).length j) width (theta j l) (center k)
    ((P).length_pos j).ne' hwidth.ne' ((P).actualX j l u,(P).actualZ j l u) x

end LipschitzHilbert.PacketRepresentation

end

end OAI
