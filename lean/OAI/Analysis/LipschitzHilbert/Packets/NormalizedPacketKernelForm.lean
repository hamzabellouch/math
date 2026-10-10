import OAI.Analysis.LipschitzHilbert.Packets.NormalizedPacketLattice
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataKernelForm

namespace OAI

/-! The actual normalized Fourier kernels realize the finite physical
coefficient form, including every carrier and the exact area factors. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
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

local notation "P" => normalizedPacketLattice F q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile

variable (G : SchwartzMap (ℝ×ℝ) ℂ)
  (hG : planarProfileConstant (analysisProfile G q nu) (2*order)≤C)

local notation "alt" => normalizedAnalysisFamily F q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile G
local notation "hAlt" => normalizedAnalysisFamily_bound F q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile G hG

theorem normalized_packet_kernel_form
    (S : Finset (P).PacketIndex) (b : ∀ j, (P).labels j → κ → ℝ → ℂ)
    (u : ℝ×ℝ → ℝ) (g f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : MemLp f 2 (volume.prod volume)) :
    let KA := fun (s : (P).PacketIndex) (k : κ) => horizontalFrequencyKernel
      (scaledFrequencyWindow F ((P).length s.1) width (theta s.1 s.2.1)
        (2*Real.pi*center k) ((P).length_pos s.1).ne' hwidth.ne')
      nu q ((P).length s.1) (theta s.1 s.2.1)
    let KB := fun (s : (P).PacketIndex) (k : κ) => verticalFrequencyKernel
      (scaledFrequencyWindow G ((P).length s.1) width (theta s.1 s.2.1)
        (2*Real.pi*center k) ((P).length_pos s.1).ne' hwidth.ne')
      nu q width (center k)
    (∫ z, inner ℂ (∑ s∈S, (P).crossPacketValue alt hAlt 0 b u g z s) (f z)
      ∂volume.prod volume) =
      ∑ s∈S, ∑ k, (((P).length s.1*width:ℝ):ℂ)⁻¹*
        packetProduct (KA s k) (KB s k) (fun z => f z k)
          (fun z => b s.1 s.2.1 k (u z)) (fun z => g z k)
          ((P).length s.1*width) ((P).actualX s.1 s.2.1 s.2.2,(P).actualZ s.1 s.2.1 s.2.2) := by
  intro KA KB
  apply (P).cross_kernel_form alt hAlt S b u g f hf (fun s k x => KA s k x) (fun s k x => KB s k x)
    (fun s => ((P).actualX s.1 s.2.1 s.2.2,(P).actualZ s.1 s.2.1 s.2.2))
  · intro s _ k x
    exact normalizedPacketLattice_synthesis F q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile s.1 s.2.1 s.2.2 k x
  · intro s _ k x
    have h := normalizedAnalysisFamily_packet F q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale labels originX originZ theta center site hinj hprofile G s.1 s.2.1 s.2.2 k x
    change physicalPlanarPacket (alt s.1 s.2.1 s.2.2 k)
      ((P).actualX s.1 s.2.1 s.2.2)
      ((P).actualZ s.1 s.2.1 s.2.2+0*(P).actualX s.1 s.2.1 s.2.2)
      ((P).length s.1) width (0+theta s.1 s.2.1) (2*Real.pi*center k)
      _ _ x = analyzingWave ((P).length s.1*width) (KB s k)
        ((P).actualX s.1 s.2.1 s.2.2,(P).actualZ s.1 s.2.1 s.2.2) x
    simpa only [KB,zero_mul,add_zero,zero_add] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
