import OAI.Analysis.LipschitzHilbert.Packets.FiniteNormalizedPacketLattice

namespace OAI

/-! The exact finite convolution form is realized on the arbitrary
retained subset of the common translated spatial lattices. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]
variable (F : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
  (topLength width scale ratioBound C : ℝ) (order : ℕ)
  (htop : 0<topLength) (hwidth : 0<width) (hC : 0<C) (horder : 3≤order)
  (hratio : 1≤ratioBound) (hscale : |scale/width|≤ratioBound)
  (labels : ∀ j, Finset (Label j))
  (origin : ∀ j, labels j → ℝ×ℝ) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
  (S : Finset (LatticeSiteIndex labels))
  (hprofile : planarProfileConstant (synthesisProfile F q nu) (2*order)≤C)


local notation "P" => finiteNormalizedPacketLattice F q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale labels origin theta center S hprofile

variable (G : SchwartzMap (ℝ×ℝ) ℂ)
  (hG : planarProfileConstant (analysisProfile G q nu) (2*order)≤C)

theorem finite_normalized_kernel_form
    (b : ∀ j, (P).labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (g f : ℝ×ℝ → EuclideanSpace ℂ κ) (hf : MemLp f 2 (volume.prod volume)) :
    let alt := fun (j : Fin N) (l : (P).labels j)
      (_a : finiteSiteFiber labels S j l.val) (_k : κ) => analysisProfile G q nu
    let hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*(P).order)≤(P).profileBound :=
      fun _ _ _ _ => hG
    let KA := fun (s : LatticeSiteIndex labels) (k : κ) => horizontalFrequencyKernel
      (scaledFrequencyWindow F ((P).length s.1) width (theta s.1 s.2.1)
        (2*Real.pi*center k) ((P).length_pos s.1).ne' hwidth.ne')
      nu q ((P).length s.1) (theta s.1 s.2.1)
    let KB := fun (s : LatticeSiteIndex labels) (k : κ) => verticalFrequencyKernel
      (scaledFrequencyWindow G ((P).length s.1) width (theta s.1 s.2.1)
        (2*Real.pi*center k) ((P).length_pos s.1).ne' hwidth.ne')
      nu q width (center k)
    (∫ z, inner ℂ (∑ a : (P).PacketIndex,
      (P).crossPacketValue alt hAlt 0 b u g z a) (f z) ∂volume.prod volume) =
    ∑ s∈S, ∑ k, (((P).length s.1*width:ℝ):ℂ)⁻¹*
      packetProduct (KA s k) (KB s k) (fun z => f z k)
        (fun z => b s.1 s.2.1 k (u z)) (fun z => g z k) ((P).length s.1*width)
        (latticeHom ((P).length s.1) width (theta s.1 s.2.1) s.2.2+origin s.1 s.2.1) := by
  intro alt hAlt KA KB
  have hrep := normalized_packet_kernel_form
    (Item := fun j l => finiteSiteFiber labels S j l)
    F q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale
    labels (fun j l => (origin j l).1) (fun j l => (origin j l).2) theta center
    (fun _ _ n => n.val) (fun _ _ => Subtype.val_injective) hprofile G hG
    (Finset.univ : Finset (P).PacketIndex) b u g f hf
  dsimp only at hrep
  simp_rw [PacketLatticeData.actualSite_eq_lattice_translate] at hrep
  have hsum := finiteNormalizedPacket_sum F q nu topLength width scale ratioBound C order htop hwidth hC horder hratio hscale labels origin theta center S hprofile
    (fun s => ∑ k, (((P).length s.1*width:ℝ):ℂ)⁻¹*
      packetProduct (KA s k) (KB s k) (fun z => f z k)
        (fun z => b s.1 s.2.1 k (u z)) (fun z => g z k) ((P).length s.1*width)
        (latticeHom ((P).length s.1) width (theta s.1 s.2.1) s.2.2+origin s.1 s.2.1))
  exact hrep.trans hsum

end LipschitzHilbert.PacketRepresentation

end

end OAI
