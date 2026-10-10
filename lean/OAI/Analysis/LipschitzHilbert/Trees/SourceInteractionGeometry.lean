import OAI.Analysis.LipschitzHilbert.Trees.SourceSelectedEnvelopeEnergy
import OAI.Analysis.LipschitzHilbert.Trees.SourceGramMargin
import OAI.Analysis.LipschitzHilbert.Estimates.StoppingScaleIntervals

namespace OAI

/-! The short family used in the selected-tree argument is defined by
actual nonzero Gram interactions. Its angular geometry follows from the
packet spectra, rather than being a separate analytic premise. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def interactingShortPackets (S T : Finset P.PacketIndex) (gap : ℕ) : Finset P.PacketIndex :=
  S.filter fun s => ∃ q∈T, q.1.val+gap≤s.1.val ∧ ∃ k : κ,
    (∫ z, inner ℂ (P.physicalPacket 0 s.1 s.2.1 s.2.2 k z)
      (P.physicalPacket 0 q.1 q.2.1 q.2.2 k z) ∂volume.prod volume)≠0

theorem interactingShortPackets_subset (S T : Finset P.PacketIndex) (gap : ℕ) :
    P.interactingShortPackets S T gap⊆S := Finset.filter_subset _ _

theorem interacting_short_length (S T : Finset P.PacketIndex) (gap : ℕ) (L : ℝ)
    (hT : ∀ q∈T, P.length q.1≤L) (s : P.PacketIndex)
    (hs : s∈P.interactingShortPackets S T gap) : P.length s.1≤L := by
  obtain ⟨_,q,hq,hgap,_⟩ := Finset.mem_filter.mp hs
  exact (P.length_antitone (show q.1≤s.1 by change q.1.val≤s.1.val; omega)).trans (hT q hq)

theorem interacting_short_direction (S T : Finset P.PacketIndex) (gap : ℕ)
    (t w cStar cEta CEta cb : ℝ) (hw : 0<w) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hconstants : (cStar/cEta)*(1+1/(2:ℝ)^gap)+1/(2:ℝ)^gap≤cb/4)
    (hT : ∀ q∈T, |P.rowSlope q.1 q.2.1-t|≤w/P.length q.1)
    (hspectrum : ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
      |xi+P.rowSlope j l*eta|≤cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta)
    (s : P.PacketIndex) (hs : s∈P.interactingShortPackets S T gap) :
    |P.rowSlope s.1 s.2.1-t|≤cb*(w/P.length s.1)/4 := by
  obtain ⟨_,q,hq,hgap,k,hinner⟩ := Finset.mem_filter.mp hs
  have h := gram_short_direction
    (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (P.physicalPacket 0 q.1 q.2.1 q.2.2 k)
    (P.rowSlope s.1 s.2.1) (P.rowSlope q.1 q.2.1) t (P.length s.1) (P.length q.1)
    w cStar cEta CEta cb 1 ((2:ℝ)^gap) (P.length_pos s.1) (P.length_pos q.1)
    hw hcStar hcEta (by norm_num) (by positivity) (P.length_scale_gap q.1 s.1 gap hgap)
    (by simpa only [one_div] using hconstants) (by simpa only [one_mul] using hT q hq)
    (hspectrum s.1 s.2.1 s.2.2 k) (hspectrum q.1 q.2.1 q.2.2 k) hinner
  convert h using 1
  ring

theorem interacting_short_margin (S T : Finset P.PacketIndex) (gap : ℕ)
    (w cStar cEta margin cb : ℝ) (hw : 0<w) (hcEta : 0<cEta)
    (hconstants : cb/2≤margin-cStar/cEta)
    (cell : P.PacketIndex → Set ℝ)
    (hspectrum : ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
      |xi+P.rowSlope j l*eta|≤cStar/P.length j ∧ cEta≤w*eta)
    (hmargin : ∀ s∈S, ∀ k xi eta,
      planarAngularFourier (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (xi,eta)≠0 →
        Icc (-xi/eta-margin*(w/P.length s.1)) (-xi/eta+margin*(w/P.length s.1))⊆cell s)
    (s : P.PacketIndex) (hs : s∈P.interactingShortPackets S T gap) :
    Icc (P.rowSlope s.1 s.2.1-cb*(w/P.length s.1)/2)
      (P.rowSlope s.1 s.2.1+cb*(w/P.length s.1)/2)⊆cell s := by
  obtain ⟨hsS,q,_,_,k,hinner⟩ := Finset.mem_filter.mp hs
  intro u hu
  have huabs : |u-P.rowSlope s.1 s.2.1|≤(cb/2)*(w/P.length s.1) := by
    apply abs_le.mpr
    constructor <;> linarith [hu.1,hu.2]
  exact gram_margin_direction_mem
    (P.physicalPacket 0 s.1 s.2.1 s.2.2 k) (P.physicalPacket 0 q.1 q.2.1 q.2.2 k)
    (P.rowSlope s.1 s.2.1) (P.length s.1) w cStar cEta margin u (cell s)
    (P.length_pos s.1) hw hcEta (hspectrum s.1 s.2.1 s.2.2 k)
    (hmargin s hsS k) (huabs.trans (mul_le_mul_of_nonneg_right hconstants
      (div_nonneg hw.le (P.length_pos s.1).le))) hinner

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
