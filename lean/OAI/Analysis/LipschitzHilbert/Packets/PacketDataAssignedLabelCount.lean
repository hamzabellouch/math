import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedTopSelector
import OAI.Analysis.LipschitzHilbert.Trees.SourceInhabitedLabels

namespace OAI

/-! Only labels carrying assigned packets enter the local source model.
Their actual packet directions lie in the assignment window, so local
slope multiplicity gives a fixed slot bound independent of empty labels. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone)
  (hF : 0 ≤ F) (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

local notation "Q" => referenceFamily (P.assignedTopFamily packets assigned top)
  oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => referenceOriginalLabel (P.assignedTopFamily packets assigned top)
  oldSlope newSlope R cone w

theorem assignedReference_inhabited_label_count (j : Fin N) (d radius : ℝ) (H K : ℕ)
    (hd : 0 < d) (hradius : radius ≤ K)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) d H)
    (hangle : ∀ q ∈ packets, assigned q = top →
      |oldSlope+P.rowSlope q.1 q.2.1-newSlope| ≤ radius*d) :
    (((Q).inhabitedFamily).labels j).card ≤ (2*K+1)*H := by
  let labelSlope := fun l : (Q).labels j => newSlope+(Q).rowSlope j l
  have hlocalQ := P.assignedTopReference_localMultiplicity packets assigned top
    oldSlope newSlope R cone w F hw hcone hF hwide hfrequency j d H hlocal
  have hwindow := SourceSlopeLabels.window_card_le
    (Finset.univ : Finset ((Q).labels j)) labelSlope (t := newSlope) hd hlocalQ hradius
  have hcount : (Finset.univ : Finset ((Q).inhabitedLabels j)).card ≤
      (SourceSlopeLabels.window Finset.univ labelSlope newSlope d radius).card := by
    apply Finset.card_le_card_of_injOn ((Q).inhabitedOriginalLabel j)
    · intro l _
      obtain ⟨u⟩ := (Q).inhabitedLabel_nonempty j l
      let l' := orig j ((Q).inhabitedOriginalLabel j l)
      have hu : P.AssignedTopItem packets assigned j l' := u
      have hp := P.assignedTopItem_mem packets assigned top j l' hu
      have ha := P.assignedTopItem_assignment packets assigned top j l' hu
      have hs := hangle ⟨j,⟨l'.val.2,hu.val⟩⟩ hp ha
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      change |newSlope+(Q).rowSlope j ((Q).inhabitedOriginalLabel j l)-newSlope| ≤ radius*d
      rw [P.assignedTopReference_physical_center packets assigned top oldSlope newSlope R
        cone w F hw hcone hF hwide hfrequency j ((Q).inhabitedOriginalLabel j l)]
      exact hs
    · intro l _ m _ h
      apply Subtype.ext
      exact congrArg (fun r : (Q).labels j => r.val) h
  change ((Q).inhabitedLabels j).card ≤ (2*K+1)*H
  simpa only [Finset.card_univ,Fintype.card_coe] using hcount.trans hwindow

end LipschitzHilbert.PacketLatticeData

end

end OAI
