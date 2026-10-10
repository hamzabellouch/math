import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledPositiveSplit
import OAI.Analysis.LipschitzHilbert.Packets.SourceFrozenCenteredCoefficient
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlotTails

namespace OAI

/-! The positive frozen main sum in the original labeled collection
is exactly the sum of the centered positive scales in its fixed slots.
The physical packets, coefficients and snapped envelopes are unchanged. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
variable {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)

theorem slotted_snappedSite (s : Fin B) (j : Fin N) (p : P.SlotItem hcard s j) :
    (P.slotted hcard s).snappedSite j p = P.snappedSite j p.1.1 p.1.2 := by
  change snappedLatticeSite (P.slotValue hcard s j (P.originX j))
    (P.slotValue hcard s j (P.originZ j)) (P.length j) P.width
    (P.slotValue hcard s j (P.rowSlope j)) (P.site j p.1.1 p.1.2) = _
  rw [P.slotValue_item hcard s j (P.originX j) p,
    P.slotValue_item hcard s j (P.originZ j) p,
    P.slotValue_item hcard s j (P.rowSlope j) p]
  rfl

theorem slotted_positiveEnvelope (s : Fin B) (j : Fin N) (p : P.SlotItem hcard s j)
    (y x : ℝ) :
    (P.slotted hcard s).positiveEnvelope j p y x = P.positiveEnvelope j p.1.1 p.1.2 y x := by
  unfold SourceLatticePacket.positiveEnvelope positiveEnvelope
  rw [P.slotted_snappedSite hcard s j p,P.slotted_length hcard]
  rfl

def frozenSlot (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, ‖b j l k t‖ ≤ 1) (s : Fin B) :
    SourceLatticePacket N κ (P.SlotItem hcard s) :=
  (P.slotted hcard s).frozenProfile (fun j p k => b j p.1.1 k t)
    (fun j p k => hb j p.1.1 k)

theorem frozenSlot_positiveEnvelope (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, ‖b j l k t‖ ≤ 1) (s : Fin B) (j : Fin N)
    (p : P.SlotItem hcard s j) (y x : ℝ) :
    (P.frozenSlot hcard t b hb s).positiveEnvelope j p y x =
      P.positiveEnvelope j p.1.1 p.1.2 y x :=
  P.slotted_positiveEnvelope hcard s j p y x

/-- Slotting and freezing reproduce the original centered physical
coefficient, with no integral or cutoff-boundary exception. -/
theorem frozenSlot_physicalCenteredCoefficient (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (s : Fin B) (j : Fin N) (p : P.SlotItem hcard s j) :
    (P.frozenSlot hcard t b hb s).physicalCenteredCoefficient t t
        (fun j => a*(2:ℝ)^j.val) v g j p =
      P.physicalFrozenCenteredCoefficient t a b v g j p.1.1 p.1.2 := by
  have hpacket (k : κ) (z : ℝ×ℝ) :
      (P.frozenSlot hcard t b hb s).physicalCenteredWave t t
          (fun j => a*(2:ℝ)^j.val) v ⟨j,p⟩ k z =
        if |v z-t| ≤ a*(2:ℝ)^j.val then
          b j p.1.1 k t*P.physicalPacket t j p.1.1 p.1.2 k z else 0 := by
    unfold SourceLatticePacket.physicalCenteredWave frozenSlot
    rw [(P.slotted hcard s).frozenProfile_physicalPacket,P.slotted_physicalPacket hcard]
    simp only [smul_apply,smul_eq_mul]
  ext k
  simp only [SourceLatticePacket.physicalCenteredCoefficient,
    physicalFrozenCenteredCoefficient,analyzingCoefficient,WithLp.ofLp_toLp]
  change ((↑(P.length j*P.width):ℂ)⁻¹)*
    (∫ z, g z k*star ((P.frozenSlot hcard t b hb s).physicalCenteredWave t t
      (fun j => a*(2:ℝ)^j.val) v ⟨j,p⟩ k z) ∂volume.prod volume) = _
  simp_rw [hpacket]
  rfl

/-- The original main positive scale is a literal fixed-slot sum. -/
theorem physicalMainScale_eq_slots (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (y x : ℝ) :
    P.physicalMainScale t a b v g j y x =
      ∑ s : Fin B, (P.frozenSlot hcard t b hb s).physicalCenteredPositiveScale
        t t (fun j => a*(2:ℝ)^j.val) v g j y x := by
  let f (l : P.labels j) (u : Item j l) : ℝ :=
    ‖P.physicalFrozenCenteredCoefficient t a b v g j l u‖*P.positiveEnvelope j l u y x
  have hsum := P.sum_slotted (E := ℝ) hcard j f
  unfold physicalMainScale SourceLatticePacket.physicalCenteredPositiveScale
  symm
  calc
    _ = ∑ s : Fin B, ∑ p : P.SlotItem hcard s j,
        ‖P.physicalFrozenCenteredCoefficient t a b v g j p.1.1 p.1.2‖*
          P.positiveEnvelope j p.1.1 p.1.2 y x := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro p _
      rw [P.frozenSlot_physicalCenteredCoefficient hcard,
        P.frozenSlot_positiveEnvelope hcard]
    _ = _ := hsum

/-- The exact identity supplies the square domination consumed by the
fixed-slot physical tail theorem. -/
theorem physicalMainSquare_le_slots (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y x : ℝ) :
    Real.sqrt (∑ j, P.physicalMainScale t a b v g j y x^2) ≤
      ∑ s : Fin B, (P.frozenSlot hcard t b hb s).physicalCenteredSquare
        t t (fun j => a*(2:ℝ)^j.val) v g y x := by
  simp_rw [P.physicalMainScale_eq_slots hcard t a b hb v g]
  exact source_slot_square_le _

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
