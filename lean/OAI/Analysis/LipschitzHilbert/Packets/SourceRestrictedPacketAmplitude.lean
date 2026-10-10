import OAI.Analysis.LipschitzHilbert.Packets.SourceLabeledPacketRestriction
import OAI.Analysis.LipschitzHilbert.Phase.AngularSourceAmplitude

namespace OAI

/-! The angular sums of a literal packet restriction are the original
selected sums. Stopping levels, top assignments, hierarchy masses and
analyzing coefficients are unchanged. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- Exact transport of a selected angular amplitude to restricted item fibers. -/
theorem restrictPackets_packetAmplitude {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (Q : Finset P.PacketIndex) (grid : AngularGrid) (slope : P.PacketIndex → ℝ)
    (stop : P.PacketIndex → ℕ) (base : P.PacketIndex → E)
    (transition : ℕ → ℤ → ℂ) (level : ℕ) (cell : ℤ) :
    grid.packetAmplitude (Finset.univ : Finset (P.restrictPackets Q).PacketIndex)
      (fun u => slope ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩)
      (fun u => stop ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩)
      (fun u => base ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩) transition level cell =
      grid.packetAmplitude Q slope stop base transition level cell := by
  unfold AngularGrid.packetAmplitude AngularGrid.packetSet
  convert P.sum_restrictPackets_filter Q
    (fun u => grid.packetPathProduct transition level (stop u) (slope u) • base u)
    (fun u => grid.index level (slope u) = cell ∧ level ≤ stop u) using 1 <;>
    congr 1 <;> ext u <;> simp

/-- The residual is transported exactly, including both stopping filters. -/
theorem restrictPackets_packetResidual {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (Q : Finset P.PacketIndex) (grid : AngularGrid) (slope : P.PacketIndex → ℝ)
    (stop : P.PacketIndex → ℕ) (base : P.PacketIndex → E)
    (transition : ℕ → ℤ → ℂ) (lower upper : ℕ) (cell : ℤ) :
    grid.packetResidual (Finset.univ : Finset (P.restrictPackets Q).PacketIndex)
      (fun u => slope ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩)
      (fun u => stop ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩)
      (fun u => base ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩) transition lower upper cell =
      grid.packetResidual Q slope stop base transition lower upper cell := by
  unfold AngularGrid.packetResidual AngularGrid.packetSet
  simp only [Finset.sum_filter]
  exact P.sum_restrictPackets Q (fun u =>
    if grid.index lower (slope u) = cell ∧ lower ≤ stop u then
      if stop u < upper then
        grid.packetPathProduct transition lower (stop u) (slope u) • base u else 0
    else 0)

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

/-- Physical residual transport preserves the original analyzing integral
and the same hierarchy mass at every packet's stopping level. -/
theorem restrictPackets_physicalSourceResidual {τ : Type*}
    (Q : Finset P.PacketIndex) (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → (ℝ×ℝ) → ℝ) (assigned : P.PacketIndex → τ)
    (stop : Fin N → ℕ) (T : τ → SlopeBox) (L A alpha : ℝ) (z : ℝ×ℝ)
    (transition : ℕ → ℤ → ℂ) (lower upper : ℕ) (cell : ℤ) :
    grid.packetResidual (Finset.univ : Finset (P.restrictPackets Q).PacketIndex)
      (fun u => slope (assigned ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩)) (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cutoff weight
        (fun u => assigned ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩) (fun u => stop u.1)
        ((P.restrictPackets Q).physicalMaskedValue (P.restrictedAlternate alt Q)
          (P.restrictedAlternate_bound alt hAlt Q) t b v f
          (fun j l u => T (assigned ⟨j,⟨l,u.val⟩⟩)) L A z) alpha z)
      transition lower upper cell =
    grid.packetResidual Q (fun u => slope (assigned u)) (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cutoff weight assigned (fun u => stop u.1)
        (P.physicalMaskedValue alt hAlt t b v f
          (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z) alpha z)
      transition lower upper cell := by
  let value := P.physicalMaskedValue alt hAlt t b v f
    (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
  have hvalue (u : (P.restrictPackets Q).PacketIndex) :
      (P.restrictPackets Q).physicalMaskedValue (P.restrictedAlternate alt Q)
        (P.restrictedAlternate_bound alt hAlt Q) t b v f
        (fun j l u => T (assigned ⟨j,⟨l,u.val⟩⟩)) L A z u =
      value ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩ := rfl
  have hbase :
      grid.sourcePacketBase tops slope precision cutoff weight
        (fun u : (P.restrictPackets Q).PacketIndex => assigned ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩)
        (fun u => stop u.1)
        ((P.restrictPackets Q).physicalMaskedValue (P.restrictedAlternate alt Q)
          (P.restrictedAlternate_bound alt hAlt Q) t b v f
          (fun j l u => T (assigned ⟨j,⟨l,u.val⟩⟩)) L A z) alpha z =
      fun u => grid.sourcePacketBase tops slope precision cutoff weight assigned
        (fun u => stop u.1) value alpha z ⟨u.1,⟨u.2.1,u.2.2.val⟩⟩ := by
    funext u
    dsimp only [AngularGrid.sourcePacketBase]
    rw [hvalue]
  rw [hbase]
  exact P.restrictPackets_packetResidual Q grid (fun u => slope (assigned u))
    (fun u => stop u.1)
    (grid.sourcePacketBase tops slope precision cutoff weight assigned (fun u => stop u.1)
      value alpha z) transition lower upper cell

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
