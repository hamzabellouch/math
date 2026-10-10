import OAI.Analysis.LipschitzHilbert.Packets.SourcePacketRegroup
import OAI.Analysis.LipschitzHilbert.Packets.SourceLabeledPacketRestriction

namespace OAI

/-! Individual original physical packets and their top/length bands
produce the same angular node amplitude, with all masks and analyzing
coefficients retained. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- The angular amplitude of the original masked packets is exactly
its amplitude assembled from literal assigned-top physical bands. -/
theorem physicalMaskedAmplitude_top_bands
    (P : SourceLabeledLattice N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → ℝ×ℝ → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (stop : τ → Fin N → ℕ) (phase : ℕ → ℂ) (a : ℝ)
    (z : ℝ×ℝ) (level : ℕ) (cell : ℤ) :
    grid.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned
      (fun q => stop (assigned q) q.1) (P.physicalMaskedValue alt hAlt t b v f T L A z)
      phase a z level cell =
    grid.sourcePacketAmplitude tops slope precision cutoff weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => (P.restrictPackets (packets.filter (fun q => assigned q = p.1))).physicalMaskedBand
        (P.restrictedAlternate alt (packets.filter (fun q => assigned q = p.1)))
        (P.restrictedAlternate_bound alt hAlt (packets.filter (fun q => assigned q = p.1)))
        t b v f (fun j l u => T j l u.val) L A (z.2-t*z.1) p.2 z.1)
      phase a z level cell := by
  rw [grid.sourcePacketAmplitude_regroup tops slope precision cutoff weight K gap
    packets assigned hassigned (fun q => q.1) stop
    (P.physicalMaskedValue alt hAlt t b v f T L A z) phase a z level cell]
  apply congrArg (fun values : τ×Fin N → EuclideanSpace ℂ κ =>
    grid.sourcePacketAmplitude tops slope precision cutoff weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      values phase a z level cell)
  funext p
  rcases p with ⟨top,j⟩
  rw [P.restrictPackets_physicalMaskedBand alt hAlt]
  have hpoint : (z.1,z.2-t*z.1+t*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  rw [hpoint]
  apply Finset.sum_congr
  · ext q
    simp only [Finset.mem_filter,Prod.mk.injEq,and_assoc]
  · intro q _
    rfl

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
