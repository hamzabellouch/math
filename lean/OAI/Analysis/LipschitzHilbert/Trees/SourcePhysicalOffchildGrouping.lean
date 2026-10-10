import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalPathAssembly
import OAI.Analysis.LipschitzHilbert.Trees.SourceOffchildRegroup

namespace OAI

/-! The original masked off-child packets give the exact off-child sum
of their assigned physical top bands. This is the identification needed
when applying the original-selector off-child estimate to a stopped path. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)

theorem assignedPhysicalBands_eq (z : ℝ×ℝ) (p : τ×Fin N) :
    P.assignedPhysicalBands alt hAlt t b v f T L A packets assigned z p =
      ∑ q ∈ packets.filter (fun q => (assigned q,q.1) = p),
        P.physicalMaskedValue alt hAlt t b v f T L A z q := by
  rcases p with ⟨top,j⟩
  unfold assignedPhysicalBands
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

theorem physicalOffchildAmplitude_top_bands
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → ℝ×ℝ → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (stop : τ → Fin N → ℕ) (phase : ℕ → ℂ) (a : ℝ)
    (z : ℝ×ℝ) (level : ℕ) (cell : ℤ) (child : Finset τ) :
    grid.sourcePacketAmplitude tops slope precision cutoff weight K gap
      (packets.filter (fun q => assigned q ∉ child)) assigned
      (fun q => stop (assigned q) q.1) (P.physicalMaskedValue alt hAlt t b v f T L A z)
      phase a z level cell =
    grid.sourcePacketAmplitude tops slope precision cutoff weight K gap
      ((tops ×ˢ (Finset.univ : Finset (Fin N))).filter (fun p => p.1 ∉ child))
      Prod.fst (fun p => stop p.1 p.2)
      (P.assignedPhysicalBands alt hAlt t b v f T L A packets assigned z)
      phase a z level cell := by
  rw [grid.sourcePacketAmplitude_regroup_offchild tops slope precision cutoff weight K gap
    packets assigned hassigned (fun q => q.1) stop
    (P.physicalMaskedValue alt hAlt t b v f T L A z) phase a z level cell child]
  apply congrArg (fun values : τ×Fin N → EuclideanSpace ℂ κ =>
    grid.sourcePacketAmplitude tops slope precision cutoff weight K gap
      ((tops ×ˢ (Finset.univ : Finset (Fin N))).filter (fun p => p.1 ∉ child))
      Prod.fst (fun p => stop p.1 p.2) values phase a z level cell)
  funext p
  exact (P.assignedPhysicalBands_eq alt hAlt t b v f T L A packets assigned z p).symm

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
