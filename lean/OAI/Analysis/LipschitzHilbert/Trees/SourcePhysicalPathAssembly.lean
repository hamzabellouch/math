import OAI.Analysis.LipschitzHilbert.Packets.SourcePhysicalPacketAssembly
import OAI.Analysis.LipschitzHilbert.Trees.SourcePathAmplitudeCongr

namespace OAI

/-! The measurable active path and every marked predictor are unchanged
when the original physical packets are grouped into their assigned top
and length bands. Both sides retain the original selector coefficients. -/

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

def assignedPhysicalBands (z : ℝ×ℝ) (p : τ×Fin N) : EuclideanSpace ℂ κ :=
  (P.restrictPackets (packets.filter (fun q => assigned q = p.1))).physicalMaskedBand
    (P.restrictedAlternate alt (packets.filter (fun q => assigned q = p.1)))
    (P.restrictedAlternate_bound alt hAlt (packets.filter (fun q => assigned q = p.1)))
    t b v f (fun j l u => T j l u.val) L A (z.2-t*z.1) p.2 z.1

theorem physicalActivePathValue_top_bands
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → ℝ×ℝ → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (stop : τ → Fin N → ℕ) (phase : ℕ → ℂ) (a α p M : ℝ)
    {Kb : ℕ} (shift : Fin Kb) (top : τ) (count : ℕ) (z : ℝ×ℝ) :
    grid.sourceActivePathValue tops slope precision cutoff weight K gap
      packets assigned (fun q => stop (assigned q) q.1)
      (P.physicalMaskedValue alt hAlt t b v f T L A) phase a α p M shift top count z =
    grid.sourceActivePathValue tops slope precision cutoff weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun q => stop q.1 q.2)
      (P.assignedPhysicalBands alt hAlt t b v f T L A packets assigned)
      phase a α p M shift top count z := by
  apply grid.sourceActivePathValue_congr_amplitude tops slope precision cutoff weight K gap
    packets assigned (fun q => stop (assigned q) q.1)
    (P.physicalMaskedValue alt hAlt t b v f T L A)
    (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun q => stop q.1 q.2)
    (P.assignedPhysicalBands alt hAlt t b v f T L A packets assigned) phase a z
    _ α p M shift top count
  intro level cell
  exact P.physicalMaskedAmplitude_top_bands alt hAlt t b v f T L A grid tops slope precision
    cutoff weight K gap packets assigned hassigned stop phase a z level cell

theorem physicalShiftedPathPrediction_top_bands
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → ℝ×ℝ → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (stop : τ → Fin N → ℕ) (phase : ℕ → ℂ) (a p μ : ℝ)
    {Kb : ℕ} (shift : Fin Kb) (top : τ) (j : ℕ) (z : ℝ×ℝ) :
    grid.sourceShiftedPathPrediction tops slope precision cutoff weight K gap
      packets assigned (fun q => stop (assigned q) q.1)
      (P.physicalMaskedValue alt hAlt t b v f T L A) phase a p μ shift top z j =
    grid.sourceShiftedPathPrediction tops slope precision cutoff weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun q => stop q.1 q.2)
      (P.assignedPhysicalBands alt hAlt t b v f T L A packets assigned)
      phase a p μ shift top z j := by
  apply grid.sourceShiftedPathPrediction_congr_amplitude tops slope precision cutoff weight K gap
    packets assigned (fun q => stop (assigned q) q.1)
    (P.physicalMaskedValue alt hAlt t b v f T L A)
    (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun q => stop q.1 q.2)
    (P.assignedPhysicalBands alt hAlt t b v f T L A packets assigned) phase a z
    _ p μ shift top j
  intro level cell
  exact P.physicalMaskedAmplitude_top_bands alt hAlt t b v f T L A grid tops slope precision
    cutoff weight K gap packets assigned hassigned stop phase a z level cell

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
