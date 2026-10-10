import OAI.Analysis.LipschitzHilbert.Packets.PacketDataMaskedBand
import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalOffchildGrouping

namespace OAI

/-! Exact assignment and length regrouping of the physical packet sum. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)

def assignedPhysicalBands (z : ℝ×ℝ) (p : τ×Fin N) : EuclideanSpace ℂ κ :=
  ∑ q∈packets.filter (fun q => (assigned q,q.1)=p),
    P.physicalMaskedValue alt hAlt t b v f T L A z q

theorem assignedPhysicalBands_eq (z : ℝ×ℝ) (p : τ×Fin N) :
    P.assignedPhysicalBands alt hAlt t b v f T L A packets assigned z p =
      ∑ q∈packets.filter (fun q => (assigned q,q.1)=p),
        P.physicalMaskedValue alt hAlt t b v f T L A z q := rfl

/-- The angular amplitude of the original masked packets is exactly
its amplitude assembled from literal assigned-top physical bands. -/
theorem physicalMaskedAmplitude_top_bands
    (P : PacketLatticeData N κ Label Item)
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
      (P.assignedPhysicalBands alt hAlt t b v f T L A packets assigned z)
      phase a z level cell := by
  exact grid.sourcePacketAmplitude_regroup tops slope precision cutoff weight K gap
    packets assigned hassigned (fun q => q.1) stop
    (P.physicalMaskedValue alt hAlt t b v f T L A z) phase a z level cell

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

end LipschitzHilbert.PacketLatticeData

end

end OAI
