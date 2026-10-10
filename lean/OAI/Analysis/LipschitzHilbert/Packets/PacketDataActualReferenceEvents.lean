import OAI.Analysis.LipschitzHilbert.Packets.PacketDataRecenteredSelector
import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedParentCentralGain

namespace OAI

/-! The actual parent-square and continuing-path reference events of the
source packet family. The union is independent of every complex phase. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (L oldSlope C w F : ℝ) (hw : 0 < w) (hC : 0 ≤ C) (hF : 0 ≤ F)
  (hwide : ∀ i : Option (Fin (SourceParameters.blockCount L)),
    (C+(SourceParameters.branching L)^(if i.isNone then 3 else 2))*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)
  (g : AngularGrid) (tops : Finset τ) (T : τ → SlopeBox)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (hKb : 0 < SourceParameters.blockCount L)

def actualReferenceData (top : τ) (i : Option (Fin (SourceParameters.blockCount L))) :
    PhysicalReferenceData N κ Label Item :=
  P.recenteredReferenceData alt hAlt oldSlope (T top).slope (T top).length
    (C+(SourceParameters.branching L)^(if i.isNone then 3 else 2)) w F hw
    (add_nonneg hC (pow_nonneg (SourceParameters.branching_pos L).le _)) hF
    (hwide i) hfrequency b v f (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩))

def actualReferencePacketSet (top : τ) :
    Option (Fin (SourceParameters.blockCount L)) → Finset P.PacketIndex
  | none => sourceReferencePackets packets (fun u => P.length u.1)
      (fun u => oldSlope+P.rowSlope u.1 u.2.1) (T top).length (T top).slope
      (C+(SourceParameters.branching L)^3) w
  | some shift =>
      let cut := g.rootWidth/(SourceParameters.branching L)^2
      let stop := fun j : Fin N => g.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
      g.fixedPathResidualPackets tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut packets assigned (fun u => stop u.1) (ShiftedBlocks.endpoint shift)
        (g.sourceTopTerminalCount T cut w hw hKb shift top-1) (T top).slope

def actualReferenceSelection (top : τ) (i : Option (Fin (SourceParameters.blockCount L))) :
    Finset (P.actualReferenceData alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
      b v f T assigned top i).family.PacketIndex :=
  P.recenteredReferenceSelection oldSlope (T top).slope (T top).length
    (C+(SourceParameters.branching L)^(if i.isNone then 3 else 2)) w F hw
    (add_nonneg hC (pow_nonneg (SourceParameters.branching_pos L).le _)) hF
    (hwide i) hfrequency
    (P.actualReferencePacketSet L oldSlope C w hw g tops T packets assigned hKb top i)

def actualReferenceBad (maskExponent q : ℝ) (top : τ) : Set (ℝ×ℝ) :=
  ⋃ i : Option (Fin (SourceParameters.blockCount L)),
    ((P.actualReferenceData alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
      b v f T assigned top i).restrictPackets
      (P.actualReferenceSelection alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
        b v f g tops T packets assigned hKb top i)).bad
          L maskExponent (q+8) (2*q+9) (2*q+11)

theorem actualReferenceBad_measurable (maskExponent q : ℝ) (top : τ) :
    MeasurableSet (P.actualReferenceBad alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
      b v f g tops T packets assigned hKb maskExponent q top) :=
  MeasurableSet.iUnion fun i =>
    ((P.actualReferenceData alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
      b v f T assigned top i).restrictPackets
      (P.actualReferenceSelection alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
        b v f g tops T packets assigned hKb top i)).bad_measurable _ _ _ _ _

theorem actualReferencePacketSet_subset (top : τ)
    (i : Option (Fin (SourceParameters.blockCount L))) :
    P.actualReferencePacketSet L oldSlope C w hw g tops T packets assigned hKb top i ⊆ packets := by
  cases i with
  | none => exact Finset.filter_subset _ _
  | some i => exact Finset.filter_subset _ _

theorem actualReferenceBad_excludes (maskExponent q : ℝ) (top : τ) (z : ℝ×ℝ)
    (hz : z ∉ P.actualReferenceBad alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
      b v f g tops T packets assigned hKb maskExponent q top)
    (i : Option (Fin (SourceParameters.blockCount L))) :
    z ∉ ((P.actualReferenceData alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
      b v f T assigned top i).restrictPackets
      (P.actualReferenceSelection alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
        b v f g tops T packets assigned hKb top i)).bad
          L maskExponent (q+8) (2*q+9) (2*q+11) :=
  fun hi => hz (mem_iUnion.mpr ⟨i,hi⟩)

end LipschitzHilbert.PacketLatticeData

end

end OAI
