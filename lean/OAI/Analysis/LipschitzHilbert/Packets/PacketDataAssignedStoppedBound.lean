import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedTopEnvelope
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedReference
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedPhysical
import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedTopOffchild

namespace OAI

/-! The actual masked packet sum agrees with the bounded reference
families used in the supported stopped-path estimates. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

/-- The common-type recentered family used in the actual top envelopes. -/
local notation "Q" => assignedReferenceFamily P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

local notation "orig" => assignedReferenceOriginalLabel P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

local notation "alts" => assignedReferenceAlternate P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency alt

local notation "halt" => assignedReferenceAlternate_bound P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency alt hAlt

variable (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)

local notation "selector" => assignedReferenceSelector P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency b

theorem assignedReference_rawBand_original (L A : ℝ) (z : ℝ×ℝ) (top : τ) (j : Fin N)
    (hcondition : ∀ q ∈ packets, assigned q = top →
      P.referenceCondition oldSlope (T top).slope (R top) cone w q.1 q.2.1) :
    ((Q top).withProfile (alts top) (halt top)).rawBand
      (fun j l u => (T top).mask L A z •
        (Q top).physicalMultiplierCoefficient (T top).slope (selector top) v f j l u)
      0 j z.1 (z.2-(T top).slope*z.1) =
    P.assignedPhysicalBands alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A packets assigned z (top,j) := by
  have hr := (Q top).physicalMaskedBand_const_eq_rawBand (alts top) (halt top)
    (T top).slope (selector top) v f (T top) L A z j
  exact hr.symm.trans (P.assignedTopReference_topMaskBand_all packets assigned top
    oldSlope (R top) cone w F hw hcone hF hwide hfrequency T hcondition alt hAlt b v f L A z j)

/-- Original packets, their literal top/length fibers and the recentered
raw bands have exactly the same source amplitude. -/
theorem assignedReference_packetAmplitude_original
    (grid : AngularGrid) (tops : Finset τ) (precision : τ → ℝ) (cut : ℝ)
    (weight : τ → (ℝ×ℝ) → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (hcondition : ∀ q ∈ packets,
      P.referenceCondition oldSlope (T (assigned q)).slope (R (assigned q)) cone w q.1 q.2.1)
    (stop : τ → Fin N → ℕ) (phase : ℕ → ℂ) (a L A : ℝ)
    (z : ℝ×ℝ) (level : ℕ) (cell : ℤ) :
    grid.sourcePacketAmplitude tops (fun t => (T t).slope) precision cut weight K gap
      packets assigned (fun q => stop (assigned q) q.1)
      (P.physicalMaskedValue alt hAlt oldSlope b v f
        (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z) phase a z level cell =
    grid.sourcePacketAmplitude tops (fun t => (T t).slope) precision cut weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => ((Q p.1).withProfile (alts p.1) (halt p.1)).rawBand
        (fun j l u => (T p.1).mask L A z •
          (Q p.1).physicalMultiplierCoefficient (T p.1).slope (selector p.1) v f j l u)
        0 p.2 z.1 (z.2-(T p.1).slope*z.1)) phase a z level cell := by
  rw [grid.sourcePacketAmplitude_regroup tops (fun t => (T t).slope) precision cut weight K gap
    packets assigned hassigned (fun q => q.1) stop
    (P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z) phase a z level cell]
  apply congrArg (fun values : τ×Fin N → EuclideanSpace ℂ κ =>
    grid.sourcePacketAmplitude tops (fun t => (T t).slope) precision cut weight K gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      values phase a z level cell)
  funext p
  rw [P.assignedReference_rawBand_original packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f L A z p.1 p.2
    (fun q hq hqt => by simpa only [hqt] using hcondition q hq)]
  exact (P.assignedPhysicalBands_eq alt hAlt oldSlope b v f
    (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A packets assigned z p).symm


/-- The exact off-child regrouping also retains original packet masks
and coefficients; only the assignment fiber is summed. -/
theorem assignedReference_offchildAmplitude_original
    (grid : AngularGrid) (tops : Finset τ) (precision : τ → ℝ) (cut : ℝ)
    (weight : τ → (ℝ×ℝ) → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (hcondition : ∀ q ∈ packets,
      P.referenceCondition oldSlope (T (assigned q)).slope (R (assigned q)) cone w q.1 q.2.1)
    (stop : τ → Fin N → ℕ) (phase : ℕ → ℂ) (a L A : ℝ)
    (z : ℝ×ℝ) (level : ℕ) (cell : ℤ) (child : Finset τ) :
    grid.sourcePacketAmplitude tops (fun t => (T t).slope) precision cut weight K gap
      (packets.filter (fun u => assigned u ∉ child)) assigned (fun q => stop (assigned q) q.1)
      (P.physicalMaskedValue alt hAlt oldSlope b v f
        (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z) phase a z level cell =
    grid.sourcePacketAmplitude tops (fun t => (T t).slope) precision cut weight K gap
      ((tops ×ˢ (Finset.univ : Finset (Fin N))).filter fun p => p.1 ∉ child)
      Prod.fst (fun p => stop p.1 p.2)
      (fun p => ((T p.1).mask L A z : ℂ) •
        ((Q p.1).withProfile (alts p.1) (halt p.1)).rawBand
          ((Q p.1).physicalMultiplierCoefficient (T p.1).slope (selector p.1) v f)
          0 p.2 z.1 (z.2-(T p.1).slope*z.1)) phase a z level cell := by
  rw [P.physicalOffchildAmplitude_top_bands alt hAlt oldSlope b v f
    (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A packets assigned grid tops
    (fun t => (T t).slope) precision cut weight K gap hassigned stop phase a z level cell child]
  apply congrArg (fun values : τ×Fin N → EuclideanSpace ℂ κ =>
    grid.sourcePacketAmplitude tops (fun t => (T t).slope) precision cut weight K gap
      ((tops ×ˢ (Finset.univ : Finset (Fin N))).filter fun p => p.1 ∉ child)
      Prod.fst (fun p => stop p.1 p.2) values phase a z level cell)
  funext p
  have hr := P.assignedReference_rawBand_original packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f L A z p.1 p.2
    (fun q hq hqt => by simpa only [hqt] using hcondition q hq)
  have hs := ((Q p.1).withProfile (alts p.1) (halt p.1)).rawBand_coeff_real_smul
    ((Q p.1).physicalMultiplierCoefficient (T p.1).slope (selector p.1) v f)
    ((T p.1).mask L A z) 0 p.2 z.1 (z.2-(T p.1).slope*z.1)
  exact hr.symm.trans (hs.trans (IsScalarTower.algebraMap_smul ℂ _ _).symm)

end LipschitzHilbert.PacketLatticeData

end

end OAI
