import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedTopSelector
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataReferenceCross

namespace OAI

/-! Each assigned top receives its exact local bounded reference family. -/
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

/-- The selected reference family has derived shear and carrier bounds. -/
def assignedReferenceFamily (top : τ) :
    SourceLabeledLattice N κ (fun j => τ×P.labels j) (P.AssignedTopItem packets assigned) :=
  (P.assignedTopFamily packets assigned top).referenceFamily oldSlope (T top).slope
    (R top) cone w F hw hcone hF hwide hfrequency

local notation "Q" => assignedReferenceFamily P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

def assignedReferenceOriginalLabel (top : τ) (j : Fin N) (l : (Q top).labels j) : P.labels j :=
  ((P.assignedTopFamily packets assigned top).referenceOriginalLabel
    oldSlope (T top).slope (R top) cone w j l).val.2

local notation "orig" => assignedReferenceOriginalLabel P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

def assignedReferenceAlternate (top : τ) (j : Fin N) (l : (Q top).labels j)
    (u : P.AssignedTopItem packets assigned j l) (k : κ) : SchwartzMap (ℝ×ℝ) ℂ :=
  alt j (orig top j l) u.val k

local notation "alts" => assignedReferenceAlternate P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency alt

include hAlt in
theorem assignedReferenceAlternate_bound (top : τ) (j : Fin N) (l : (Q top).labels j)
    (u : P.AssignedTopItem packets assigned j l) (k : κ) :
    planarProfileConstant (alts top j l u k) (2*(Q top).order) ≤ (Q top).profileBound :=
  hAlt j (orig top j l) u.val k

local notation "halt" => assignedReferenceAlternate_bound P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency alt hAlt

variable (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)

def assignedReferenceSelector (top : τ) (j : Fin N) (l : (Q top).labels j) : κ → ℝ → ℂ :=
  b j (orig top j l)

local notation "selector" => assignedReferenceSelector P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency b

end LipschitzHilbert.PacketLatticeData

end

end OAI
