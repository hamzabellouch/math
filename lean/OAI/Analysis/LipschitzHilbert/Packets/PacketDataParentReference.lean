import OAI.Analysis.LipschitzHilbert.Trees.SourceParentReferenceEvents
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataReferenceProperties

namespace OAI

/-! The actual data at a selected reference uses only its local cone. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)
  (packetTop : ∀ j (l : P.labels j), Item j l → SlopeBox)

/-- Literal recentering of original physical reference data. -/
abbrev recenteredReferenceData : PhysicalReferenceData N κ Label Item where
  family := P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
  alternate := fun j l => alt j (P.referenceOriginalLabel oldSlope newSlope R cone w j l)
  alternate_bound := fun j l => hAlt j (P.referenceOriginalLabel oldSlope newSlope R cone w j l)
  slope := newSlope
  angle := w/P.topLength
  selector := fun j l => b j (P.referenceOriginalLabel oldSlope newSlope R cone w j l)
  direction := v
  test := f
  packetTop := fun j l => packetTop j (P.referenceOriginalLabel oldSlope newSlope R cone w j l)

/-- Original packet indices are selected through the exact reference-label map. -/
def recenteredReferenceSelection (S : Finset P.PacketIndex) :
    Finset (P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency).PacketIndex :=
  Finset.univ.filter (fun u =>
    (⟨u.1,⟨P.referenceOriginalLabel oldSlope newSlope R cone w u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S)

@[simp] theorem recenteredReferenceData_slope :
    (P.recenteredReferenceData alt hAlt oldSlope newSlope R cone w F hw hcone hF hwide
      hfrequency b v f packetTop).slope = newSlope := rfl

@[simp] theorem recenteredReferenceData_angle :
    (P.recenteredReferenceData alt hAlt oldSlope newSlope R cone w F hw hcone hF hwide
      hfrequency b v f packetTop).angle = w/P.topLength := rfl

theorem recenteredReferenceData_short (j : Fin N)
    (l : (P.recenteredReferenceData alt hAlt oldSlope newSlope R cone w F hw hcone hF hwide
      hfrequency b v f packetTop).family.labels j) :
    (P.recenteredReferenceData alt hAlt oldSlope newSlope R cone w F hw hcone hF hwide
      hfrequency b v f packetTop).family.length j ≤ R :=
  (P.referenceLabel_bounds oldSlope newSlope R cone w j l).1

theorem recenteredReferenceData_bad (S : Finset P.PacketIndex) (L A e s r : ℝ) :
    let Q := P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel oldSlope newSlope R cone w
    let selected := P.recenteredReferenceSelection oldSlope newSlope R cone w F
      hw hcone hF hwide hfrequency S
    ((P.recenteredReferenceData alt hAlt oldSlope newSlope R cone w F hw hcone hF hwide
      hfrequency b v f packetTop).restrictPackets selected).bad L A e s r =
      (Q.restrictPackets selected).physicalReferenceBad
        (Q.restrictedAlternate (fun j l => alt j (orig j l)) selected)
        (Q.restrictedAlternate_bound (fun j l => alt j (orig j l))
          (fun j l => hAlt j (orig j l)) selected)
        newSlope (w/P.topLength) (fun j l => b j (orig j l)) v f
        (fun j l u => packetTop j (orig j l) u.val) L A e s r := rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
