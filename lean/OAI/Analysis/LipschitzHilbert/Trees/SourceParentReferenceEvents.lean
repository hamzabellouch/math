import OAI.Analysis.LipschitzHilbert.Trees.SourcePolynomialSelectedGoodPath
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceSelectorGeometry

namespace OAI

/-! Reference events at the path-top slope keep the original packets and
selectors. The angular mesh is w/topLength, independently of the exponent
used in the path weights. One parent event and all continuing-shift events
form a single finite, phase-independent union. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
namespace SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
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

end SourceLabeledLattice

section Union
variable {ι : Type*} {N K : ℕ} {κ : Type} {Label : Fin N → Type}
  {Item : ∀ j, Label j → Type} [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- `none` denotes the parent square; `some shift` denotes its continuing path. -/
def parentShiftReferenceData
    (parent : ι → PhysicalReferenceData N κ Label Item)
    (child : ι → Fin K → PhysicalReferenceData N κ Label Item)
    (t : ι) : Option (Fin K) → PhysicalReferenceData N κ Label Item
  | none => parent t
  | some shift => child t shift

def parentShiftReferenceSelection
    (parent : ι → PhysicalReferenceData N κ Label Item)
    (child : ι → Fin K → PhysicalReferenceData N κ Label Item)
    (parentSelected : ∀ t, Finset (parent t).family.PacketIndex)
    (childSelected : ∀ t i, Finset (child t i).family.PacketIndex)
    (t : ι) : ∀ i, Finset (parentShiftReferenceData parent child t i).family.PacketIndex
  | none => parentSelected t
  | some shift => childSelected t shift

/-- The common union is literal, with no dependence on an imaginary phase. -/
def parentShiftReferenceBad
    (parent : ι → PhysicalReferenceData N κ Label Item)
    (child : ι → Fin K → PhysicalReferenceData N κ Label Item)
    (parentSelected : ∀ t, Finset (parent t).family.PacketIndex)
    (childSelected : ∀ t i, Finset (child t i).family.PacketIndex)
    (L A e s r : ℝ) (t : ι) : Set (ℝ×ℝ) :=
  ((parent t).restrictPackets (parentSelected t)).bad L A e s r ∪
    ⋃ i, ((child t i).restrictPackets (childSelected t i)).bad L A e s r

theorem parentShiftReferenceBad_eq_union
    (parent : ι → PhysicalReferenceData N κ Label Item)
    (child : ι → Fin K → PhysicalReferenceData N κ Label Item)
    (parentSelected : ∀ t, Finset (parent t).family.PacketIndex)
    (childSelected : ∀ t i, Finset (child t i).family.PacketIndex)
    (L A e s r : ℝ) (t : ι) :
    parentShiftReferenceBad parent child parentSelected childSelected L A e s r t =
      ⋃ i ∈ (Finset.univ : Finset (Option (Fin K))),
        ((parentShiftReferenceData parent child t i).restrictPackets
          (parentShiftReferenceSelection parent child parentSelected childSelected t i)).bad
          L A e s r := by
  ext z
  simp only [parentShiftReferenceBad,mem_union,mem_iUnion,exists_prop,Finset.mem_univ,true_and]
  constructor
  · rintro (hp|⟨i,hi⟩)
    · exact ⟨none,hp⟩
    · exact ⟨some i,hi⟩
  · rintro ⟨i,hi⟩
    cases i with
    | none => exact Or.inl hi
    | some i => exact Or.inr ⟨i,hi⟩

theorem parentShiftReferenceBad_measurable
    (parent : ι → PhysicalReferenceData N κ Label Item)
    (child : ι → Fin K → PhysicalReferenceData N κ Label Item)
    (parentSelected : ∀ t, Finset (parent t).family.PacketIndex)
    (childSelected : ∀ t i, Finset (child t i).family.PacketIndex)
    (L A e s r : ℝ) (t : ι) :
    MeasurableSet (parentShiftReferenceBad parent child parentSelected childSelected L A e s r t) :=
  (((parent t).restrictPackets (parentSelected t)).bad_measurable L A e s r).union
    (MeasurableSet.iUnion fun i =>
      ((child t i).restrictPackets (childSelected t i)).bad_measurable L A e s r)

theorem parentShiftReferenceBad_compl
    (parent : ι → PhysicalReferenceData N κ Label Item)
    (child : ι → Fin K → PhysicalReferenceData N κ Label Item)
    (parentSelected : ∀ t, Finset (parent t).family.PacketIndex)
    (childSelected : ∀ t i, Finset (child t i).family.PacketIndex)
    (L A e s r : ℝ) (t : ι) (z : ℝ×ℝ)
    (hz : z ∉ parentShiftReferenceBad parent child parentSelected childSelected L A e s r t) :
    z ∉ ((parent t).restrictPackets (parentSelected t)).bad L A e s r ∧
      ∀ i, z ∉ ((child t i).restrictPackets (childSelected t i)).bad L A e s r := by
  constructor
  · exact fun hm => hz (Or.inl hm)
  · exact fun i hm => hz (Or.inr (mem_iUnion.mpr ⟨i,hm⟩))

theorem parentShiftReference_card_le (L : ℝ) (hL : 2 ≤ L) (hK : (K:ℝ) ≤ L^2) :
    ((Finset.univ : Finset (Option (Fin K))).card:ℝ) ≤ L^3 := by
  simp only [Finset.card_univ,Fintype.card_option,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
  nlinarith [sq_nonneg L]

end Union
end LipschitzHilbert

end

end OAI
