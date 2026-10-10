import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import OAI.Combinatorics.BalancedRyser.Deletion.Deletion

namespace OAI

noncomputable section
open Filter Finset MeasureTheory
open scoped Topology NNReal

namespace Balanced
open scoped _root_.Balanced

abbrev Profile := ℕ × ℕ → ℝ

def IsBoundedProfile (M : ℝ) (p : Profile) : Prop :=
  (∀ ij, 0 ≤ p ij) ∧ HasSum p 1 ∧
  Summable (fun ij => ((ij.1 + ij.2 : ℕ) : ℝ) * p ij) ∧
  (∑' ij, ((ij.1 + ij.2 : ℕ) : ℝ) * p ij) ≤ M

def deletionInvisible (P x : Profile) : Prop :=
  ∀ i j, x (i, j) = if i = 0 then 0 else P (i - 1, j)

def coverInvisible (P x : Profile) : Prop :=
  ∀ i j, x (i, j) = if j = 0 then 0 else P (i, j - 1)

def deletionVisible (P : Profile) : Set Profile := {x | ¬ deletionInvisible P x}
def coverVisible (P : Profile) : Set Profile := {x | ¬ coverInvisible P x}

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def lineMultiplicity (C : Finset (Line F)) (x : Point F) : ℕ :=
  (C.filter (fun l => OnLine x l)).card

def planeProfile (D C : Finset (Line F)) : Profile := fun ij =>
  ((Finset.univ.filter (fun x : Point F =>
    lineMultiplicity D x = ij.1 ∧ lineMultiplicity C x = ij.2)).card : ℝ) /
      (Fintype.card F : ℝ) ^ 2

def lineProfile (D C : Finset (Line F)) (l : Line F) : Profile := fun ij =>
  (((linePoints l).filter (fun x =>
    lineMultiplicity D x = ij.1 ∧ lineMultiplicity C x = ij.2)).card : ℝ) /
      (Fintype.card F : ℝ)

def profileDirac (p : Profile) : FiniteMeasure Profile :=
  ⟨Measure.dirac p, inferInstance⟩

def empiricalProfileMeasure (D C E : Finset (Line F)) : FiniteMeasure Profile := by
  let a : ℝ≥0 := ⟨(Fintype.card F : ℝ)⁻¹, by positivity⟩
  let ν : FiniteMeasure Profile := ∑ l ∈ E, profileDirac (lineProfile D C l)
  exact a • ν

def IsProfilePair (k : ℕ) (D C : Finset (Line F)) : Prop :=
  IsDeletionSet k D ∧ Disjoint D C ∧ C.card ≤ Fintype.card F

universe u

abbrev ProfileClass :=
  ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
    Finset (Line F) → Finset (Line F) → Prop

def ProfileClassValid (k : ℕ) (A : ProfileClass.{u}) : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
    (D C : Finset (Line F)), A F D C → IsProfilePair k D C

def ProfileClassSizeGap (a : ℝ) (A : ProfileClass.{u}) : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
    (D C : Finset (Line F)), A F D C →
      C.card = 0 ∨ a * (Fintype.card F : ℝ) ≤ (C.card : ℝ)

def ProfileSequenceLimit
    {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (D C : ∀ n, Finset (Line (F n)))
    (c : ℝ) (P : Profile) (νD νC : FiniteMeasure Profile) : Prop :=
  Tendsto (fun n => ((C n).card : ℝ) / (Fintype.card (F n) : ℝ)) atTop (𝓝 c) ∧
  Tendsto (fun n => planeProfile (D n) (C n)) atTop (𝓝 P) ∧
  Tendsto (fun n => empiricalProfileMeasure (D n) (C n) (D n)) atTop (𝓝 νD) ∧
  Tendsto (fun n => empiricalProfileMeasure (D n) (C n) (C n)) atTop (𝓝 νC)

def ProfileVisibleExcess (A : ProfileClass.{u}) : Prop :=
  ∀ (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (D C : ∀ n, Finset (Line (F n))),
    (∀ n, A (F n) (D n) (C n)) →
    Tendsto (fun n => Fintype.card (F n)) atTop atTop →
    ∀ (c : ℝ) (P : Profile) (νD νC : FiniteMeasure Profile),
      ProfileSequenceLimit D C c P νD νC →
      c < (νD : Measure Profile).real (deletionVisible P) +
        (νC : Measure Profile).real (coverVisible P)

def uniformProfileWitnessProbability (k : ℕ) (A : ProfileClass.{u})
    (F : Type u) [Field F] [Fintype F] [DecidableEq F] : ℝ := by
  classical
  exact ((Finset.univ.filter (fun D : DeletionSet F k =>
    ∃ C : Finset (Line F), A F D.val C)).card : ℝ) /
      (Fintype.card (DeletionSet F k) : ℝ)

def ProfileCountingResult : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ A : ProfileClass.{u},
    ProfileClassValid k A →
    (∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A) →
    ProfileVisibleExcess A →
    ∃ b : ℝ, 0 < b ∧ ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        N ≤ Fintype.card F → k ≤ Fintype.card F →
        uniformProfileWitnessProbability k A F ≤
          Real.exp (-b * (Fintype.card F : ℝ) * Real.log (Fintype.card F : ℝ))

end Balanced

end

end OAI
