import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Order.Filter.AtTopBot.Basic
import OAI.Combinatorics.BalancedRyser.Construction.Construction

namespace OAI

namespace Balanced.Local

open scoped BigOperators
open Filter

universe u

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev TupleCode (F : Type u) := (Fin 4 → Direction F) × (Fin 4 → Bool)

abbrev ChoiceCode (F : Type u) := Line F × TupleCode F
abbrev Output (F : Type u) := Slot F → ChoiceCode F

def decodeTuple {F : Type u} (t : TupleCode F) : FourTuple F := ⟨t.1, t.2⟩
def decodeChoice {F : Type u} (c : ChoiceCode F) : SplitChoice F :=
  ⟨c.1, decodeTuple c.2⟩
def configuration {F : Type u} (M : MergedPairs F) (v : Output F) : Configuration F :=
  ⟨M, fun s => decodeChoice (v s)⟩

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

def constituentMultiplicity (M : MergedPairs F) (p : Point F) : ℕ :=
  (Finset.univ.filter (fun ds : Direction F × Bool =>
    OnLine p (constituent M ds.1 ds.2))).card

def logBudget (F : Type u) [Fintype F] : ℕ := Nat.ceil (Real.log (Fintype.card F))

def offsetProbability (E : MergedPairs F → Prop) : ℝ :=
  (∑ M : MergedPairs F, if E M then (1 : ℝ) else 0) /
    Fintype.card (MergedPairs F)

def conditionedOffsetProbability (A E : MergedPairs F → Prop) : ℝ :=
  offsetProbability (fun M => A M ∧ E M) / offsetProbability A

structure RetentionRule (F : Type u) [Field F] [Fintype F] [DecidableEq F] where
  candidates : MergedPairs F → Direction F → Finset (ChoiceCode F)
  valid : ∀ M g c, c ∈ candidates M g → ValidChoice M g (decodeChoice c)
  uniqueLine : ∀ M g c d, c ∈ candidates M g → d ∈ candidates M g →
    c.1 = d.1 → c = d
  complete : ∀ M g c, ValidChoice M g (decodeChoice c) →
    ∃ d ∈ candidates M g, d.1 = c.1

abbrev Kernel (F : Type u) := MergedPairs F → Output F → ℝ

def KernelConditions (Q : RetentionRule F) (w : Kernel F) (K : ℝ) : Prop :=
  (∀ M v, 0 ≤ w M v) ∧
  (∀ M, ∑ v, w M v ≤ 1) ∧
  (∀ M v, 0 < w M v →
    (configuration M v).Valid ∧ (configuration M v).Compatible ∧
    (∀ s, v s ∈ Q.candidates M s.1) ∧
    (∀ p, constituentMultiplicity M p ≤ logBudget F)) ∧
  (∀ M (S : Finset (Slot F)) (t : Slot F → TupleCode F),
    (∑ v, if (∀ s ∈ S, (v s).2 = t s) then w M v else 0) ≤
      (K / Fintype.card F) ^ S.card)

def selectedProbability (w : Kernel F) (E : Configuration F → Prop) : ℝ :=
  (∑ M : MergedPairs F, ∑ v : Output F,
    if E (configuration M v) then w M v else 0) /
      Fintype.card (MergedPairs F)

def generatorUnionAt (C : Configuration F) (p : Point F) : Finset (Direction F) :=
  (Finset.univ.filter (fun s => OnLine p (C.choice s).line)).biUnion
    (fun s => generatorSet (C.choice s).tuple)

def reuseCount (C : Configuration F) (p : Point F) : ℕ :=
  4 * C.splitMultiplicity p - (generatorUnionAt C p).card

structure EqualityPattern (b κ : ℕ) where
  classOf : Fin b → Fin 4 → Fin (4 * b - κ)
  everyClass : Function.Surjective (fun ij : Fin b × Fin 4 => classOf ij.1 ij.2)
  withinTuple : ∀ i, Function.Injective (classOf i)
  pairOverlap : ∀ i j, i ≠ j →
    ((Finset.univ.image (classOf i)) ∩ (Finset.univ.image (classOf j))).card ≤ 1

abbrev DirectionAssignment (F : Type u) (b κ : ℕ) :=
  (Fin b → Direction F) × (Fin (4 * b - κ) → Direction F)
abbrev Bits (b : ℕ) := Fin b → Fin 4 → Bool

def Eligible {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) : Prop :=
  Function.Injective a.1 ∧ Function.Injective a.2 ∧
    ∀ i j, a.2 (P.classOf i j) ≠ a.1 i

def prescribedTuple {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (i : Fin b) : FourTuple F :=
  ⟨fun j => a.2 (P.classOf i j), bits i⟩

def prescribedPoint {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b)
    (M : MergedPairs F) (ij : Fin b × Fin 4) : Point F :=
  tuplePoint M (prescribedTuple P a bits ij.1) ij.2

def Aligned {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) : Prop :=
  ∀ ij, OnLine (prescribedPoint P a bits M ij) (lineThrough (a.1 ij.1) p)

def Admissible {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) : Prop :=
  Aligned P a bits p M ∧ Function.Injective (prescribedPoint P a bits M) ∧
    (∀ ij, prescribedPoint P a bits M ij ≠ p) ∧
    (∀ i, lineThrough (a.1 i) p ∉ constituentLines M) ∧
    (∀ x, constituentMultiplicity M x ≤ logBudget F)

def prescribedDesignated {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (M : MergedPairs F) :
    Finset (Point F) := Finset.univ.image (prescribedPoint P a bits M)

def prescribedPartners {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) : Finset (Point F) :=
  (prescribedDesignated P a bits M).filter (fun x =>
    ∃ ds : Direction F × Bool, OnLine p (constituent M ds.1 ds.2) ∧
      OnLine x (constituent M ds.1 (!ds.2)))

def piecePoints (M : MergedPairs F) : LocalPiece F → Finset (Point F)
  | Sum.inl U => U
  | Sum.inr (Sum.inl l) => linePoints l
  | Sum.inr (Sum.inr d) => mergedPoints M d

def AllowedPiece {b κ : ℕ} (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) : LocalPiece F → Prop
  | Sum.inl U => U.card ≤ 2
  | Sum.inr (Sum.inl l) =>
      l ∉ (Finset.univ.image (fun i => lineThrough (a.1 i) p)) ∪ constituentLines M
  | Sum.inr (Sum.inr _) => True

def BadCover {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) : Prop :=
  ∃ A : Finset (LocalPiece F), A.card ≤ b - 1 ∧
    (∀ x ∈ A, AllowedPiece a p M x) ∧
    prescribedDesignated P a bits M ⊆
      prescribedPartners P a bits p M ∪ A.biUnion (piecePoints M)

def AdmissibleBadCover {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) : Prop :=
  Admissible P a bits p M ∧ BadCover P a bits p M

def PencilLocalResult : Prop :=
  ∀ K : ℝ, 0 < K → ∃ ε : ℕ → ℝ,
    Tendsto ε atTop (nhds 0) ∧ (∀ q, 0 ≤ ε q) ∧
    ∃ q₀ : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      q₀ ≤ Fintype.card F → ∀ (Q : RetentionRule F) (w : Kernel F),
      KernelConditions Q w K →
      selectedProbability w (fun C => ¬ C.LocalCondition) ≤ ε (Fintype.card F)

def PencilReuseResult : Prop :=
  ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
    ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      q₀ ≤ Fintype.card F → ∀ (Q : RetentionRule F) (w : Kernel F),
      KernelConditions Q w K → ∀ p : Point F,
      selectedProbability w (fun X => 2 ≤ X.splitMultiplicity p ∧ 3 ≤ reuseCount X p) ≤
        C / (Fintype.card F : ℝ) ^ 3

def AlignmentNormalizationResult : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
    ∀ b κ : ℕ, 3 ≤ b → b ≤ logBudget F → κ ≤ 2 →
    ∀ (P : EqualityPattern b κ) (a : DirectionAssignment F b κ), Eligible P a →
    ∀ (bits : Bits b) (p : Point F),
      offsetProbability (Aligned P a bits p) = 1 / (Fintype.card F : ℝ) ^ (4 * b)

def PencilSmallReuseResult : Prop :=
  AlignmentNormalizationResult.{u} ∧
  ∃ C : ℝ, 0 < C ∧ ∃ d q₀ : ℕ,
    ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      q₀ ≤ Fintype.card F → ∀ b κ : ℕ, 3 ≤ b → b ≤ logBudget F → κ ≤ 1 →
      ∀ (P : EqualityPattern b κ) (a : DirectionAssignment F b κ), Eligible P a →
      ∀ (bits : Bits b) (p : Point F),
      conditionedOffsetProbability (Aligned P a bits p) (AdmissibleBadCover P a bits p) ≤
        C * (b : ℝ) ^ d * (2 * (logBudget F : ℝ) / Fintype.card F) ^ (3 - κ)

def PencilTwoReusesResult : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
    ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      q₀ ≤ Fintype.card F → ∀ b : ℕ, 3 ≤ b → b ≤ logBudget F →
      ∀ (P : EqualityPattern b 2) (bits : Bits b) (p : Point F),
      (∑ a : DirectionAssignment F b 2,
        if Eligible P a then offsetProbability (fun M =>
          Aligned P a bits p M ∧ AdmissibleBadCover P a bits p M) else 0) ≤
        ((Fintype.card F + 1 : ℕ) : ℝ) ^ (5 * b - 2) /
          (Fintype.card F : ℝ) ^ (4 * b) * (C * (b : ℝ) ^ 3 / Fintype.card F)

end
end Balanced.Local

end OAI
