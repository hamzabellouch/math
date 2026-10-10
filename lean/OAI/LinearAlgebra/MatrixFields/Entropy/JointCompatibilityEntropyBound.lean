import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.JointCompatibilityIncidence

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open MatrixMultiplication.Foundation
open MatrixMultiplication.JointTypeCounts MatrixMultiplication.JointCompatibilityIncidence
open scoped BigOperators

namespace MatrixMultiplication.JointCompatibilityEntropyBound

attribute [local instance] Classical.propDecidable

section ClassCounts

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos A : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

def classEntropy (counts : ∀ c, A c → ℕ) : ℝ :=
  ∑ c, (Fintype.card (Pos c) : ℝ) *
    finiteEntropy (fun a => (counts c a : ℝ) / Fintype.card (Pos c))

def classTypeError : ℝ :=
  ∑ c, ((Fintype.card (A c) : ℝ) + 1) *
    (1 + Real.log (Fintype.card (Pos c) + 1 : ℕ))

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Pos c)] in
theorem fixedClassWords_size (counts : ∀ c, A c → ℕ)
    (w : FixedClassWords Pos A counts) (c : C) :
    Fintype.card (Pos c) = ∑ a, counts c a := by
  calc
    Fintype.card (Pos c) = ∑ a, wordPopulation (w c).val a :=
      (wordPopulation_sum (w c).val).symm
    _ = ∑ a, counts c a := Finset.sum_congr rfl fun a _ => (w c).property a

theorem abs_log_card_sub_classEntropy_le (counts : ∀ c, A c → ℕ)
    (w : FixedClassWords Pos A counts) :
    |Real.log (Fintype.card (FixedClassWords Pos A counts) : ℝ) -
      classEntropy Pos A counts| ≤ classTypeError Pos A := by
  have hsize := fixedClassWords_size Pos A counts w
  simpa only [classEntropy, classTypeError, ← hsize] using
    abs_log_fixedClassWords_card_sub_entropy_le Pos A counts hsize

theorem fixedClassWords_card_le_exp (counts : ∀ c, A c → ℕ)
    (w : FixedClassWords Pos A counts) :
    (Fintype.card (FixedClassWords Pos A counts) : ℝ) ≤
      Real.exp (classEntropy Pos A counts + classTypeError Pos A) := by
  have hpos : 0 < (Fintype.card (FixedClassWords Pos A counts) : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨w⟩)
  have h := (abs_le.mp (abs_log_card_sub_classEntropy_le Pos A counts w)).2
  calc
    (Fintype.card (FixedClassWords Pos A counts) : ℝ) =
      Real.exp (Real.log (Fintype.card (FixedClassWords Pos A counts) : ℝ)) :=
        (Real.exp_log hpos).symm
    _ ≤ Real.exp (classEntropy Pos A counts + classTypeError Pos A) :=
      Real.exp_le_exp.mpr (by linarith)

theorem exp_le_fixedClassWords_card (counts : ∀ c, A c → ℕ)
    (w : FixedClassWords Pos A counts) :
    Real.exp (classEntropy Pos A counts - classTypeError Pos A) ≤
      (Fintype.card (FixedClassWords Pos A counts) : ℝ) := by
  have hpos : 0 < (Fintype.card (FixedClassWords Pos A counts) : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨w⟩)
  have h := (abs_le.mp (abs_log_card_sub_classEntropy_le Pos A counts w)).1
  calc
    Real.exp (classEntropy Pos A counts - classTypeError Pos A) ≤
      Real.exp (Real.log (Fintype.card (FixedClassWords Pos A counts) : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = (Fintype.card (FixedClassWords Pos A counts) : ℝ) := Real.exp_log hpos

end ClassCounts

section GroupCounts

def wordTypeError (I A : Type*) [Fintype I] [Fintype A] : ℝ :=
  ((Fintype.card A : ℝ) + 1) * (1 + Real.log (Fintype.card I + 1 : ℕ)) +
    (Fintype.card A : ℝ) * Real.log (Fintype.card I + 1 : ℕ)

theorem wordEntropyBound_eq_exp (I A : Type*) [Fintype I] [Fintype A] (H : ℝ) :
    wordEntropyBound I A H =
      Real.exp ((Fintype.card I : ℝ) * H + wordTypeError I A) := by
  unfold wordEntropyBound wordTypeError
  rw [show (Fintype.card I : ℝ) * H +
      (((Fintype.card A : ℝ) + 1) * (1 + Real.log (Fintype.card I + 1 : ℕ)) +
        (Fintype.card A : ℝ) * Real.log (Fintype.card I + 1 : ℕ)) =
      (Fintype.card A : ℝ) * Real.log (Fintype.card I + 1 : ℕ) +
        ((Fintype.card I : ℝ) * H + ((Fintype.card A : ℝ) + 1) *
          (1 + Real.log (Fintype.card I + 1 : ℕ))) by ring]
  conv_rhs => rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity)]
  simp only [Nat.cast_add, Nat.cast_one]

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos Shape A : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable (counts : ∀ c, Shape c → ℕ)
  (designated : ∀ c, Shape c → Prop)
  (H : (Σ c, Option (Shape c)) → ℝ)
  (w : FixedClassWords Pos Shape counts)

def groupedEntropy : ℝ :=
  ∑ g : Σ c, Option (Shape c),
    (Fintype.card (GroupPos (w g.1).val (designated g.1) g.2) : ℝ) * H g

def groupedTypeError : ℝ :=
  ∑ g : Σ c, Option (Shape c),
    wordTypeError (GroupPos (w g.1).val (designated g.1) g.2) (A g.1)

omit [DecidableEq C] [∀ c, DecidableEq (Pos c)] [∀ c, DecidableEq (A c)] in
theorem prod_wordEntropyBound_eq_exp :
    (∏ g : Σ c, Option (Shape c), wordEntropyBound
      (GroupPos (w g.1).val (designated g.1) g.2) (A g.1) (H g)) =
      Real.exp (groupedEntropy Pos Shape counts designated H w +
        groupedTypeError Pos Shape A counts designated w) := by
  simp only [wordEntropyBound_eq_exp, groupedEntropy, groupedTypeError,
    ← Real.exp_sum, Finset.sum_add_distrib]

end GroupCounts

section Compatibility

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos Shape Pair Left Right : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
  [∀ c, Fintype (Left c)] [∀ c, DecidableEq (Left c)]
  [∀ c, Fintype (Right c)] [∀ c, DecidableEq (Right c)]
variable (shapeCounts : ∀ c, Shape c → ℕ) (pairCounts : ∀ c, Pair c → ℕ)
  (leftPart : ∀ c, Pair c → Left c) (rightPart : ∀ c, Pair c → Right c)
  (designatedLeft designatedRight : ∀ c, Shape c → Prop)
  (leftLaw : ∀ c, Shape c → Left c → ℝ)
  (rightLaw : ∀ c, Shape c → Right c → ℝ) (χ : ℝ)

def compatibilityExponent (HL HR : (Σ c, Option (Shape c)) → ℝ)
    (w : FixedClassWords Pos Shape shapeCounts) : ℝ :=
  classEntropy Pos Shape shapeCounts - classEntropy Pos Pair pairCounts +
    groupedEntropy Pos Shape shapeCounts designatedLeft HL w +
    groupedEntropy Pos Shape shapeCounts designatedRight HR w +
    classTypeError Pos Shape + classTypeError Pos Pair +
    groupedTypeError Pos Shape Left shapeCounts designatedLeft w +
    groupedTypeError Pos Shape Right shapeCounts designatedRight w

theorem compatibleCandidateCount_le_exp
    (w : FixedClassWords Pos Shape shapeCounts)
    (z : FixedClassWords Pos Pair pairCounts)
    (hpair : ∀ c, Function.Injective (fun s : Pair c => (leftPart c s, rightPart c s)))
    (HL HR : (Σ c, Option (Shape c)) → ℝ)
    (controlLeft : SideEntropyControl Pos Shape Pair Left shapeCounts pairCounts
      leftPart designatedLeft leftLaw χ HL w)
    (controlRight : SideEntropyControl Pos Shape Pair Right shapeCounts pairCounts
      rightPart designatedRight rightLaw χ HR w) :
    (compatibleCandidateCount Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) ≤
      Real.exp (compatibilityExponent Pos Shape Pair Left Right shapeCounts pairCounts
        designatedLeft designatedRight HL HR w) := by
  have h := compatibleCandidateCount_le_of_controls Pos Shape Pair Left Right
    shapeCounts pairCounts leftPart rightPart designatedLeft designatedRight
    leftLaw rightLaw χ w z hpair HL HR controlLeft controlRight
  rw [prod_wordEntropyBound_eq_exp, prod_wordEntropyBound_eq_exp] at h
  let E := groupedEntropy Pos Shape shapeCounts designatedLeft HL w +
    groupedTypeError Pos Shape Left shapeCounts designatedLeft w +
    (groupedEntropy Pos Shape shapeCounts designatedRight HR w +
      groupedTypeError Pos Shape Right shapeCounts designatedRight w)
  rw [← Real.exp_add] at h
  have hnum : (Fintype.card (FixedClassWords Pos Shape shapeCounts) : ℝ) * Real.exp E ≤
      Real.exp (classEntropy Pos Shape shapeCounts + classTypeError Pos Shape + E) := by
    conv_rhs => rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_right
      (fixedClassWords_card_le_exp Pos Shape shapeCounts w) (Real.exp_pos E).le
  calc
    (compatibleCandidateCount Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) ≤
        (Fintype.card (FixedClassWords Pos Shape shapeCounts) : ℝ) * Real.exp E /
          Fintype.card (FixedClassWords Pos Pair pairCounts) := h
    _ ≤ Real.exp (classEntropy Pos Shape shapeCounts + classTypeError Pos Shape + E) /
        Real.exp (classEntropy Pos Pair pairCounts - classTypeError Pos Pair) :=
      div_le_div₀ (Real.exp_pos _).le hnum (Real.exp_pos _)
        (exp_le_fixedClassWords_card Pos Pair pairCounts z)
    _ = Real.exp (compatibilityExponent Pos Shape Pair Left Right shapeCounts pairCounts
        designatedLeft designatedRight HL HR w) := by
      rw [← Real.exp_sub]
      congr 1
      dsimp [E, compatibilityExponent]
      ring

theorem log_compatibleCandidateCount_le
    (w : FixedClassWords Pos Shape shapeCounts)
    (z : FixedClassWords Pos Pair pairCounts)
    (hpair : ∀ c, Function.Injective (fun s : Pair c => (leftPart c s, rightPart c s)))
    (HL HR : (Σ c, Option (Shape c)) → ℝ)
    (controlLeft : SideEntropyControl Pos Shape Pair Left shapeCounts pairCounts
      leftPart designatedLeft leftLaw χ HL w)
    (controlRight : SideEntropyControl Pos Shape Pair Right shapeCounts pairCounts
      rightPart designatedRight rightLaw χ HR w)
    (hpos : 0 < compatibleCandidateCount Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z) :
    Real.log (compatibleCandidateCount Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) ≤
      compatibilityExponent Pos Shape Pair Left Right shapeCounts pairCounts
        designatedLeft designatedRight HL HR w := by
  have h := Real.log_le_log (Nat.cast_pos.mpr hpos)
    (compatibleCandidateCount_le_exp Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ
      w z hpair HL HR controlLeft controlRight)
  simpa only [Real.log_exp] using h

end Compatibility

end MatrixMultiplication.JointCompatibilityEntropyBound

end
end

end MatrixAllFields

end OAI
