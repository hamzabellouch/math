import OAI.Combinatorics.ProgressionColoring.ComparisonOutputs
import OAI.Combinatorics.ProgressionColoring.LabelIncidences
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fin.VecNotation

namespace OAI

universe uLabel uk uOtherLabel

namespace QuantitativeVanDerWaerden

/-- Literal half-open cells on a single fundamental interval. A centered
partition is represented by translating both its endpoints by `1/2`. -/
structure CirclePartition (Label : Type uLabel) where
  left : Label → ℝ
  right : Label → ℝ
  left_nonneg : ∀ l, 0 ≤ left l
  left_lt_right : ∀ l, left l < right l
  right_le_one : ∀ l, right l ≤ 1
  covers : ∀ x ∈ Set.Ico (0 : ℝ) 1, ∃! l, x ∈ Set.Ico (left l) (right l)

namespace CirclePartition

noncomputable section

variable {Label : Type uLabel} (P : CirclePartition Label)

def label (x : ℝ) : Label :=
  Classical.choose ((P.covers (Int.fract x)
    ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩).exists)

theorem label_mem (x : ℝ) :
    Int.fract x ∈ Set.Ico (P.left (P.label x)) (P.right (P.label x)) :=
  Classical.choose_spec ((P.covers (Int.fract x)
    ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩).exists)

theorem label_eq_iff (x : ℝ) (l : Label) :
    P.label x = l ↔ Int.fract x ∈ Set.Ico (P.left l) (P.right l) := by
  constructor
  · rintro rfl
    exact P.label_mem x
  · intro h
    exact (P.covers (Int.fract x)
      ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩).unique (P.label_mem x) h

theorem label_eq_of_mem (x : ℝ) (l : Label)
    (h : Int.fract x ∈ Set.Ico (P.left l) (P.right l)) : P.label x = l :=
  (P.label_eq_iff x l).mpr h

theorem label_eq_of_fract_eq {x y : ℝ} (h : Int.fract x = Int.fract y) :
    P.label x = P.label y := by
  apply P.label_eq_of_mem
  rw [h]
  exact P.label_mem y

theorem label_eq_of_sub_int {x y : ℝ} (z : ℤ) (h : x - y = (z : ℝ)) :
    P.label x = P.label y :=
  P.label_eq_of_fract_eq (Int.fract_eq_fract.mpr ⟨z, h⟩)

theorem label_add_int (x : ℝ) (z : ℤ) : P.label (x + z) = P.label x :=
  P.label_eq_of_fract_eq (Int.fract_add_intCast x z)

theorem label_sub_int (x : ℝ) (z : ℤ) : P.label (x - z) = P.label x :=
  P.label_eq_of_fract_eq (Int.fract_sub_intCast x z)

/-- Membership in one lifted half-open interval already determines the
periodic label; the integer part need not be known in advance. -/
theorem label_eq_of_lifted_mem (x : ℝ) (z : ℤ) (l : Label)
    (hleft : P.left l + z ≤ x) (hright : x < P.right l + z) :
    P.label x = l := by
  have hzero : 0 ≤ x - z := by linarith [P.left_nonneg l]
  have hone : x - z < 1 := by linarith [P.right_le_one l]
  have hfract : Int.fract x = x - z :=
    Int.fract_eq_iff.mpr ⟨hzero, hone, z, by ring⟩
  apply P.label_eq_of_mem
  rw [hfract]
  constructor <;> linarith

def word (k : ℕ) (a b : ℝ) : Fin k → Label :=
  fun j => P.label (a + (j : ℝ) * b)

theorem word_fract_parameters (k : ℕ) (a b : ℝ) :
    P.word k a b = P.word k (Int.fract a) (Int.fract b) := by
  funext j
  apply P.label_eq_of_sub_int (⌊a⌋ + (j.val : ℤ) * ⌊b⌋)
  simp only [Int.fract, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  ring

/-- Start and step representatives of the global counting argument. -/
def parameterDomain : Set (Fin 2 → ℝ) :=
  {x | x 0 ∈ Set.Ico (0 : ℝ) 1 ∧ x 1 ∈ Set.Ico (0 : ℝ) 1}

def affinePoint {k : ℕ} (j : Fin k) (x : Fin 2 → ℝ) : ℝ :=
  x 0 + (j : ℝ) * x 1

theorem affinePoint_mem {k : ℕ} (j : Fin k) {x : Fin 2 → ℝ}
    (hx : x ∈ parameterDomain) : affinePoint j x ∈ Set.Ico (0 : ℝ) k := by
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  have hjk : (j : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_iff.mpr j.isLt
  have hprod : (j : ℝ) * x 1 ≤ j := by
    simpa using mul_le_mul_of_nonneg_left hx.2.2.le hj
  constructor
  · exact add_nonneg hx.1.1 (mul_nonneg hj hx.2.1)
  · dsimp [affinePoint]
    linarith [hx.1.2]

/-- Position, literal label, choice of endpoint, and integer translate. -/
abbrev ComparisonIndex (k : ℕ) (Label : Type uk) := Fin k × Label × Bool × Fin k

def endpoint (l : Label) (upper : Bool) : ℝ :=
  if upper then P.right l else P.left l

def comparison {k : ℕ} (i : ComparisonIndex k Label) : AffineForm 2 where
  linear := ![1, (i.1 : ℝ)]
  constant := -(P.endpoint i.2.1 i.2.2.1 + (i.2.2.2 : ℝ))

theorem comparison_eval {k : ℕ} (i : ComparisonIndex k Label) (x : Fin 2 → ℝ) :
    (P.comparison i).eval x =
      affinePoint i.1 x - (P.endpoint i.2.1 i.2.2.1 + (i.2.2.2 : ℝ)) := by
  simp [comparison, AffineForm.eval, affinePoint, Fin.sum_univ_two]
  ring

variable [Fintype Label]

def comparisons (k : ℕ) : Fin (Fintype.card (ComparisonIndex k Label)) → AffineForm 2 :=
  fun i => P.comparison ((Fintype.equivFin (ComparisonIndex k Label)).symm i)

theorem comparison_count (k : ℕ) :
    Fintype.card (ComparisonIndex k Label) = 2 * k ^ 2 * Fintype.card Label := by
  simp only [ComparisonIndex, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

theorem word_eq_of_signVector_eq {k : ℕ} {x y : Fin 2 → ℝ}
    (hx : x ∈ parameterDomain) (_hy : y ∈ parameterDomain)
    (hs : signVector (P.comparisons k) x = signVector (P.comparisons k) y) :
    P.word k (x 0) (x 1) = P.word k (y 0) (y 1) := by
  classical
  have hsign (i : ComparisonIndex k Label) :
      ternarySign ((P.comparison i).eval x) =
        ternarySign ((P.comparison i).eval y) := by
    have h := congrFun hs ((Fintype.equivFin (ComparisonIndex k Label)) i)
    simpa only [signVector, comparisons, Equiv.symm_apply_apply] using h
  funext j
  let t := affinePoint j x
  have ht := affinePoint_mem j hx
  have hz0 : (0 : ℤ) ≤ ⌊t⌋ := Int.floor_nonneg.mpr ht.1
  have hzk : ⌊t⌋ < (k : ℤ) := Int.floor_lt.mpr (by exact_mod_cast ht.2)
  let z : Fin k := ⟨⌊t⌋.toNat, by omega⟩
  have hzcast : (z : ℝ) = (⌊t⌋ : ℝ) := by
    dsimp [z]
    exact_mod_cast Int.toNat_of_nonneg hz0
  let l := P.label t
  have hcell := P.label_mem t
  change P.left l ≤ t - (⌊t⌋ : ℝ) ∧ t - (⌊t⌋ : ℝ) < P.right l at hcell
  have hl : 0 ≤ t - (P.left l + (z : ℝ)) := by
    rw [hzcast]
    linarith [hcell.1]
  have hr : t - (P.right l + (z : ℝ)) < 0 := by
    rw [hzcast]
    linarith [hcell.2]
  have hleft := hsign (j, l, false, z)
  have hright := hsign (j, l, true, z)
  simp only [comparison_eval, endpoint, Bool.false_eq_true, ite_false, ite_true] at hleft hright
  have hyl : 0 ≤ affinePoint j y - (P.left l + (z : ℝ)) := by
    apply le_of_not_gt
    intro hyneg
    have hzero := (ternarySign_eq_zero _).mpr hyneg
    rw [← hleft] at hzero
    exact (not_lt_of_ge hl) ((ternarySign_eq_zero _).mp hzero)
  have hyr : affinePoint j y - (P.right l + (z : ℝ)) < 0 := by
    apply (ternarySign_eq_zero _).mp
    rw [← hright]
    exact (ternarySign_eq_zero _).mpr hr
  have hylabel : P.label (affinePoint j y) = l :=
    P.label_eq_of_lifted_mem (affinePoint j y) (z.val : ℤ) l
      (by simpa only [Int.cast_natCast] using
        (show P.left l + (z : ℝ) ≤ affinePoint j y by linarith))
      (by simpa only [Int.cast_natCast] using
        (show affinePoint j y < P.right l + (z : ℝ) by linarith))
  exact hylabel.symm

/-- The finite scalar-word family is derived from actual affine comparisons.
The equivalence characterizes its exact image on normalized parameters. -/
theorem exists_exact_word_family (k : ℕ) :
    ∃ S : Finset (Fin k → Label),
      (∀ w, w ∈ S ↔ ∃ x ∈ parameterDomain, P.word k (x 0) (x 1) = w) ∧
      S.card ≤ 16 * (3 * k ^ 2 * Fintype.card Label + 1) ^ 6 := by
  obtain ⟨S, hS, hcard⟩ := finite_outputs_of_comparisons (P.comparisons k)
    parameterDomain (fun x => P.word k (x 0) (x 1))
    (fun _ hx _ hy hs => P.word_eq_of_signVector_eq hx hy hs)
  refine ⟨S, hS, ?_⟩
  have hcount : Fintype.card (ComparisonIndex k Label) ≤
      3 * k ^ 2 * Fintype.card Label := by
    rw [comparison_count]
    nlinarith
  calc
    S.card ≤ 16 * (Fintype.card (ComparisonIndex k Label) + 1) ^ 6 := by
      simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reducePow] using hcard
    _ ≤ 16 * (3 * k ^ 2 * Fintype.card Label + 1) ^ 6 :=
      Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right hcount 1) 6)

/-- Every real start and step belongs to the same counted family, by genuine
integer-periodicity of the literal interval labels. -/
theorem exists_word_family (k : ℕ) :
    ∃ S : Finset (Fin k → Label), (∀ a b : ℝ, P.word k a b ∈ S) ∧
      S.card ≤ 16 * (3 * k ^ 2 * Fintype.card Label + 1) ^ 6 := by
  obtain ⟨S, hS, hcard⟩ := P.exists_exact_word_family k
  refine ⟨S, ?_, hcard⟩
  intro a b
  rw [P.word_fract_parameters]
  apply (hS _).mpr
  refine ⟨![Int.fract a, Int.fract b], ?_, rfl⟩
  exact ⟨⟨Int.fract_nonneg a, Int.fract_lt_one a⟩,
    ⟨Int.fract_nonneg b, Int.fract_lt_one b⟩⟩

variable {OtherLabel : Type uOtherLabel} [Fintype OtherLabel]

/-- The actual full label word of two independent `D`-coordinate progressions. -/
def fullWord (Q : CirclePartition OtherLabel) (D k : ℕ)
    (firstStart firstStep secondStart secondStep : Fin D → ℝ) :
    Fin k → FullLabel D Label OtherLabel := fun j =>
  (fun i => P.word k (firstStart i) (firstStep i) j,
   fun i => Q.word k (secondStart i) (secondStep i) j)

/-- Global full words have a finite cover derived from their actual scalar
interval labels. The common endpoint budget is the sum of the two mesh sizes.
The argument does not require or assume independence of actual cyclic orbit
coordinates: counting all independent real starts and steps gives a cover. -/
theorem exists_fullWord_family (Q : CirclePartition OtherLabel) (D k : ℕ) :
    ∃ S : Finset (Fin k → FullLabel D Label OtherLabel),
      (∀ a b c d : Fin D → ℝ, P.fullWord Q D k a b c d ∈ S) ∧
      S.card ≤ (16 *
        (3 * k ^ 2 * (Fintype.card Label + Fintype.card OtherLabel) + 1) ^ 6) ^
          (2 * D) := by
  classical
  obtain ⟨first, hfirst, hfirstcard⟩ := P.exists_word_family k
  obtain ⟨second, hsecond, hsecondcard⟩ := Q.exists_word_family k
  let decode : ((Fin D → Fin k → Label) × (Fin D → Fin k → OtherLabel)) →
      (Fin k → FullLabel D Label OtherLabel) :=
    fun p j => (fun i => p.1 i j, fun i => p.2 i j)
  let S := ((coordinateFamily (fun _ : Fin D => first)).product
    (coordinateFamily (fun _ : Fin D => second))).image decode
  refine ⟨S, ?_, ?_⟩
  · intro a b c d
    apply Finset.mem_image.mpr
    refine ⟨(fun i => P.word k (a i) (b i), fun i => Q.word k (c i) (d i)),
      Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Fintype.mem_piFinset.mpr (fun i => hfirst (a i) (b i))
    · exact Fintype.mem_piFinset.mpr (fun i => hsecond (c i) (d i))
  · apply card_decoded_twoSystems_le
    · intro _
      exact hfirstcard.trans (Nat.mul_le_mul_left 16
        (Nat.pow_le_pow_left (Nat.add_le_add_right
          (Nat.mul_le_mul_left (3 * k ^ 2) (Nat.le_add_right _ _)) 1) 6))
    · intro _
      exact hsecondcard.trans (Nat.mul_le_mul_left 16
        (Nat.pow_le_pow_left (Nat.add_le_add_right
          (Nat.mul_le_mul_left (3 * k ^ 2) (Nat.le_add_left _ _)) 1) 6))

end
end CirclePartition

end QuantitativeVanDerWaerden

end OAI
