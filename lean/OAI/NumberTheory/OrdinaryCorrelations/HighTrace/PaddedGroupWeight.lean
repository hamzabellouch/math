import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Support

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.TaggedPrimeGroups
open Finset Classical
variable {P Q : Type*}

def paddedGroupWeight (W : P → ℝ) : Option P → ℝ
  | none => 1
  | some p => W p

def paddedShapeWeight (U : P → Q → ℝ) : Option P → Option Q → ℝ
  | none,none => 1
  | some p,some q => U p q
  | _,_ => 0

lemma paddedGroupWeight_nonneg (W : P → ℝ) (hW : ∀ p, 0 ≤ W p) (p : Option P) :
    0 ≤ paddedGroupWeight W p := by cases p <;> simp [paddedGroupWeight,hW]

lemma paddedShapeWeight_nonneg (U : P → Q → ℝ) (hU : ∀ p q, 0 ≤ U p q)
    (p : Option P) (q : Option Q) : 0 ≤ paddedShapeWeight U p q := by
  cases p <;> cases q <;> simp [paddedShapeWeight,hU]

variable [Fintype Q]

lemma paddedShapeSum (U : P → Q → ℝ) (A : ℝ)
    (hA : 1 ≤ A) (hU : ∀ p, ∑ q, U p q ≤ A) (p : Option P) :
    (∑ q : Option Q, paddedShapeWeight U p q) ≤ A := by
  rw [Fintype.sum_option]
  cases p <;> simp only [paddedShapeWeight,sum_const_zero,add_zero,zero_add]
  · exact hA
  · exact hU _

lemma padded_shape_tuple_sum (U : P → Q → ℝ) (A : ℝ) (hA : 1 ≤ A)
    (hU : ∀ p q, 0 ≤ U p q) (hSum : ∀ p, ∑ q, U p q ≤ A)
    (n : ℕ) (x : Fin n → Option P) :
    (∑ y : Fin n → Option Q, ∏ i, paddedShapeWeight U (x i) (y i)) ≤ A^n := by
  rw [← Fintype.prod_sum]
  calc
    _ ≤ ∏ _i : Fin n, A := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact sum_nonneg (fun q hq => paddedShapeWeight_nonneg U hU _ _)
      · exact fun i hi => paddedShapeSum U A hA hSum _
    _ = _ := by simp

variable [Fintype P] [DecidableEq P]

theorem weighted_tagged_slot_sum (W : P → ℝ) (hW : ∀ p, 0 ≤ W p)
    (U : P → Q → ℝ) (hU : ∀ p q, 0 ≤ U p q) (A : ℝ) (hA : 1 ≤ A)
    (hSum : ∀ p, ∑ q, U p q ≤ A) (m n : ℕ) (pick : Fin n → Fin m) :
    (∑ x : Fin m → Option P, ∑ y : Fin n → Option Q,
      weight (paddedGroupWeight W) x * ∏ i, paddedShapeWeight U (x (pick i)) (y i)) ≤
      (∏ i ∈ range m, ((i : ℝ)+1+∑ p : P, W p)) * A^n := by
  have hw : ∀ x : Fin m → Option P, 0 ≤ weight (paddedGroupWeight W) x :=
    fun x => weight_nonneg _ (paddedGroupWeight_nonneg W hW) x
  calc
    _ = ∑ x : Fin m → Option P,
        weight (paddedGroupWeight W) x *
          ∑ y : Fin n → Option Q, ∏ i, paddedShapeWeight U (x (pick i)) (y i) := by
      simp only [mul_sum]
    _ ≤ ∑ x : Fin m → Option P, weight (paddedGroupWeight W) x * A^n := by
      exact sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left
        (padded_shape_tuple_sum U A hA hU hSum n (fun i => x (pick i))) (hw x))
    _ = (∑ x : Fin m → Option P, weight (paddedGroupWeight W) x) * A^n := (sum_mul ..).symm
    _ ≤ (∏ i ∈ range m, ((i:ℝ)+∑ p : Option P, paddedGroupWeight W p)) * A^n :=
      mul_le_mul_of_nonneg_right (grouped_prime_sum _ (paddedGroupWeight_nonneg W hW) m)
        (pow_nonneg (by linarith) n)
    _ = _ := by
      rw [Fintype.sum_option]
      simp only [paddedGroupWeight,add_assoc]

end OrdinaryCorrelations.TaggedPrimeGroups

end

end OAI
