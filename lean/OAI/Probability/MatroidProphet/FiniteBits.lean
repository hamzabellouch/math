import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

noncomputable def bitsWeight (q : α → ℝ) (V S : Finset α) : ℝ :=
  ∏ e ∈ V, if e ∈ S then q e else 1 - q e

noncomputable def bitsExpectation (q : α → ℝ) (V : Finset α)
    (f : Finset α → ℝ) : ℝ :=
  ∑ S ∈ V.powerset, bitsWeight q V S * f S

lemma bitsWeight_nonneg (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (V S : Finset α) : 0 ≤ bitsWeight q V S := by
  apply prod_nonneg
  intro e he
  split_ifs
  · exact hq0 e
  · exact sub_nonneg.2 (hq1 e)

lemma bitsWeight_insert_no (q : α → ℝ) (V S : Finset α) (e : α)
    (he : e ∉ V) (hS : S ⊆ V) :
    bitsWeight q (insert e V) S = (1 - q e) * bitsWeight q V S := by
  have heS : e ∉ S := fun h => he (hS h)
  simp [bitsWeight, he, heS]

lemma bitsWeight_insert_yes (q : α → ℝ) (V S : Finset α) (e : α)
    (he : e ∉ V) :
    bitsWeight q (insert e V) (insert e S) = q e * bitsWeight q V S := by
  simp only [bitsWeight, prod_insert he, mem_insert_self, ite_true]
  congr 1
  apply prod_congr rfl
  intro x hx
  have hxe : x ≠ e := fun h => he (h ▸ hx)
  simp [hxe]

lemma bitsExpectation_insert (q : α → ℝ) (V : Finset α) (e : α) (he : e ∉ V)
    (f : Finset α → ℝ) :
    bitsExpectation q (insert e V) f =
      (1 - q e) * bitsExpectation q V f +
        q e * bitsExpectation q V (fun S => f (insert e S)) := by
  unfold bitsExpectation
  rw [sum_powerset_insert he, mul_sum, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro S hS
    rw [bitsWeight_insert_no q V S e he (mem_powerset.1 hS)]
    ring
  · apply sum_congr rfl
    intro S hS
    rw [bitsWeight_insert_yes q V S e he]
    ring

@[simp] lemma bitsExpectation_empty (q : α → ℝ) (f : Finset α → ℝ) :
    bitsExpectation q ∅ f = f ∅ := by
  simp [bitsExpectation, bitsWeight]

@[simp] lemma bitsExpectation_one (q : α → ℝ) (V : Finset α) :
    bitsExpectation q V (fun _ => 1) = 1 := by
  induction V using Finset.induction_on with
  | empty => simp
  | @insert e V he ih =>
    rw [bitsExpectation_insert q V e he]
    simp only [ih]
    ring

lemma bitsExpectation_mono (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (V : Finset α) {f g : Finset α → ℝ} (h : ∀ S ⊆ V, f S ≤ g S) :
    bitsExpectation q V f ≤ bitsExpectation q V g := by
  apply sum_le_sum
  intro S hS
  exact mul_le_mul_of_nonneg_left (h S (mem_powerset.1 hS)) (bitsWeight_nonneg q hq0 hq1 V S)

lemma bitsExpectation_congr (q : α → ℝ) (V : Finset α)
    {f g : Finset α → ℝ} (h : ∀ S ⊆ V, f S = g S) :
    bitsExpectation q V f = bitsExpectation q V g := by
  apply sum_congr rfl
  intro S hS
  rw [h S (mem_powerset.1 hS)]

lemma bitsExpectation_add (q : α → ℝ) (V : Finset α) (f g : Finset α → ℝ) :
    bitsExpectation q V (fun S => f S + g S) =
      bitsExpectation q V f + bitsExpectation q V g := by
  simp only [bitsExpectation, mul_add, sum_add_distrib]

lemma bitsExpectation_const (q : α → ℝ) (V : Finset α) (c : ℝ) :
    bitsExpectation q V (fun _ => c) = c := by
  have h := bitsExpectation_one q V
  simp only [bitsExpectation, mul_one] at h
  simp only [bitsExpectation, ← sum_mul, h, one_mul]

lemma bitsExpectation_nonneg (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (V : Finset α) {f : Finset α → ℝ} (h : ∀ S ⊆ V, 0 ≤ f S) :
    0 ≤ bitsExpectation q V f := by
  apply sum_nonneg
  intro S hS
  exact mul_nonneg (bitsWeight_nonneg q hq0 hq1 V S) (h S (mem_powerset.1 hS))

noncomputable def bitsFailure (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) (V I : Finset α) : ℝ :=
  bitsExpectation q V (fun S => if cert (I ∪ S) then 0 else 1)

lemma bitsFailure_nonneg (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (V I : Finset α) : 0 ≤ bitsFailure cert q V I := by
  apply bitsExpectation_nonneg q hq0 hq1
  intro S hS
  split_ifs <;> norm_num

lemma bitsFailure_le_one (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (V I : Finset α) : bitsFailure cert q V I ≤ 1 := by
  rw [← bitsExpectation_one q V]
  apply bitsExpectation_mono q hq0 hq1
  intro S hS
  split_ifs <;> norm_num

lemma bitsFailure_forced_antitone (cert : Finset α → Prop) [DecidablePred cert]
    (hcert : Monotone cert) (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (V : Finset α) {I J : Finset α} (hIJ : I ⊆ J) :
    bitsFailure cert q V J ≤ bitsFailure cert q V I := by
  apply bitsExpectation_mono q hq0 hq1
  intro S hS
  have himp : cert (I ∪ S) → cert (J ∪ S) := hcert (union_subset_union hIJ Subset.rfl)
  by_cases hi : cert (I ∪ S)
  · simp [hi, himp hi]
  · split_ifs <;> norm_num

lemma bitsFailure_certifies (cert : Finset α → Prop) [DecidablePred cert]
    (hcert : Monotone cert) (q : α → ℝ) (V I : Finset α) (hI : cert I) :
    bitsFailure cert q V I = 0 := by
  unfold bitsFailure bitsExpectation
  apply sum_eq_zero
  intro S hS
  have hIS : cert (I ∪ S) := hcert subset_union_left hI
  simp [hIS]

lemma bitsFailure_insert (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) (V I : Finset α) (e : α) (he : e ∉ V) :
    bitsFailure cert q (insert e V) I =
      (1 - q e) * bitsFailure cert q V I + q e * bitsFailure cert q V (insert e I) := by
  unfold bitsFailure
  rw [bitsExpectation_insert q V e he]
  congr 2
  apply bitsExpectation_congr
  intro S hS
  simp only [union_insert, insert_union]

lemma bitsFailure_split (cert : Finset α → Prop) [DecidablePred cert]
    (q : α → ℝ) (V I : Finset α) (e : α) (he : e ∈ V) :
    bitsFailure cert q V I = (1 - q e) * bitsFailure cert q (V.erase e) I +
      q e * bitsFailure cert q (V.erase e) (insert e I) := by
  have h := bitsFailure_insert cert q (V.erase e) I e (notMem_erase e V)
  simpa only [insert_erase he] using h

lemma bitsFailure_antitone (cert : Finset α → Prop) [DecidablePred cert]
    (hcert : Monotone cert) (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (I : Finset α) : Antitone (fun V => bitsFailure cert q V I) := by
  apply Finset.antitone_iff_forall_insert_le.2
  intro V e he
  rw [bitsFailure_insert cert q V I e he]
  have h := bitsFailure_forced_antitone cert hcert q hq0 hq1 V (subset_insert e I)
  have hmul := mul_le_mul_of_nonneg_left h (hq0 e)
  nlinarith

end MatroidProphet

end OAI
