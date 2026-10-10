import Mathlib
import OAI.Combinatorics.KMedian.Probability.BernoulliBatches
import OAI.Combinatorics.KMedian.Probability.FiniteVariance
import OAI.Combinatorics.KMedian.Sparse.SparseRealLaw
import OAI.Combinatorics.KMedian.Probability.BernoulliSquare

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n : ℕ}

theorem product_indicator (q : Fin n → Bool) (S : Finset (Fin n)) :
    (∏ i∈S, flag q i)=(if ∀ i∈S, q i=true then (1:ℚ) else 0) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [prod_insert hi,ih]
    simp only [mem_insert,forall_eq_or_imp]
    cases hq : q i <;> simp [flag,hq]

noncomputable def reference (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    FiniteLaw (Fin n → Bool) :=
  FiniteLaw.bernoulli (fun i => (p i:ℝ))
    (fun i => by exact_mod_cast (hp i).1) (fun i => by exact_mod_cast (hp i).2)

theorem reference_subset (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset (Fin n)) :
    (reference p hp).expect (fun q => ((∏ i∈S,flag q i:ℚ):ℝ))=((∏ i∈S,p i:ℚ):ℝ) := by
  simp_rw [product_indicator]
  simp only [apply_ite,Rat.cast_one,Rat.cast_zero]
  change (reference p hp).prob (fun q => ∀ i∈S, q i=true)=_
  have hh := FiniteLaw.bernoulli_cylinder (fun i => (p i:ℝ))
      (fun i => by exact_mod_cast (hp i).1) (fun i => by exact_mod_cast (hp i).2) S (fun _ => true)
  simp only [FiniteLaw.coinWeight_true] at hh
  rw [Rat.cast_prod]
  apply Eq.trans ?_ hh
  unfold reference FiniteLaw.prob FiniteLaw.expect
  apply sum_congr rfl
  intro q _
  by_cases hq : ∀ i∈S, q i=true
  · simp only [ite_eq_left hq]
  · simp only [ite_eq_right hq]

theorem real_subset {d : ℕ} (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset (Fin n)) (hS : S.card ≤ d) :
    (run (d := d) p hp n).real.expect (fun q => ((∏ i∈S,flag q i:ℚ):ℝ))=
      (reference p hp).expect (fun q => ((∏ i∈S,flag q i:ℚ):ℝ)) := by
  rw [SparseIntegerLaw.real_expect,subset_moment p hp S hS,reference_subset]

theorem reference_polynomial {m : ℕ} (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Fin m → Finset (Fin n)) (c : Fin m → ℚ) :
    (reference p hp).expect (fun q => (polynomial S c q:ℝ))=
      ((∑ j, c j*∏ i∈S j,p i:ℚ):ℝ) := by
  simp only [polynomial,Rat.cast_sum,Rat.cast_mul,FiniteLaw.expect_sum,
    FiniteLaw.expect_mul,reference_subset]

theorem real_polynomial {d m : ℕ} (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (hS : ∀ j, (S j).card ≤ d) :
    (run (d := d) p hp n).real.expect (fun q => (polynomial S c q:ℝ))=
      (reference p hp).expect (fun q => (polynomial S c q:ℝ)) := by
  rw [SparseIntegerLaw.real_expect,polynomial_moment p hp S c hS,reference_polynomial]

theorem quadratic_variance {m : ℕ} (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (hS : ∀ j, (S j).card ≤ 2) :
    (run (d := 4) p hp n).real.variance (fun q => (polynomial S c q:ℝ))=
      (reference p hp).variance (fun q => (polynomial S c q:ℝ)) := by
  have he := real_polynomial (d := 4) p hp S c (fun j => (hS j).trans (by omega))
  have hsq : (fun q => (polynomial S c q:ℝ)^2)=
      (fun q => (polynomial (pairSet S) (pairCoefficient c) q:ℝ)) := by
    funext q
    rw [← Rat.cast_pow,polynomial_square]
  rw [FiniteLaw.variance_eq,FiniteLaw.variance_eq,he,hsq,
    real_polynomial p hp (pairSet S) (pairCoefficient c) (pairSet_card S hS)]

end MetricKMedian.SparseBernoulli

end OAI
