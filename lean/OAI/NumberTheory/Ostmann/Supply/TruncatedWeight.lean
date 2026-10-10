import OAI.NumberTheory.Ostmann.Supply.PolynomialFunctional

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators
open TensorOperators BivariateTruncation

variable {ι : Type*}

def truncatedSubsetSum {R : Type*} [CommSemiring R] (P : Finset ι) (b : ι→R) (K : ℕ) : R :=
  ∑s∈P.powerset.filter (fun s => s.card≤K),∏i∈s,b i

def truncatedWeight (P : Finset ι) (b : ι→ℝ) (K : ℕ) : ℝ :=
  (truncatedSubsetSum P b K)^2

theorem truncatedWeight_nonneg (P : Finset ι) (b : ι→ℝ) (K : ℕ) :
    0≤truncatedWeight P b K := sq_nonneg _

def subsetPairPolynomial (P : Finset ι) (b : ι→ℂ) : (ℕ×ℕ)→₀ℂ :=
  ∑s∈P.powerset,∑t∈P.powerset,
    Finsupp.single (s.card,t.card) ((∏i∈s,b i)*(∏i∈t,b i))

theorem eval_subsetPairPolynomial (P : Finset ι) (b : ι→ℂ) (u v : ℂ) :
    eval (subsetPairPolynomial P b) u v = ∏i∈P,(1+u*b i)*(1+v*b i) := by
  classical
  simp only [subsetPairPolynomial,eval_sum,eval_single,smul_eq_mul]
  rw [Finset.prod_mul_distrib,Finset.prod_one_add,Finset.prod_one_add,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Finset.prod_mul_distrib,Finset.prod_const]
  ring

theorem rectangularTruncation_subsetPairPolynomial (P : Finset ι) (b : ι→ℂ) (K : ℕ) :
    rectangularTruncation (subsetPairPolynomial P b) K = (truncatedSubsetSum P b K)^2 := by
  classical
  simp only [subsetPairPolynomial,rectangularTruncation_sum,rectangularTruncation_single,
    truncatedSubsetSum,Finset.sum_filter,pow_two,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hsK : s.card≤K <;> by_cases htK : t.card≤K <;> simp [hsK,htK,mul_comm]

theorem rectangularTruncation_real_subsetPairPolynomial (P : Finset ι) (b : ι→ℝ) (K : ℕ) :
    rectangularTruncation (subsetPairPolynomial P (fun i => (b i:ℂ))) K =
      (truncatedWeight P b K:ℂ) := by
  rw [rectangularTruncation_subsetPairPolynomial]
  simp [truncatedWeight,truncatedSubsetSum]

theorem rectangularTruncation_eq_weight {c : (ℕ×ℕ)→₀ℂ} (P : Finset ι) (b : ι→ℝ)
    (h : ∀u v : ℂ,eval c u v=∏i∈P,(1+u*(b i:ℂ))*(1+v*(b i:ℂ))) (K : ℕ) :
    rectangularTruncation c K=(truncatedWeight P b K:ℂ) := by
  have he : c=subsetPairPolynomial P (fun i => (b i:ℂ)) :=
    eq_of_eval_eq (fun u v => (h u v).trans (eval_subsetPairPolynomial P _ u v).symm)
  rw [he,rectangularTruncation_real_subsetPairPolynomial]

end Ostmann.Supply

end

end OAI
