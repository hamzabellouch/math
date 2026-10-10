import OAI.Algebra.DepthFive.FactorialPositive
import OAI.Algebra.DepthFive.OccupationExpansion

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

variable {σ : Type*} [Fintype σ]

/-- Reassemble two occupation vectors on the complementary variable classes. -/
def joinOccupation (side : σ → Bool)
    (M : {i // side i = true} → ℕ) (N : {i // ¬ side i = true} → ℕ) : σ → ℕ :=
  fun i => if h : side i = true then M ⟨i, h⟩ else N ⟨i, h⟩

omit [Fintype σ] in
@[simp] theorem joinOccupation_true (side : σ → Bool)
    (M : {i // side i = true} → ℕ) (N : {i // ¬ side i = true} → ℕ)
    (i : {i // side i = true}) : joinOccupation side M N i = M i := by
  simp [joinOccupation, i.property]

omit [Fintype σ] in
@[simp] theorem joinOccupation_false (side : σ → Bool)
    (M : {i // side i = true} → ℕ) (N : {i // ¬ side i = true} → ℕ)
    (i : {i // ¬ side i = true}) : joinOccupation side M N i = N i := by
  simp [joinOccupation, i.property]

theorem factorialMonomial_joinOccupation (side : σ → Bool) (d : σ → ℕ)
    (M : {i // side i = true} → ℕ) (N : {i // ¬ side i = true} → ℕ) :
    factorialMonomial d (joinOccupation side M N) =
      (∏ i, (M i).descFactorial (d i)) * (∏ i, (N i).descFactorial (d i)) := by
  classical
  unfold factorialMonomial
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => side i = true)]
  simp

variable [DecidableEq σ]

/-- The actual finite uniform average, not an assumed moment functional. -/
def partitionCompositionMean (side : σ → Bool) (f : (σ → ℕ) → ℝ) (a b : ℕ) : ℝ := by
  classical
  exact (∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset {i // side i = true}) a,
    (∑ N ∈ Finset.finsuppAntidiag (Finset.univ : Finset {i // ¬ side i = true}) b,
      f (joinOccupation side M N)) /
      (Finset.finsuppAntidiag (Finset.univ : Finset {i // ¬ side i = true}) b).card) /
    (Finset.finsuppAntidiag (Finset.univ : Finset {i // side i = true}) a).card

namespace FactorialExpansion
variable {f : (σ → ℕ) → ℕ} {S : Finset σ} {D : ℕ}

theorem partitionCompositionMean_eq (F : FactorialExpansion f S D)
    (side : σ → Bool) (a b : ℕ) :
    Problem335.partitionCompositionMean side (fun M => (f M : ℝ)) a b =
      twoGroupCompositionExpansionMean Finset.univ (fun j => (F.coeff j : ℝ))
        (fun j (i : {i // side i = true}) => F.degree j i)
        (fun j (i : {i // ¬ side i = true}) => F.degree j i) a b := by
  classical
  unfold Problem335.partitionCompositionMean twoGroupCompositionExpansionMean
    compositionExpansionMean factorialExpansionValue
  apply congrArg (fun x : ℝ => x / _)
  apply Finset.sum_congr rfl
  intro M hM
  apply congrArg (fun x : ℝ => x / _)
  apply Finset.sum_congr rfl
  intro N hN
  dsimp only
  rw [F.eval_real]
  apply Finset.sum_congr rfl
  intro j hj
  rw [factorialMonomial_joinOccupation]
  push_cast
  ring

omit [DecidableEq σ] in
/-- The two means give one coordinate-wise geometric factorial monomial. -/
theorem partition_geometric_monomial (side : σ → Bool) (d : σ → ℕ) (A B : ℝ) :
    (∏ i, (d i).factorial * (if side i = true then A else B) ^ d i : ℝ) =
      (∏ i : {i // side i = true}, ((d i).factorial : ℝ)) *
      (∏ i : {i // ¬ side i = true}, ((d i).factorial : ℝ)) *
      (A ^ (∑ i : {i // side i = true}, d i) *
       B ^ (∑ i : {i // ¬ side i = true}, d i)) := by
  classical
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => side i = true)]
  have hV (i : {i // side i = true}) : (if side i = true then A else B) = A :=
    ite_eq_left i.property
  have hU (i : {i // ¬ side i = true}) : (if side i = true then A else B) = B :=
    ite_eq_right i.property
  simp_rw [hV, hU]
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

/-- Upper occupation comparison for every concrete nonnegative factorial expansion.
No total-order restriction is necessary for this upper bound. -/
theorem partitionCompositionMean_le (F : FactorialExpansion f S D)
    (side : σ → Bool) [Nonempty {i // side i = true}] [Nonempty {i // ¬ side i = true}]
    (a b : ℕ) :
    Problem335.partitionCompositionMean side (fun M => (f M : ℝ)) a b ≤
      ∑ j, (F.coeff j : ℝ) * ∏ i, ((F.degree j i).factorial : ℝ) *
        (if side i = true then (a : ℝ) / Fintype.card {i // side i = true}
         else (b : ℝ) / Fintype.card {i // ¬ side i = true}) ^ F.degree j i := by
  classical
  rw [F.partitionCompositionMean_eq]
  have h := twoGroupCompositionExpansionMean_le_geometric Finset.univ
    (fun j => (F.coeff j : ℝ))
    (fun j (i : {i // side i = true}) => F.degree j i)
    (fun j (i : {i // ¬ side i = true}) => F.degree j i) a b
    (by intro j hj; positivity)
  refine h.trans_eq ?_
  unfold twoGroupGeometricExpansionValue
  apply Finset.sum_congr rfl
  intro j hj
  rw [partition_geometric_monomial]
  ring

end FactorialExpansion
end Problem335

end

end OAI
