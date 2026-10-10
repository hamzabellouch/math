import OAI.Algebra.DepthFive.BidegreeShiftedOccupation
import OAI.Algebra.DepthFive.InvalidOccupation

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335
namespace LocalMoments

open ShiftedOccupation

/-- The explicit path amplitude on the canonical fixed-bidegree source indices. -/
def sourcePathAmplitude {ι σ : Type*} [Fintype ι]
    {side : ι → Bool} {a b : ℕ} (M : BidegreeSource (σ := σ) side a b)
    (p : ι → σ) : ℝ :=
  ∏ t : ι, coefficient (side t) (M.1 (t, p t))

lemma sourceIndex_shiftRelation {ι σ : Type*} [Fintype ι] [Fintype σ]
    [DecidableEq σ] {side : ι → Bool} {a b : ℕ}
    (M : BidegreeSource (σ := σ) side a b) (p q : ι → σ)
    (h : ∀ x, 0 ≤ signedSource M.1 (operatorSign ∘ side) p q x) (t : ι) :
    ShiftRelation (side t) (fun x => M.1 (t, x))
      (fun x => (sourceIndex M (operatorSign ∘ side) p q h).1 (t, x)) (p t) (q t) := by
  intro x
  change (source M.1 (operatorSign ∘ side) p q (t, x) : ℤ) = _
  rw [source_cast M.1 (operatorSign ∘ side) p q h]
  simp only [signedSource, operatorSign, Function.comp_apply, Finsupp.sub_apply,
    Finsupp.single_apply]
  congr 2
  simp only [eq_comm]

/-- The complete zero-extension bridge required by the eliminated-source second trace.
Valid shifts remain in the fixed bidegree domain; invalid shifts give zero on both sides. -/
theorem extended_four_path_product_eq {ι σ : Type*} [Fintype ι] [Fintype σ]
    [DecidableEq σ] {side : ι → Bool} {a b : ℕ}
    (M : BidegreeSource (σ := σ) side a b) (p q r s : ι → σ)
    (hmatch : ∀ t, Finsupp.single (p t) (1 : ℤ) - Finsupp.single (q t) 1 =
      Finsupp.single (r t) 1 - Finsupp.single (s t) 1) :
    sourcePathAmplitude M p *
      Function.extend sourceEmbedding (fun N : BidegreeSource (σ := σ) side a b => sourcePathAmplitude N q) (fun _ => 0)
        (signedSource M.1 (operatorSign ∘ side) p q) *
      sourcePathAmplitude M r *
      Function.extend sourceEmbedding (fun N : BidegreeSource (σ := σ) side a b => sourcePathAmplitude N s) (fun _ => 0)
        (signedSource M.1 (operatorSign ∘ side) p q) =
      ∏ t : ι, localPolynomial (side t) (fun x => M.1 (t, x)) (p t) (q t) (r t) := by
  classical
  by_cases h : ∀ x, 0 ≤ signedSource M.1 (operatorSign ∘ side) p q x
  · rw [extend_source_valid M (operatorSign ∘ side) p q h,
      extend_source_valid M (operatorSign ∘ side) p q h]
    unfold sourcePathAmplitude
    apply four_path_products_eq_localPolynomial_product Finset.univ side
      (fun t x => M.1 (t, x))
      (fun t x => (sourceIndex M (operatorSign ∘ side) p q h).1 (t, x)) p q r s
    · intro t ht
      exact hmatch t
    · intro t ht
      exact sourceIndex_shiftRelation M p q h t
  · rw [extend_source_invalid M (operatorSign ∘ side) p q h,
      mul_zero, zero_mul, zero_mul]
    symm
    apply localPolynomial_product_zero_of_no_source side M.1 p q r
    rw [ShiftedOccupation.exists_source_iff]
    exact h

end LocalMoments
end Problem335

end

end OAI
