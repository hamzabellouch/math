import OAI.Analysis.KadisonKastler.CompleteCorrectionLimit

namespace OAI

/-! # Uniform complete bounds on the successive correction products -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def correctionProducts (S : ℕ → A →L[ℂ] A) : ℕ → A →L[ℂ] A
  | 0 => ContinuousLinearMap.id ℂ A
  | n + 1 => (S n).comp (correctionProducts S n)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem correctionProducts_zero (S : ℕ → A →L[ℂ] A) :
    correctionProducts S 0 = ContinuousLinearMap.id ℂ A := rfl

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem correctionProducts_succ (S : ℕ → A →L[ℂ] A) (n : ℕ) :
    correctionProducts S (n + 1) = (S n).comp (correctionProducts S n) := rfl

omit [PartialOrder A] [StarOrderedRing A] in
theorem correctionProducts_increment (S : ℕ → A →L[ℂ] A) (n : ℕ) :
    (correctionProducts S (n + 1)).toLinearMap - (correctionProducts S n).toLinearMap =
      ((S n).toLinearMap - LinearMap.id).comp (correctionProducts S n).toLinearMap := by
  ext x
  simp

/-- The displacement is bounded by twice the sum of the step sizes. The
hypothesis on the partial sums closes the simultaneous bound by two. -/
theorem correctionProducts_complete_bounds (S : ℕ → A →L[ℂ] A) (r : ℕ → ℝ)
    (hr : ∀ n, 0 ≤ r n)
    (hsmall : ∀ n, 2 * ∑ i ∈ Finset.range n, r i ≤ 1)
    (hS : ∀ n, CompletelyBoundedBy ((S n).toLinearMap - LinearMap.id) (r n))
    (n : ℕ) :
    CompletelyBoundedBy ((correctionProducts S n).toLinearMap - LinearMap.id)
      (2 * ∑ i ∈ Finset.range n, r i) ∧
    CompletelyBoundedBy (correctionProducts S n).toLinearMap 2 := by
  induction n with
  | zero =>
    constructor
    · intro p q X
      simp only [correctionProducts_zero, ContinuousLinearMap.coe_id, sub_self,
        matrix_map_zero, Finset.range_zero, Finset.sum_empty, mul_zero, zero_mul, norm_zero, le_refl]
    · exact (completelyBoundedBy_id (A := A)).mono (by norm_num)
  | succ n ih =>
    have hdifference : CompletelyBoundedBy
        ((correctionProducts S (n + 1)).toLinearMap -
          (correctionProducts S n).toLinearMap) (2 * r n) := by
      rw [correctionProducts_increment]
      convert (hS n).comp ih.2 (hr n) using 1
      ring
    have heq : (correctionProducts S (n + 1)).toLinearMap - LinearMap.id =
        ((correctionProducts S (n + 1)).toLinearMap -
          (correctionProducts S n).toLinearMap) +
        ((correctionProducts S n).toLinearMap - LinearMap.id) := by abel
    have hdisplacement : CompletelyBoundedBy
        ((correctionProducts S (n + 1)).toLinearMap - LinearMap.id)
        (2 * ∑ i ∈ Finset.range (n + 1), r i) := by
      rw [heq]
      convert hdifference.add ih.1 using 1
      rw [Finset.sum_range_succ]
      ring
    refine ⟨hdisplacement, ?_⟩
    have heq' : (correctionProducts S (n + 1)).toLinearMap =
        LinearMap.id + ((correctionProducts S (n + 1)).toLinearMap - LinearMap.id) := by abel
    rw [heq']
    exact ((completelyBoundedBy_id (A := A)).add hdisplacement).mono (by linarith [hsmall (n+1)])

omit [PartialOrder A] [StarOrderedRing A] in
/-- The products preserve the involution if each factor does. -/
theorem correctionProducts_star (S : ℕ → A →L[ℂ] A)
    (hS : ∀ n x, S n (star x) = star (S n x)) (n : ℕ) (x : A) :
    correctionProducts S n (star x) = star (correctionProducts S n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change S n (correctionProducts S n (star x)) = star (S n (correctionProducts S n x))
    rw [ih, hS]

end

end KadisonKastler

end OAI
