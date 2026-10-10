import OAI.Probability.SignedSweeps.KernelTransition

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma proper_endpointKernel_annihilates {d : ℕ} (lam : Partition (2 ^ d))
    (A : Finset (OffFirstRow lam)) (hA : A ≠ Finset.univ) (v : Specht lam) :
    kernelOperator (subsetEndpointKernel d A) (tupleRealization lam v) = 0 := by
  let e : A ↪ OffFirstRow lam := Function.Embedding.subtype _
  let K := fun (x : InjectiveTuple (OffFirstRow lam) (2 ^ d)) (z : InjectiveTuple A (2 ^ d)) =>
    ((2 ^ d : ℕ) ^ Fintype.card (OffFirstRow lam) : ℝ)⁻¹ *
      ((2 ^ d : ℕ) ^ A.card * finiteProb (fun p : PhysicalSettings d =>
        ∀ a : A, sampleSweep d (physicalSettingsEquiv d p) (x a.1) = z a))
  have hcard : Fintype.card A < 2 ^ d - lam.1.rowLen 0 := by
    rw [Fintype.card_coe, ← card_offFirstRow]
    exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hA)
  have hK : subsetEndpointKernel d A = fun x y => K x (e.trans y) := by
    funext x y
    unfold subsetEndpointKernel normalizedEndpointProb sweepEndpointProb K
    congr 2
    apply finiteProb_congr
    intro p
    exact ⟨fun h a => h a.1 a.2, fun h a ha => h ⟨a,ha⟩⟩
  rw [hK]
  exact specht_marginal_kernel_eq_zero lam e hcard K v

lemma differenceKernel_apply_eq_sum {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    (K : Finset I → X → X → ℝ) (f : EuclideanSpace ℂ X) :
    kernelOperator (differenceKernel K) f = ∑ A : Finset I,
      (((-1 : ℝ) ^ Fintype.card I * (-1) ^ A.card : ℝ) : ℂ) • kernelOperator (K A) f := by
  apply PiLp.ext
  intro x
  simp only [kernelOperator_apply, differenceKernel, Complex.ofReal_mul, Complex.ofReal_sum,
    Finset.mul_sum, Finset.sum_mul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro y _
  ring

def maskedEndpointKernel {I : Type*} [Fintype I] [DecidableEq I] (d : ℕ) (A : Finset I)
    (x y : InjectiveTuple I (2 ^ d)) : ℝ :=
  if NoIsolatedVertex (endpointEncounter d x y) Finset.univ then subsetEndpointKernel d A x y else 0

lemma maskedEndpointKernel_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (d : ℕ) (A : Finset I) (x y : InjectiveTuple I (2 ^ d)) :
    0 ≤ maskedEndpointKernel d A x y := by
  unfold maskedEndpointKernel
  split_ifs
  · exact subsetEndpointKernel_nonneg d A x y
  · exact le_rfl

lemma differenceKernel_masked {I : Type*} [Fintype I] [DecidableEq I] (d : ℕ) :
    differenceKernel (maskedEndpointKernel (I := I) d) = differenceKernel (subsetEndpointKernel d) := by
  funext x y
  by_cases h : NoIsolatedVertex (endpointEncounter d x y) Finset.univ
  · simp only [differenceKernel, maskedEndpointKernel, ite_eq_left h]
  · have hx : ∃ a, ∀ b, ¬ (endpointEncounter d x y).Adj a b := by
      simpa only [NoIsolatedVertex, Finset.mem_univ, true_and, forall_true_left,
        not_forall, not_exists] using h
    obtain ⟨a,ha⟩ := hx
    rw [sweep_differenceKernel_vanishes_of_isolate d x y a ha]
    simp only [differenceKernel, maskedEndpointKernel, ite_eq_right h, mul_zero, Finset.sum_const_zero]

theorem sweep_norm_le_of_masked_rows {d : ℕ} (lam : Partition (2 ^ d))
    {p : ℝ} (hp : 0 ≤ p)
    (hrow : ∀ A : Finset (OffFirstRow lam), ∀ x : InjectiveTuple (OffFirstRow lam) (2 ^ d),
      (∑ z, ∑ y, maskedEndpointKernel d A x y * maskedEndpointKernel d A z y) ≤ p) :
    ‖(sweepOperator lam).toContinuousLinearMap‖ ≤
      2 ^ (2 ^ d - lam.1.rowLen 0) * Real.sqrt p := by
  apply sweep_norm_le_of_adjoint_tuple_bound lam (by positivity)
  intro v
  rw [tupleSweep_adjoint_eq_endpointKernel,
    ← differenceKernel_action (subsetEndpointKernel d) _ (fun A hA => proper_endpointKernel_annihilates lam A hA v),
    ← differenceKernel_masked d, differenceKernel_apply_eq_sum]
  have hn (A : Finset (OffFirstRow lam)) :
      ‖(kernelOperator (maskedEndpointKernel d A)).toContinuousLinearMap‖ ≤ Real.sqrt p := by
    have hs := nonnegative_kernel_opNorm_sq_le (maskedEndpointKernel d A)
      (maskedEndpointKernel_nonneg d A) hp (hrow A)
    nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg p, norm_nonneg (kernelOperator (maskedEndpointKernel d A)).toContinuousLinearMap]
  calc
    _ ≤ ∑ A : Finset (OffFirstRow lam),
        ‖((((-1 : ℝ) ^ Fintype.card (OffFirstRow lam) * (-1) ^ A.card : ℝ) : ℂ) •
          kernelOperator (maskedEndpointKernel d A) (tupleRealization lam v))‖ := norm_sum_le _ _
    _ = ∑ A : Finset (OffFirstRow lam), ‖kernelOperator (maskedEndpointKernel d A) (tupleRealization lam v)‖ := by
      apply Finset.sum_congr rfl
      intro A _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_pow]
      norm_num
    _ ≤ ∑ _A : Finset (OffFirstRow lam), Real.sqrt p * ‖tupleRealization lam v‖ := by
      apply Finset.sum_le_sum
      intro A _
      exact ((kernelOperator (maskedEndpointKernel d A)).toContinuousLinearMap.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hn A) (norm_nonneg _))
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_finset, card_offFirstRow]
      push_cast
      ring

end SignedSweeps
end

end OAI
