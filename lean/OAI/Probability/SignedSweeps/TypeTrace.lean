import OAI.Probability.SignedSweeps.GroupedTypes
import OAI.Probability.SignedSweeps.OccupiedCounts

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {E H K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype H] [Fintype K]

omit [FiniteDimensional ℂ E] in
lemma trace_type_resolution [FiniteDimensional ℂ E] (P X Y : E →ₗ[ℂ] E)
    (A : H → E →ₗ[ℂ] E) (B : K → E →ₗ[ℂ] E)
    (hA : ∑ a, A a = 1) (hB : ∑ b, B b = 1) :
    LinearMap.trace ℂ E (P*X*Y) =
      ∑ a, ∑ b, LinearMap.trace ℂ E (P*(A a*X)*(B b*Y)) := by
  calc
    _ = LinearMap.trace ℂ E (P*((∑ a, A a)*X)*((∑ b, B b)*Y)) := by
      rw [hA, hB, one_mul, one_mul]
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum, map_sum]
      exact Finset.sum_comm

lemma positive_trace_type_resolution_bound (P X Y : E →ₗ[ℂ] E)
    (A : H → E →ₗ[ℂ] E) (B : K → E →ₗ[ℂ] E)
    (hA : ∑ a, A a = 1) (hB : ∑ b, B b = 1)
    (hX : X.IsPositive) (hY : Y.IsPositive) (hP : P.IsPositive) (hPP : P*P=P)
    (hAs : ∀ a, (A a).IsPositive) (hBs : ∀ b, (B b).IsPositive)
    (hAA : ∀ a, A a*A a=A a) (hBB : ∀ b, B b*B b=B b)
    (hPA : ∀ a, P*A a=A a*P) (hPB : ∀ b, P*B b=B b*P)
    (hPX : P*X=X*P) (hPY : P*Y=Y*P)
    (hAX : ∀ a, A a*X=X*A a) (hBY : ∀ b, B b*Y=Y*B b) :
    (LinearMap.trace ℂ E (P*X*Y)).re ≤
      ∑ a, ∑ b, ‖(A a*B b*P).toContinuousLinearMap‖^2 *
        (LinearMap.trace ℂ E (A a*X)).re * (LinearMap.trace ℂ E (B b*Y)).re := by
  rw [trace_type_resolution P X Y A B hA hB]
  simp only [Complex.re_sum]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  apply positive_global_projection_trace_bound
    (A a*X) (B b*Y) (A a) (B b) P
    (positive_commuting_projection X (A a) hX (hAs a).isSymmetric (hAA a) (hAX a))
    (positive_commuting_projection Y (B b) hY (hBs b).isSymmetric (hBB b) (hBY b))
    (hAs a).isSymmetric hP.isSymmetric hPP
  · rw [← mul_assoc, hPA, mul_assoc, hPX, ← mul_assoc]
  · rw [← mul_assoc, hPB, mul_assoc, hPY, ← mul_assoc]
  · rw [← mul_assoc, hAA]
  · rw [← mul_assoc, hBB]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k : J → ℕ}

lemma blockTypeProjection_trace_real (e : (Σ j, Fin (k j)) ≃ Fin p)
    (t : ∀ j, PairType (k j)) (f : ∀ j, SymmetricGroup (k j) → ℂ)
    (hf : ∀ j, (coefficientAction (signedWordRepresentation (k j) C) (f j)).IsPositive) :
    (LinearMap.trace ℂ (WordSpace p (C ⊕ C))
      (blockTypeProjection e t * coefficientAction (signedWordRepresentation p C)
        (coefficientPush (blockPermutation e) (productCoefficient f)))).re =
      ∏ j, (LinearMap.trace ℂ (WordSpace (k j) (C ⊕ C))
        ((t j).projector C * coefficientAction (signedWordRepresentation (k j) C) (f j))).re := by
  rw [blockTypeProjection_trace]
  have hp (j : J) : ((t j).projector C *
      coefficientAction (signedWordRepresentation (k j) C) (f j)).IsPositive := by
    apply positive_commuting_projection _ _ (hf j)
      (pairTypeProjection_positive _ _ _ _).isSymmetric
      (pairTypeProjection_idempotent _ _ _ _) (pairTypeProjection_coefficient_commute _ _ _ _)
  have hr (j : J) : LinearMap.trace ℂ (WordSpace (k j) (C ⊕ C))
      ((t j).projector C * coefficientAction (signedWordRepresentation (k j) C) (f j)) =
      ((LinearMap.trace ℂ (WordSpace (k j) (C ⊕ C))
      ((t j).projector C * coefficientAction (signedWordRepresentation (k j) C) (f j))).re : ℂ) := by
    apply Complex.ext <;> simp only [Complex.ofReal_re, Complex.ofReal_im]
    exact (Complex.nonneg_iff.mp (hp j).trace_nonneg).2.symm
  have he := Finset.prod_congr (s₁ := Finset.univ) rfl (fun j _ => hr j)
  rw [he, ← Complex.ofReal_prod, Complex.ofReal_re]

end SignedSweeps
end

end OAI
