import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder

namespace BinaryCoordinateSweeps
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

lemma positive_pow {B : W →ₗ[ℂ] W} (hB : B.IsPositive) (q : ℕ) : (B^q).IsPositive :=
  match q with
  | 0 => LinearMap.isPositive_one
  | 1 => by simpa using hB
  | n+2 => by
    rw [pow_succ,pow_succ']
    simpa only [Module.End.mul_eq_comp,LinearMap.comp_assoc,hB.adjoint_eq] using (positive_pow hB n).conj_adjoint B

theorem positive_trace_restrict_le (S : Submodule ℂ W) (B : W →ₗ[ℂ] W)
    (hB : B.IsPositive) (hS : ∀ x ∈ S, B x ∈ S) :
    (LinearMap.trace ℂ S (B.restrict hS)).re ≤ (LinearMap.trace ℂ W B).re := by
  let P := S.starProjection.toLinearMap
  let Q : W →ₗ[ℂ] W := 1-P
  have hPsy : P.IsSymmetric := (Submodule.isSymmetricProjection_starProjection S).isSymmetric
  have hQsy : Q.IsSymmetric := LinearMap.IsSymmetric.id.sub hPsy
  have hPP : P*P = P := by
    ext x
    exact congrArg (fun t : W →L[ℂ] W => t x) S.isIdempotentElem_starProjection
  have hQQ : Q*Q = Q := by
    dsimp [Q]
    noncomm_ring [hPP]
  have hQBQ : (Q*B*Q).IsPositive := by
    simpa only [Module.End.mul_eq_comp,LinearMap.comp_assoc,hQsy.adjoint_eq] using hB.conj_adjoint Q
  have hpRange : ∀ x, ((P*B)*P) x ∈ S := by
    intro x
    exact S.starProjection_apply_mem _
  have hpRestr : ((P*B)*P).restrict (fun x _ => hpRange x) = B.restrict hS := by
    ext x
    change P (B (P x.val)) = B x.val
    rw [show P x.val = x.val from Submodule.starProjection_eq_self_iff.mpr x.property]
    exact Submodule.starProjection_eq_self_iff.mpr (hS x.val x.property)
  have hTrP : LinearMap.trace ℂ W (P*B*P) = LinearMap.trace ℂ W (B*P) := by
    change LinearMap.trace ℂ W (P.comp (B*P)) = _
    rw [LinearMap.trace_comp_comm']
    change LinearMap.trace ℂ W (B*P*P) = _
    rw [mul_assoc,hPP]
  have hTrQ : LinearMap.trace ℂ W (Q*B*Q) = LinearMap.trace ℂ W B -
      LinearMap.trace ℂ W (B*P) := by
    change LinearMap.trace ℂ W (Q.comp (B*Q)) = _
    rw [LinearMap.trace_comp_comm']
    change LinearMap.trace ℂ W (B*Q*Q) = _
    rw [mul_assoc,hQQ]
    dsimp [Q]
    rw [mul_sub,mul_one,map_sub]
  have hTrace := LinearMap.trace_restrict_eq_of_forall_mem S (P*B*P) hpRange
  rw [hpRestr,hTrP] at hTrace
  have hn := (Complex.nonneg_iff.mp hQBQ.trace_nonneg).1
  rw [hTrQ,Complex.sub_re,← hTrace] at hn
  linarith

end BinaryCoordinateSweeps

end

end OAI
