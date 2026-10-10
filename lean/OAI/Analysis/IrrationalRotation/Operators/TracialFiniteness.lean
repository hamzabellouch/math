import OAI.Analysis.IrrationalRotation.Model.VectorTraceState
import Mathlib.Algebra.Star.StarProjection

namespace OAI

noncomputable section

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H} {ξ : H}

theorem IsFaithfulTracialVector.projection_eq_of_trace_eq
    (hτ : IsFaithfulTracialVector M ξ)
    {p q : H →L[ℂ] H} (hpm : p ∈ M) (hqm : q ∈ M)
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : p * q = p) (htrace : vectorTrace ξ p = vectorTrace ξ q) : p = q := by
  have hpos : (q - p).IsPositive :=
    ContinuousLinearMap.IsPositive.of_isStarProjection (hp.sub_of_mul_eq_left hq hpq)
  have hzero : vectorTrace ξ (q - p) = 0 := by
    simp only [vectorTrace, sub_apply, inner_sub_right] at htrace ⊢
    exact sub_eq_zero.mpr htrace.symm
  exact (sub_eq_zero.mp (hτ.2.2 (q - p) (sub_mem hqm hpm) hpos hzero)).symm

theorem IsFaithfulTracialVector.projection_eq_of_equivalent_subprojection
    (hτ : IsFaithfulTracialVector M ξ)
    {p q v : H →L[ℂ] H} (hpm : p ∈ M) (hqm : q ∈ M) (hvm : v ∈ M)
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = p)
    (hvinit : star v * v = p) (hvfinal : v * star v = q) : p = q := by
  apply hτ.projection_eq_of_trace_eq hpm hqm hp hq hpq
  rw [← hvinit, ← hvfinal]
  exact hτ.2.1 (star v) v (star_mem hvm) hvm

theorem IsFaithfulTracialVector.mul_star_eq_one_of_star_mul_eq_one
    (hτ : IsFaithfulTracialVector M ξ)
    {v : H →L[ℂ] H} (hvm : v ∈ M) (hv : star v * v = 1) :
    v * star v = 1 := by
  have hp : IsStarProjection (v * star v) := by
    refine ⟨?_, ?_⟩
    · change (v * star v) * (v * star v) = v * star v
      calc
        (v * star v) * (v * star v) = v * (star v * v) * star v := by
          simp only [mul_assoc]
        _ = v * star v := by rw [hv]; simp
    · simp [IsSelfAdjoint]
  apply hτ.projection_eq_of_trace_eq (mul_mem hvm (star_mem hvm)) (one_mem M)
    hp (IsStarProjection.one _) (mul_one _)
  rw [hτ.2.1 v (star v) hvm (star_mem hvm), hv]

theorem IsFaithfulTracialVector.mem_unitary_of_star_mul_eq_one
    (hτ : IsFaithfulTracialVector M ξ)
    {v : H →L[ℂ] H} (hvm : v ∈ M) (hv : star v * v = 1) :
    v ∈ unitary (H →L[ℂ] H) :=
  Unitary.mem_iff.mpr ⟨hv, hτ.mul_star_eq_one_of_star_mul_eq_one hvm hv⟩

theorem IsFaithfulTracialVector.mem_unitary_of_mul_star_eq_one
    (hτ : IsFaithfulTracialVector M ξ)
    {v : H →L[ℂ] H} (hvm : v ∈ M) (hv : v * star v = 1) :
    v ∈ unitary (H →L[ℂ] H) := by
  apply Unitary.star_mem_iff.mp
  apply hτ.mem_unitary_of_star_mul_eq_one (star_mem hvm)
  simpa only [star_star] using hv

end Invariant233

end

end OAI
