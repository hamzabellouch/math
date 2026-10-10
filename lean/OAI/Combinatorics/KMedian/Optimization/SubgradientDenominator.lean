import Mathlib
import OAI.Combinatorics.KMedian.Optimization.SimplexDiameter
import OAI.Combinatorics.KMedian.Rounding.IntegerSimplexProjection
import OAI.Combinatorics.KMedian.Optimization.GradientDenominator

namespace OAI

section
section
namespace MetricKMedian.ProjectedSubgradient
open Finset
variable {n : ℕ} [NeZero n]

theorem next_denominator (k b R Q : ℤ) (hb : 0 < b) (hR : 0 < R) (hQ : 0 < Q)
    (g : (Fin n → ℚ) → Fin n → ℚ) (v : Vector ℚ n)
    (hv : ∀ i, RationalGrid.At Q (point v i))
    (hg : ∀ i, RationalGrid.At R (g (point v) i)) :
    ∃ Q' : ℤ, 0 < Q' ∧ Q' ≤ Q*(b*R*(n:ℤ)) ∧
      ∀ i, RationalGrid.At Q' (point (next (k:ℚ) (1/(b:ℚ)) g v) i) := by
  choose Y hY using hv
  choose G hG using hg
  let X : Fin n → ℤ := fun i => Y i*(b*R)-G i*Q
  have hQi : Q*b*R > 0 := mul_pos (mul_pos hQ hb) hR
  have hX : ∀ i, point v i-(1/(b:ℚ))*g (point v) i=(X i:ℚ)/((Q*b*R:ℤ):ℚ) := by
    intro i
    rw [hY,hG]
    simp only [X,Int.cast_sub,Int.cast_mul]
    have hq : (Q:ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
    have hbq : (b:ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    have hrq : (R:ℚ) ≠ 0 := by exact_mod_cast hR.ne'
    field_simp
  obtain ⟨Q',Y',hpos,hbound,hval⟩ := Simplex.project_integer_denominator
    (fun i => point v i-(1/(b:ℚ))*g (point v) i) X (Q*b*R) k hQi hX
  refine ⟨Q',hpos,by nlinarith [hbound],fun i => ⟨Y' i,?_⟩⟩
  rw [next_apply,hval]

theorem trajectory_denominator (k b R : ℤ) (hb : 0 < b) (hR : 0 < R)
    (g : (Fin n → ℚ) → Fin n → ℚ)
    (hg : ∀ y i, RationalGrid.At R (g y i)) (t : ℕ) :
    ∃ Q : ℤ, 0 < Q ∧ Q ≤ (b*R*(n:ℤ))^t ∧
      ∀ i, RationalGrid.At Q (point (trajectory (k:ℚ) (1/(b:ℚ)) g (initial (k:ℚ)) t) i) := by
  induction t with
  | zero =>
    refine ⟨1,by norm_num,by norm_num,?_⟩
    intro i
    simp only [trajectory_zero,initial,point_ofFn_apply]
    split_ifs
    · exact RationalGrid.integer 1 k (by norm_num)
    · exact RationalGrid.zero 1
  | succ t ih =>
    obtain ⟨Q,hQ,hbound,hv⟩ := ih
    obtain ⟨Q',hQ',hbound',hv'⟩ := next_denominator k b R Q hb hR hQ g _ hv (hg _)
    refine ⟨Q',hQ',hbound'.trans ?_,hv'⟩
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right hbound (by positivity)

end MetricKMedian.ProjectedSubgradient
end
end

end OAI
