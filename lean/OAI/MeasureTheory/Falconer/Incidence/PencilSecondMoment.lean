import OAI.MeasureTheory.Falconer.Incidence.PlanarBaselineIncidence

namespace OAI

/-! The geometric second-moment bound, allowing unequal pencil sizes. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem pencil_second_moment_bound (N : ℕ) {s t K M : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, InBoundedLineChart (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ((T x).card:ℝ) ≤ M ∧ ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    (∑ l ∈ P.biUnion T, (tubeDegree P T l)^2) ≤
      (K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t)*(P.card:ℝ)^2 := by
  let δ := 1/(2:ℝ)^N
  let C := K*(80*δ)^s*M
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hrow (x : Space 2) (hx : x ∈ P) :
      (∑ y ∈ P, ((T x ∩ T y).card:ℝ)) ≤ C*(1+K*planarPotentialConstant s t)*(P.card:ℝ) := by
    have hM : 0 ≤ M := (Nat.cast_nonneg (T x).card).trans (hT x hx).2.2.1
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hpot := finite_dyadic_truncated_potential_real P x N hK hs hst hPball
    calc
      _ ≤ ∑ y ∈ P, C*(1+(1/max (dist x y) δ)^s) := by
        apply Finset.sum_le_sum
        intro y hy
        apply (intersect_tube_power_bound hδ hδ1 hs hK (T x) (T y) x y
          (hPchart x hx).1 (hT x hx).1 (hT x hx).2.2.2
          (hT y hy).2.2.2 (hT x hx).2.1).trans
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hT x hx).2.2.1
          (by positivity)) (by positivity)
      _ = C*((P.card:ℝ)+∑ y ∈ P, (1/max (dist x y) δ)^s) := by
        simp only [mul_add,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one]
        rw [← Finset.mul_sum]
        ring
      _ ≤ C*((P.card:ℝ)+K*planarPotentialConstant s t*(P.card:ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hpot) hC
      _ = _ := by ring
  rw [sum_tubeDegree_sq]
  calc
    _ ≤ ∑ _x ∈ P, C*(1+K*planarPotentialConstant s t)*(P.card:ℝ) :=
      Finset.sum_le_sum hrow
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; dsimp [C]; ring

end Falconer

end OAI
