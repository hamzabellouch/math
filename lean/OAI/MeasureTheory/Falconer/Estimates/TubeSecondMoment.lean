import OAI.MeasureTheory.Falconer.Incidence.PublishedFurstenberg
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace OAI

/-! Exact finite incidence identities before the geometric common-tube bound. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def tubeDegree (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (l : Space 2) : ℝ :=
  ∑ x ∈ P, if l ∈ T x then 1 else 0

theorem sum_tube_membership (U S : Finset (Space 2)) (hS : S ⊆ U) :
    (∑ l ∈ U, if l ∈ S then (1 : ℝ) else 0) = S.card := by
  rw [← Finset.sum_filter]
  have he : U.filter (fun l => l ∈ S) = S := by
    ext l
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hl => hS hl)
  rw [he]
  simp

theorem sum_tubeDegree (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) :
    (∑ l ∈ P.biUnion T, tubeDegree P T l) = ∑ x ∈ P, ((T x).card : ℝ) := by
  unfold tubeDegree
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  exact sum_tube_membership _ _ (Finset.subset_biUnion_of_mem T hx)

theorem sum_tubeDegree_sq (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) :
    (∑ l ∈ P.biUnion T, (tubeDegree P T l)^2) =
      ∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card : ℝ) := by
  let U := P.biUnion T
  calc
    _ = ∑ l ∈ U, ∑ x ∈ P, ∑ y ∈ P,
        (if l ∈ T x then (1 : ℝ) else 0)*(if l ∈ T y then 1 else 0) := by
      simp only [tubeDegree, pow_two, Finset.sum_mul_sum, U]
    _ = ∑ x ∈ P, ∑ y ∈ P, ∑ l ∈ U,
        (if l ∈ T x then (1 : ℝ) else 0)*(if l ∈ T y then 1 else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y _
      have he (l : Space 2) :
          (if l ∈ T x then (1 : ℝ) else 0)*(if l ∈ T y then 1 else 0) =
          if l ∈ T x ∩ T y then 1 else 0 := by
        by_cases hx : l ∈ T x <;> by_cases hy : l ∈ T y <;> simp [hx,hy]
      simp_rw [he]
      exact sum_tube_membership U _ (fun l hl =>
        Finset.mem_biUnion.mpr ⟨x,hx,(Finset.mem_inter.mp hl).1⟩)

theorem tube_union_second_moment (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) :
    (∑ x ∈ P, ((T x).card : ℝ))^2 ≤
      ((P.biUnion T).card : ℝ) * (∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card : ℝ)) := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (P.biUnion T)
    (fun _ => (1 : ℝ)) (tubeDegree P T)
  simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
    sum_tubeDegree, sum_tubeDegree_sq] using hh

end Falconer

end OAI
