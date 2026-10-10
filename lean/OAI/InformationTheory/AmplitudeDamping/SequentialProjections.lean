import OAI.InformationTheory.AmplitudeDamping.Model

namespace OAI

universe u_1

noncomputable section
open scoped BigOperators InnerProductSpace
namespace GAD

/-- The elementary sequential-projector union bound. -/
theorem sequential_union_bound {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ℕ → E → E) (hP : ∀ i x y, ⟪P i x, y-P i y⟫_ℝ = 0)
    (u : ℕ → E) (hu : ∀ i, u (i+1)=P i (u i)) (n : ℕ) :
    ‖u 0‖^2-‖u n‖^2 ≤ 4 * ∑ i ∈ Finset.range n, ‖u 0-P i (u 0)‖^2 := by
  let d : ℕ → E := fun i ↦ u i-u (i+1)
  have hi (i : ℕ) : ⟪P i (u 0), d i⟫_ℝ=0 := by
    dsimp [d]; rw [hu]; exact hP i _ _
  have hd (i : ℕ) : ‖d i‖^2=‖u i‖^2-‖u (i+1)‖^2 := by
    have horth : ⟪u (i+1),d i⟫_ℝ=0 := by dsimp only [d]; rw [hu]; exact hP i _ _
    have he : u i=u (i+1)+d i := by dsimp [d]; abel
    rw [he,norm_add_sq_real,horth]
    ring
  have hsum : (∑ i ∈ Finset.range n, ‖d i‖^2) = ‖u 0‖^2-‖u n‖^2 := by
    simp_rw [hd]
    exact Finset.sum_range_sub' (fun i ↦ ‖u i‖^2) n
  have hdsum : (∑ i ∈ Finset.range n, d i)=u 0-u n :=
    Finset.sum_range_sub' u n
  have hin : ⟪u 0,u 0-u n⟫_ℝ = ∑ i ∈ Finset.range n, ⟪u 0-P i (u 0),d i⟫_ℝ := by
    rw [← hdsum,inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [inner_sub_left,hi,sub_zero]
  let a : ℝ := ∑ i ∈ Finset.range n, ‖u 0-P i (u 0)‖*‖d i‖
  have ha0 : 0 ≤ a := Finset.sum_nonneg (fun i _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hia : ⟪u 0,u 0-u n⟫_ℝ ≤ a := by
    rw [hin]
    exact Finset.sum_le_sum (fun i _ ↦ real_inner_le_norm _ _)
  have henergy : ‖u 0‖^2-‖u n‖^2 ≤ 2*a := by
    have he := norm_sub_sq_real (u 0) (u n)
    have hh : ⟪u 0,u 0-u n⟫_ℝ = ‖u 0‖^2-⟪u 0,u n⟫_ℝ := by
      rw [inner_sub_right,real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg ‖u 0-u n‖]
  have hc : a^2 ≤ (∑ i ∈ Finset.range n, ‖u 0-P i (u 0)‖^2)*
      (‖u 0‖^2-‖u n‖^2) := by
    rw [← hsum]
    exact Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n) _ _
  have hS0 : 0 ≤ ‖u 0‖^2-‖u n‖^2 := by
    rw [← hsum]; exact Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  by_cases hS : ‖u 0‖^2-‖u n‖^2=0
  · rw [hS]; positivity
  · have hSpos : 0 < ‖u 0‖^2-‖u n‖^2 := lt_of_le_of_ne hS0 (Ne.symm hS)
    have hsquare : (‖u 0‖^2-‖u n‖^2)^2 ≤ 4*a^2 := by nlinarith
    nlinarith

end GAD

end

end OAI
