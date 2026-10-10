import OAI.NumberTheory.TwoPoint.Bounds.FamilyPatternSum

namespace OAI

/-! Sum one coordinate first, retaining the weighted sum of all other coordinates. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def outsideCoordinate {I : Type*} {β : I → Type*} (j : I) (w : ∀ i, β i) :
    (i : {i // i ≠ j}) → β i := fun i => w i

lemma update_eq_of_outside_eq {I : Type*} [DecidableEq I] {β : I → Type*}
    (j : I) (u v : ∀ i, β i) (h : outsideCoordinate j u = outsideCoordinate j v) :
    Function.update u j (v j) = v := by
  funext i
  by_cases hi : i = j
  · subst i
    simp
  · rw [Function.update_of_ne hi]
    exact congrFun h ⟨i, hi⟩

theorem coordinate_fiber_sum_bound {I : Type*} [Fintype I] [DecidableEq I]
    {β : I → Type*} [∀ i, DecidableEq (β i)]
    (F : Finset (∀ i, β i)) (j : I) (weight : (i : I) → β i → ℝ)
    (hw : ∀ i x, 0 ≤ weight i x) (M : ℝ)
    (hfiber : ∀ x ∈ F.image (outsideCoordinate j),
      (∑ v ∈ (F.filter (fun w => outsideCoordinate j w = x)).image (fun w => w j),
        weight j v) ≤ M) :
    (∑ w ∈ F, ∏ i, weight i (w i)) ≤
      M * ∑ x ∈ F.image (outsideCoordinate j), ∏ i, weight i.val (x i) := by
  let fiber (x : (i : {i // i ≠ j}) → β i) :=
    F.filter (fun w => outsideCoordinate j w = x)
  have hsplit (w : ∀ i, β i) :
      (∏ i, weight i (w i)) = weight j (w j) *
        ∏ i : {i // i ≠ j}, weight i.val (outsideCoordinate j w i) := by
    rw [← mul_prod_erase univ (fun i => weight i (w i)) (mem_univ j)]
    congr 1
    exact prod_subtype (univ.erase j) (by simp) (fun i => weight i (w i))
  have hinj (x : (i : {i // i ≠ j}) → β i) :
      Set.InjOn (fun w : ∀ i, β i => w j) (fiber x) := by
    intro u hu v hv he
    funext i
    by_cases hi : i = j
    · subst i
      exact he
    · have ho := (mem_filter.mp hu).2.trans (mem_filter.mp hv).2.symm
      exact congrFun ho ⟨i, hi⟩
  calc
    _ = ∑ x ∈ F.image (outsideCoordinate j), ∑ w ∈ fiber x, ∏ i, weight i (w i) :=
      (sum_fiberwise_of_maps_to (fun w hw => mem_image_of_mem _ hw) _).symm
    _ = ∑ x ∈ F.image (outsideCoordinate j),
        (∑ w ∈ fiber x, weight j (w j)) * ∏ i, weight i.val (x i) := by
      apply sum_congr rfl
      intro x hx
      rw [sum_mul]
      apply sum_congr rfl
      intro w hw'
      rw [hsplit, (mem_filter.mp hw').2]
    _ ≤ ∑ x ∈ F.image (outsideCoordinate j), M * ∏ i, weight i.val (x i) := by
      apply sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_right _ (prod_nonneg (fun i _ => hw _ _))
      rw [← sum_image (hinj x)]
      exact hfiber x hx
    _ = _ := (mul_sum _ _ _).symm

end TwoPointCorrelations

end OAI
