import OAI.Combinatorics.BooleanFunctions.Blocks

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Projection
attribute [local instance] Classical.propDecidable
variable {α β γ κ : Type*} [Fintype α] [Nonempty α] [Fintype β] [Fintype γ]

omit [Nonempty α] [Fintype β] in
/-- Conditional averages are characterized by their cell moments. -/
theorem conditional_eq_of_projection (F : α → β) (g h : α → ℝ)
    (hp : ∀ p : β → ℝ, average (fun x => p (F x)*g x) = average (fun x => p (F x)*h x)) :
    conditionalAverage F g = conditionalAverage F h := by
  funext x
  unfold conditionalAverage conditionalValue cellMoment
  congr 1
  exact hp (cell id (F x))

omit [Fintype γ] in
theorem conditional_nested (F : α → β) (H : β → γ) (g : α → ℝ) :
    conditionalAverage (H ∘ F) g = conditionalAverage (H ∘ F) (conditionalAverage F g) := by
  apply conditional_eq_of_projection
  intro p
  exact (conditionalAverage_projection F g (p ∘ H)).symm

omit [Fintype γ] in
theorem pi_projection [Fintype κ] [DecidableEq κ] (F : α → β) (g : α → ℝ)
    (p : (κ → β) → ℝ) (j : κ) :
    average (fun x : κ → α => p (fun i => F (x i))*g (x j)) =
      average (fun x : κ → α => p (fun i => F (x i))*conditionalAverage F g (x j)) := by
  rw [← average_update _ j,← average_update (fun x : κ → α =>
    p (fun i => F (x i))*conditionalAverage F g (x j)) j]
  congr 1
  funext x
  have he (a : α) : (fun i => F (Function.update x j a i)) =
      Function.update (fun i => F (x i)) j (F a) := by
    funext i
    by_cases hi : i = j <;> simp [hi]
  simp only [he,Function.update_self]
  exact (conditionalAverage_projection F g
    (fun b => p (Function.update (fun i => F (x i)) j b))).symm

omit [Fintype γ] in
theorem pi_conditional_sum [Fintype κ] [DecidableEq κ]
    (F : α → β) (H : (κ → β) → γ) (g : α → ℝ) :
    conditionalAverage (fun x : κ → α => H (fun i => F (x i)))
      (fun x => ∑ i, g (x i)) =
    conditionalAverage (fun x : κ → α => H (fun i => F (x i)))
      (fun x => ∑ i, conditionalAverage F g (x i)) := by
  apply conditional_eq_of_projection
  intro p
  simp only [Finset.mul_sum,average_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact pi_projection F g (p ∘ H) j

omit [Nonempty α] [Fintype β] [Fintype γ] in
theorem conditional_equiv {δ : Type*} [Fintype δ] (e : α ≃ δ)
    {ε : Type*} (F : δ → ε) (g : δ → ℝ) :
    conditionalAverage (F ∘ e) (g ∘ e) = conditionalAverage F g ∘ e := by
  funext x
  unfold conditionalAverage conditionalValue cellMoment cellMass
  have hm := average_equiv e (cell F (F (e x)))
  have hg := average_equiv e (fun y => cell F (F (e x)) y*g y)
  exact congrArg₂ (fun a b : ℝ => a/b) hg hm

end Projection
end SquareRootDegree

namespace SquareRootDegree
namespace Projection
attribute [local instance] Classical.propDecidable

variable {α β γ : Type*} [Fintype α] [Nonempty α] [Fintype β]

omit [Fintype β] in
theorem cellMass_pos (F : α → β) (x : α) : 0 < cellMass F (F x) := by
  unfold cellMass average
  apply mul_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  apply Finset.sum_pos'
  · intro y _
    unfold cell
    split_ifs <;> positivity
  · exact ⟨x,Finset.mem_univ x,by simp [cell]⟩

omit [Nonempty α] [Fintype β] in
theorem conditional_const_mul (F : α → β) (g : α → ℝ) (c : ℝ) :
    conditionalAverage F (fun x => c*g x) = fun x => c*conditionalAverage F g x := by
  funext x
  unfold conditionalAverage conditionalValue cellMoment
  simp_rw [show ∀ y, cell F (F x) y*(c*g y) = c*(cell F (F x) y*g y) by intros; ring]
  rw [average_const_mul]
  ring

omit [Fintype β] in
theorem conditional_comp (F : α → β) (g : β → ℝ) :
    conditionalAverage F (fun x => g (F x)) = fun x => g (F x) := by
  funext x
  unfold conditionalAverage conditionalValue
  have he : cellMoment F (fun y => g (F y)) (F x) = g (F x)*cellMass F (F x) := by
    unfold cellMoment cellMass
    rw [← average_const_mul]
    congr 1
    funext y
    by_cases h : F y = F x <;> simp [cell,h]
  rw [he,mul_div_cancel_right₀ _ (cellMass_pos F x).ne']

omit [Nonempty α] [Fintype β] in
theorem conditional_add (F : α → β) (g h : α → ℝ) :
    conditionalAverage F (fun x => g x+h x) =
      fun x => conditionalAverage F g x+conditionalAverage F h x := by
  funext x
  unfold conditionalAverage conditionalValue cellMoment
  simp_rw [mul_add]
  rw [average_add,add_div]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem conditional_tuple_sum (F : α → β) (g : α → ℝ) :
    conditionalAverage (fun x : ι → α => fun i => F (x i)) (fun x => ∑ i, g (x i)) =
      fun x => ∑ i, conditionalAverage F g (x i) := by
  have hp := pi_conditional_sum (κ := ι) F id g
  simp only [id_eq] at hp
  rw [hp]
  exact conditional_comp (fun x : ι → α => fun i => F (x i))
    (fun b => ∑ i, conditionalValue F g (b i))

end Projection
end SquareRootDegree

end

end OAI
