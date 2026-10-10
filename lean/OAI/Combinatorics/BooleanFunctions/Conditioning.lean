import OAI.Combinatorics.BooleanFunctions.Walsh

namespace OAI

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

/-! ## Uniform finite conditioning, without measure-theoretic assumptions -/

theorem average_prod {α β : Type*} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    average f = average (fun x => average (fun y => f (x,y))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

def updateSwap {ι α : Type*} [DecidableEq ι] (i : ι) :
    ((ι → α) × α) ≃ ((ι → α) × α) where
  toFun p := (Function.update p.1 i p.2, p.1 i)
  invFun p := (Function.update p.1 i p.2, p.1 i)
  left_inv p := by
    apply Prod.ext
    · funext j; by_cases h : j = i <;> simp [h]
    · simp
  right_inv p := by
    apply Prod.ext
    · funext j; by_cases h : j = i <;> simp [h]
    · simp

theorem average_update {ι α : Type*} [DecidableEq ι] [Fintype ι] [Fintype α] [Nonempty α]
    (f : (ι → α) → ℝ) (i : ι) :
    average (fun x => average (fun a => f (Function.update x i a))) = average f := by
  classical
  have h := average_equiv (updateSwap (α := α) i) (fun p => f p.1)
  rw [average_prod, average_prod] at h
  simpa [updateSwap, average_const] using h

def cell {α β : Type*} (F : α → β) (b : β) (x : α) : ℝ := by
  classical
  exact if F x = b then 1 else 0

def cellMass {α β : Type*} [Fintype α] (F : α → β) (b : β) : ℝ :=
  average (cell F b)

def cellMoment {α β : Type*} [Fintype α] (F : α → β) (g : α → ℝ) (b : β) : ℝ :=
  average (fun x => cell F b x * g x)

def conditionalValue {α β : Type*} [Fintype α] (F : α → β) (g : α → ℝ) (b : β) : ℝ :=
  cellMoment F g b / cellMass F b

def conditionalAverage {α β : Type*} [Fintype α] (F : α → β) (g : α → ℝ) : α → ℝ :=
  fun x => conditionalValue F g (F x)

theorem cellMoment_eq_zero_of_mass_eq_zero {α β : Type*} [Fintype α] [Nonempty α]
    (F : α → β) (g : α → ℝ) (b : β) (h : cellMass F b = 0) :
    cellMoment F g b = 0 := by
  classical
  have hc : ∀ x, cell F b x = 0 := by
    intro x
    have hs : ∑ x, cell F b x = 0 := by
      unfold cellMass average at h
      exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => by unfold cell; split <;> norm_num)).mp hs x (Finset.mem_univ x)
  simp [cellMoment, hc]

theorem mass_mul_conditionalValue {α β : Type*} [Fintype α] [Nonempty α]
    (F : α → β) (g : α → ℝ) (b : β) :
    cellMass F b * conditionalValue F g b = cellMoment F g b := by
  by_cases h : cellMass F b = 0
  · simp [h, cellMoment_eq_zero_of_mass_eq_zero F g b h]
  · simp [conditionalValue, field]

theorem average_mul_comp_eq_sum {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β) (g : α → ℝ) (h : β → ℝ) :
    average (fun x => h (F x) * g x) = ∑ b, h b * cellMoment F g b := by
  classical
  simp only [cellMoment, ← average_const_mul, ← average_sum]
  congr 1
  funext x
  simp [cell]

theorem cellMoment_conditionalAverage {α β : Type*} [Fintype α] [Nonempty α]
    (F : α → β) (g : α → ℝ) (b : β) :
    cellMoment F (conditionalAverage F g) b = cellMoment F g b := by
  have he : (fun x => cell F b x * conditionalAverage F g x) =
      (fun x => cell F b x * conditionalValue F g b) := by
    funext x
    unfold cell conditionalAverage
    split_ifs with h
    · rw [h]
    · simp
  rw [cellMoment, he, average_mul_const]
  exact mass_mul_conditionalValue F g b

theorem conditionalAverage_projection {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    (F : α → β) (g : α → ℝ) (h : β → ℝ) :
    average (fun x => h (F x) * conditionalAverage F g x) =
      average (fun x => h (F x) * g x) := by
  rw [average_mul_comp_eq_sum, average_mul_comp_eq_sum]
  simp only [cellMoment_conditionalAverage]

theorem average_conditionalAverage {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    (F : α → β) (g : α → ℝ) : average (conditionalAverage F g) = average g := by
  simpa using conditionalAverage_projection F g (fun _ => 1)

theorem conditionalAverage_sq {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    (F : α → β) (g : α → ℝ) :
    average (fun x => conditionalAverage F g x ^ 2) =
      average (fun x => conditionalAverage F g x * g x) := by
  simpa only [conditionalAverage, pow_two] using
    conditionalAverage_projection F g (conditionalValue F g)

theorem conditionalAverage_lower_bound {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    (F : α → β) (g : α → ℝ) (p : β → ℝ) :
    average (fun x => g x ^ 2) - average (fun x => (g x - p (F x)) ^ 2) ≤
      average (fun x => conditionalAverage F g x ^ 2) := by
  have h := average_nonneg (fun x => sq_nonneg (conditionalAverage F g x - p (F x)))
  have he : (fun x => (conditionalAverage F g x - p (F x)) ^ 2) =
      (fun x => conditionalAverage F g x ^ 2 - 2 * (p (F x) * conditionalAverage F g x) +
        p (F x) ^ 2) := by funext x; ring
  have he' : (fun x => (g x - p (F x)) ^ 2) =
      (fun x => g x ^ 2 - 2 * (p (F x) * g x) + p (F x) ^ 2) := by funext x; ring
  rw [he, average_add, average_sub, average_const_mul, conditionalAverage_projection] at h
  rw [he', average_add, average_sub, average_const_mul]
  linarith

end SquareRootDegree

end

end OAI
