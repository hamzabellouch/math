import Mathlib

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                             
section

namespace UniqueGames.Foundations.Repetition

open scoped BigOperators

noncomputable section

variable {ι α β : Type*} [Fintype ι] [DecidableEq α] [DecidableEq β]

def revealedProductWeight (weight : ι → α → β → ℝ) (mask : ι → Bool)
    (fixedLeft : ι → α) (fixedRight : ι → β) (x : ι → α) (y : ι → β) : ℝ :=
  ∏ i, weight i (x i) (y i) *
    (if mask i then (if y i = fixedRight i then 1 else 0)
     else (if x i = fixedLeft i then 1 else 0))

def revealedLeftWeight (weight : ι → α → β → ℝ) (mask : ι → Bool)
    (fixedLeft : ι → α) (fixedRight : ι → β) (x : ι → α) : ℝ :=
  ∏ i, if mask i then weight i (x i) (fixedRight i)
    else (if x i = fixedLeft i then 1 else 0)

def revealedRightWeight (weight : ι → α → β → ℝ) (mask : ι → Bool)
    (fixedLeft : ι → α) (fixedRight : ι → β) (y : ι → β) : ℝ :=
  ∏ i, if mask i then (if y i = fixedRight i then 1 else 0)
    else weight i (fixedLeft i) (y i)

theorem revealedProductWeight_factorizes (weight : ι → α → β → ℝ) (mask : ι → Bool)
    (fixedLeft : ι → α) (fixedRight : ι → β) (x : ι → α) (y : ι → β) :
    revealedProductWeight weight mask fixedLeft fixedRight x y =
      revealedLeftWeight weight mask fixedLeft fixedRight x *
        revealedRightWeight weight mask fixedLeft fixedRight y := by
  unfold revealedProductWeight revealedLeftWeight revealedRightWeight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hm : mask i = true
  · by_cases hy : y i = fixedRight i <;> simp [hm, hy]
  · by_cases hx : x i = fixedLeft i <;> simp [hm, hx]

theorem revealedProductWeight_local_restrictions
    (weight : ι → α → β → ℝ) (mask : ι → Bool)
    (fixedLeft : ι → α) (fixedRight : ι → β)
    (leftTest : (ι → α) → ℝ) (rightTest : (ι → β) → ℝ)
    (x : ι → α) (y : ι → β) :
    revealedProductWeight weight mask fixedLeft fixedRight x y * leftTest x * rightTest y =
      (revealedLeftWeight weight mask fixedLeft fixedRight x * leftTest x) *
      (revealedRightWeight weight mask fixedLeft fixedRight y * rightTest y) := by
  rw [revealedProductWeight_factorizes]
  ring

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem productWeight_mass (left : X → ℝ) (right : Y → ℝ) :
    (∑ xy : X × Y, left xy.1 * right xy.2) =
      (∑ x, left x) * (∑ y, right y) := by
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

def normalizedWeight (weight : X → ℝ) : X → ℝ :=
  fun x => weight x / ∑ x', weight x'

theorem normalizedWeight_isProbability (weight : X → ℝ)
    (hweight : ∀ x, 0 ≤ weight x) (hmass : 0 < ∑ x, weight x) :
    (∀ x, 0 ≤ normalizedWeight weight x) ∧ (∑ x, normalizedWeight weight x) = 1 := by
  constructor
  · intro x
    exact div_nonneg (hweight x) hmass.le
  · simp only [normalizedWeight, div_eq_mul_inv, ← Finset.sum_mul, mul_inv_cancel₀ hmass.ne']

theorem normalized_productWeight (left : X → ℝ) (right : Y → ℝ)
    (hleft : 0 < ∑ x, left x) (hright : 0 < ∑ y, right y) (xy : X × Y) :
    normalizedWeight (fun z : X × Y => left z.1 * right z.2) xy =
      normalizedWeight left xy.1 * normalizedWeight right xy.2 := by
  unfold normalizedWeight
  rw [productWeight_mass]
  field_simp

theorem normalized_rectangle_restriction
    (left : X → ℝ) (right : Y → ℝ) (leftTest : X → ℝ) (rightTest : Y → ℝ)
    (hleft : 0 < ∑ x, left x * leftTest x)
    (hright : 0 < ∑ y, right y * rightTest y) (xy : X × Y) :
    normalizedWeight
      (fun z : X × Y => left z.1 * right z.2 * leftTest z.1 * rightTest z.2) xy =
      normalizedWeight (fun x => left x * leftTest x) xy.1 *
      normalizedWeight (fun y => right y * rightTest y) xy.2 := by
  have hfun : (fun z : X × Y => left z.1 * right z.2 * leftTest z.1 * rightTest z.2) =
      (fun z : X × Y => (left z.1 * leftTest z.1) * (right z.2 * rightTest z.2)) := by
    funext z
    ring
  rw [hfun]
  exact normalized_productWeight _ _ hleft hright xy

end

end UniqueGames.Foundations.Repetition

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
