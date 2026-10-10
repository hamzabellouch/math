import Mathlib
import OAI.Computability.MinUncut.Games.Sampling

namespace OAI

section
namespace MinUncutGames.Foundations.Repetition.ProfileCorrection
open scoped BigOperators
open MinUncutGames.Foundations.Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

def seedQuestionMarginal (p : X × (S × Y) → ℝ) : X × S → ℝ :=
  firstMarginal (fun z : (X × S) × Y => p (z.1.1, (z.1.2, z.2)))

theorem seedQuestionMarginal_isProbability (p : X × (S × Y) → ℝ)
    (hp : IsProbability p) : IsProbability (seedQuestionMarginal p) := by
  apply firstMarginal_isProbability
  constructor
  · intro z
    exact hp.1 _
  · have h := hp.2
    simp only [Fintype.sum_prod_type] at h ⊢
    exact h

omit [Fintype X] in
theorem seedQuestionMarginal_first (p : X × (S × Y) → ℝ) :
    firstMarginal (seedQuestionMarginal p) = firstMarginal p := by
  funext x
  simp only [seedQuestionMarginal, firstMarginal, Fintype.sum_prod_type]

theorem totalVariation_triangle {Ω : Type*} [Fintype Ω]
    (p c d : Ω → ℝ) :
    totalVariation p d ≤ totalVariation p c + totalVariation c d := by
  unfold totalVariation
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => abs_sub_le (p x) (c x) (d x))
  rw [Finset.sum_add_distrib] at h
  linarith

theorem left_profile_correction
    (p : X × (S × Y) → ℝ) (μ : X × Y → ℝ)
    (fallbackS : S → ℝ) (fallbackY : Y → ℝ)
    (hp : IsProbability p) (hμ : IsProbability μ)
    (hS : IsProbability fallbackS) (hY : IsProbability fallbackY) :
    totalVariation p (fun z => μ (z.1, z.2.2) *
      conditionalKernel (seedQuestionMarginal p) fallbackS z.1 z.2.1) ≤
    totalVariation p (fun z => seedQuestionMarginal p (z.1, z.2.1) *
      conditionalKernel μ fallbackY z.1 z.2.2) +
    totalVariation (firstMarginal p) (firstMarginal μ) := by
  let σ := seedQuestionMarginal p
  let L := conditionalKernel σ fallbackS
  let M := conditionalKernel μ fallbackY
  let k : X → S × Y → ℝ := fun x sy => L x sy.1 * M x sy.2
  let c : X × (S × Y) → ℝ := fun z => σ (z.1,z.2.1) * M z.1 z.2.2
  let d : X × (S × Y) → ℝ := fun z => μ (z.1,z.2.2) * L z.1 z.2.1
  have hσ : IsProbability σ := seedQuestionMarginal_isProbability p hp
  have hk : ∀ x, IsProbability (k x) := by
    intro x
    exact kernelProduct_isProbability (L x) (fun _ : S => M x)
      (conditionalKernel_isProbability σ fallbackS hσ hS x)
      (fun _ => conditionalKernel_isProbability μ fallbackY hμ hY x)
  have hc : c = fun z => firstMarginal σ z.1 * k z.1 z.2 := by
    funext z
    change σ (z.1,z.2.1) * M z.1 z.2.2 =
      firstMarginal σ z.1 * (L z.1 z.2.1 * M z.1 z.2.2)
    rw [← mul_assoc, marginal_mul_conditionalKernel σ fallbackS hσ]
  have hd : d = fun z => firstMarginal μ z.1 * k z.1 z.2 := by
    funext z
    change μ (z.1,z.2.2) * L z.1 z.2.1 =
      firstMarginal μ z.1 * (L z.1 z.2.1 * M z.1 z.2.2)
    calc
      _ = (firstMarginal μ z.1 * M z.1 z.2.2) * L z.1 z.2.1 := by
        rw [marginal_mul_conditionalKernel μ fallbackY hμ]
      _ = _ := by ring
  have hmiddle : totalVariation c d =
      totalVariation (firstMarginal σ) (firstMarginal μ) := by
    rw [hc, hd]
    exact totalVariation_joint_common_kernel _ _ k hk
  have result := totalVariation_triangle p c d
  rw [hmiddle] at result
  have hmarg : firstMarginal σ = firstMarginal p := seedQuestionMarginal_first p
  rw [hmarg] at result
  exact result
end
end MinUncutGames.Foundations.Repetition.ProfileCorrection

end
section
namespace MinUncutGames.Foundations.Repetition

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

end MinUncutGames.Foundations.Repetition

end

end OAI
