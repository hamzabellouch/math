import Mathlib
import OAI.Combinatorics.IndependentSets.Repetition.TotalVariation

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealEndpoint (q : X × Y) (side : Bool) : X ⊕ Y :=
  if side then Sum.inr q.2 else Sum.inl q.1

def revealLaw (μ : FiniteDistribution (X × Y)) :
    FiniteDistribution ((X × Y) × (X ⊕ Y)) :=
  (μ.product (FiniteDistribution.uniform Bool)).pushforward
    (fun z => (z.1, revealEndpoint z.1 z.2))

theorem revealLaw_weight (μ : FiniteDistribution (X × Y)) (q : X × Y) (r : X ⊕ Y) :
    (revealLaw μ).weight (q,r) =
      (if r = Sum.inl q.1 then μ.weight q / 2 else 0) +
      (if r = Sum.inr q.2 then μ.weight q / 2 else 0) := by
  classical
  rcases q with ⟨x,y⟩
  simp only [revealLaw, FiniteDistribution.pushforward, FiniteDistribution.product,
    Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  simp [revealEndpoint, FiniteDistribution.uniform, div_eq_mul_inv, add_comm, eq_comm]

def revealFirstLaw (μ : FiniteDistribution (X × Y)) :
    FiniteDistribution ((X ⊕ Y) × (X × Y)) :=
  (revealLaw μ).transport (Equiv.prodComm _ _)

omit [DecidableEq X] [DecidableEq Y] in
@[simp] theorem revealFirstLaw_weight (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (q : X × Y) :
    (revealFirstLaw μ).weight (r,q) = (revealLaw μ).weight (q,r) := rfl

def revealFallback (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) :
    FiniteDistribution (X × Y) :=
  match r with
  | Sum.inl x => μ.pushforward (fun q => (x,q.2))
  | Sum.inr y => μ.pushforward (fun q => (q.1,y))

def revealProfile (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) :
    FiniteDistribution (X × Y) :=
  gameConditionalKernel (revealFirstLaw μ) (revealFallback μ r) r

theorem revealProfile_inl_support (μ : FiniteDistribution (X × Y))
    (x : X) (q : X × Y) (h : q.1 ≠ x) :
    (revealProfile μ (Sum.inl x)).weight q = 0 := by
  classical
  rcases q with ⟨x',y⟩
  dsimp at h
  simp only [revealProfile, gameConditionalKernel, toGameLaw, conditionalKernel]
  split
  · simp [revealFallback, FiniteDistribution.pushforward, Fintype.sum_prod_type,
      Prod.mk.injEq, Ne.symm h]
  · simp [revealLaw_weight, Ne.symm h]

theorem revealProfile_inr_support (μ : FiniteDistribution (X × Y))
    (y : Y) (q : X × Y) (h : q.2 ≠ y) :
    (revealProfile μ (Sum.inr y)).weight q = 0 := by
  classical
  rcases q with ⟨x,y'⟩
  dsimp at h
  simp only [revealProfile, gameConditionalKernel, toGameLaw, conditionalKernel]
  split
  · simp [revealFallback, FiniteDistribution.pushforward, Fintype.sum_prod_type,
      Prod.mk.injEq, Ne.symm h]
  · simp [revealLaw_weight, Ne.symm h]

def revealInputLaw (μ : FiniteDistribution (X × Y)) : FiniteDistribution (X ⊕ Y) :=
  (revealLaw μ).pushforward Prod.snd

theorem revealInputLaw_weight (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) :
    (revealInputLaw μ).weight r = firstMarginal (revealFirstLaw μ).weight r := by
  classical
  cases r <;>
    simp [revealInputLaw, FiniteDistribution.pushforward, firstMarginal, Fintype.sum_prod_type]

theorem reveal_profile_recombination (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (q : X × Y) :
    (revealInputLaw μ).weight r * (revealProfile μ r).weight q =
      (revealLaw μ).weight (q,r) := by
  rw [revealInputLaw_weight]
  exact gameConditionalKernel_recombine (revealFirstLaw μ) (revealFallback μ r) r q

theorem reveal_profile_inl_recombination (μ : FiniteDistribution (X × Y))
    (x : X) (q : X × Y) :
    (revealInputLaw μ).weight (Sum.inl x) * (revealProfile μ (Sum.inl x)).weight q =
      if x = q.1 then μ.weight q / 2 else 0 := by
  rw [reveal_profile_recombination, revealLaw_weight]
  simp

theorem reveal_profile_inr_recombination (μ : FiniteDistribution (X × Y))
    (y : Y) (q : X × Y) :
    (revealInputLaw μ).weight (Sum.inr y) * (revealProfile μ (Sum.inr y)).weight q =
      if y = q.2 then μ.weight q / 2 else 0 := by
  rw [reveal_profile_recombination, revealLaw_weight]
  simp

theorem revealInputLaw_inl (μ : FiniteDistribution (X × Y)) (x : X) :
    (revealInputLaw μ).weight (Sum.inl x) = (∑ y, μ.weight (x,y)) / 2 := by
  classical
  rw [revealInputLaw_weight]
  simp [firstMarginal, Fintype.sum_prod_type, revealLaw_weight, div_eq_mul_inv]
  rw [Finset.sum_comm]
  simp [← Finset.sum_mul]

theorem revealInputLaw_inr (μ : FiniteDistribution (X × Y)) (y : Y) :
    (revealInputLaw μ).weight (Sum.inr y) = (∑ x, μ.weight (x,y)) / 2 := by
  classical
  rw [revealInputLaw_weight]
  simp [firstMarginal, Fintype.sum_prod_type, revealLaw_weight,
    div_eq_mul_inv, ← Finset.sum_mul]

theorem revealProfile_inl_diagonal (μ : FiniteDistribution (X × Y)) (x : X) (y : Y) :
    (revealProfile μ (Sum.inl x)).weight (x,y) =
      conditionalKernel μ.weight (μ.pushforward Prod.snd).weight x y := by
  classical
  have hm : firstMarginal (revealFirstLaw μ).weight (Sum.inl x) =
      firstMarginal μ.weight x / 2 := by
    rw [← revealInputLaw_weight, revealInputLaw_inl]
    rfl
  have hf : (revealFallback μ (Sum.inl x)).weight (x,y) =
      (μ.pushforward Prod.snd).weight y := by
    simp [revealFallback, FiniteDistribution.pushforward, Prod.mk.injEq]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q.2 = y <;> simp [hq]
  simp only [revealProfile, gameConditionalKernel, toGameLaw, conditionalKernel, hm]
  by_cases h : firstMarginal μ.weight x = 0
  · simpa [h] using hf
  · have hh : firstMarginal μ.weight x / 2 ≠ 0 := div_ne_zero h (by norm_num)
    simp only [ite_eq_right h, ite_eq_right hh, revealFirstLaw_weight, revealLaw_weight,
      ite_true, Sum.inl_ne_inr, ite_false, add_zero]
    field_simp

theorem revealProfile_inr_diagonal (μ : FiniteDistribution (X × Y)) (x : X) (y : Y) :
    (revealProfile μ (Sum.inr y)).weight (x,y) =
      conditionalKernel (μ.transport (Equiv.prodComm X Y)).weight
        (μ.pushforward Prod.fst).weight y x := by
  classical
  have hm : firstMarginal (revealFirstLaw μ).weight (Sum.inr y) =
      firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y / 2 := by
    rw [← revealInputLaw_weight, revealInputLaw_inr]
    rfl
  have hf : (revealFallback μ (Sum.inr y)).weight (x,y) =
      (μ.pushforward Prod.fst).weight x := by
    simp [revealFallback, FiniteDistribution.pushforward, Prod.mk.injEq]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q.1 = x <;> simp [hq]
  simp only [revealProfile, gameConditionalKernel, toGameLaw, conditionalKernel, hm]
  by_cases h : firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y = 0
  · simpa [h] using hf
  · have hh : firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y / 2 ≠ 0 :=
      div_ne_zero h (by norm_num)
    simp only [ite_eq_right h, ite_eq_right hh, revealFirstLaw_weight, revealLaw_weight,
      ite_true, Sum.inr_ne_inl, ite_false, zero_add]
    change (μ.weight (x,y) / 2) / (firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y / 2) =
      μ.weight (x,y) / firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y
    field_simp

theorem revealLaw_sum_left (μ : FiniteDistribution (X × Y)) (q : X × Y) :
    (∑ x, (revealLaw μ).weight (q, Sum.inl x)) = μ.weight q / 2 := by
  classical
  simp [revealLaw_weight]

theorem revealLaw_sum_right (μ : FiniteDistribution (X × Y)) (q : X × Y) :
    (∑ y, (revealLaw μ).weight (q, Sum.inr y)) = μ.weight q / 2 := by
  classical
  simp [revealLaw_weight]

theorem revealLaw_forget (μ : FiniteDistribution (X × Y)) :
    (revealLaw μ).pushforward Prod.fst = μ := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro q
  rcases q with ⟨x,y⟩
  simp [FiniteDistribution.pushforward, Fintype.sum_prod_type,
    Finset.sum_ite_irrel, revealLaw_weight]

theorem reveal_product_factorization {ι : Type*} [Fintype ι]
    (μ : FiniteDistribution (X × Y)) (r : ι → X ⊕ Y) (q : ι → X × Y) :
    (∏ i, (revealInputLaw μ).weight (r i)) *
      (∏ i, (revealProfile μ (r i)).weight (q i)) =
        ∏ i, (revealLaw μ).weight (q i,r i) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact reveal_profile_recombination μ (r i) (q i)

theorem reveal_product_forget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : FiniteDistribution (X × Y)) (q : ι → X × Y) :
    (∑ r : ι → X ⊕ Y,
      (∏ i, (revealInputLaw μ).weight (r i)) *
        (∏ i, (revealProfile μ (r i)).weight (q i))) =
      ∏ i, μ.weight (q i) := by
  classical
  simp_rw [reveal_product_factorization]
  calc
    _ = ∏ i, ∑ r : X ⊕ Y, (revealLaw μ).weight (q i,r) :=
      (Fintype.prod_sum (fun (i : ι) (r : X ⊕ Y) => (revealLaw μ).weight (q i,r))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Fintype.sum_sum_type, revealLaw_sum_left, revealLaw_sum_right]
      ring

theorem reveal_product_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : FiniteDistribution (X × Y)) (f : (ι → X × Y) → ℝ) :
    (∑ r : ι → X ⊕ Y,
      (∏ i, (revealInputLaw μ).weight (r i)) *
        ∑ q : ι → X × Y, (∏ i, (revealProfile μ (r i)).weight (q i)) * f q) =
      ∑ q : ι → X × Y, (∏ i, μ.weight (q i)) * f q := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  rw [reveal_product_forget]

end
end IndependentSetsGames.Foundations.Repetition

end OAI
