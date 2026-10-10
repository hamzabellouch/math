import Mathlib

namespace OAI

open scoped BigOperators

namespace Balanced.DependencyExtraction

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β]

def coordinateSwap (i : α) : ((α → β) × β) ≃ ((α → β) × β) where
  toFun z := (Function.update z.1 i z.2, z.1 i)
  invFun z := (Function.update z.1 i z.2, z.1 i)
  left_inv z := by
    ext j
    · by_cases h : j = i <;> simp [h]
    · simp
  right_inv z := by
    ext j
    · by_cases h : j = i <;> simp [h]
    · simp

theorem expect_coordinate_refresh (i : α) (f : (α → β) → ℝ) :
    (𝔼 x, 𝔼 y, f (Function.update x i y)) = 𝔼 x, f x := by
  classical
  have hswap := Fintype.expect_equiv (coordinateSwap (β := β) i)
    (fun z : (α → β) × β => f (Function.update z.1 i z.2))
    (fun z : (α → β) × β => f z.1) (fun _ => rfl)
  have hprod₁ := Finset.expect_product' (Finset.univ : Finset (α → β))
    (Finset.univ : Finset β) (fun x y => f (Function.update x i y))
  have hprod₂ := Finset.expect_product' (Finset.univ : Finset (α → β))
    (Finset.univ : Finset β) (fun x (_ : β) => f x)
  simpa only [Finset.univ_product_univ, Fintype.expect_const] using
    hprod₁.symm.trans (hswap.trans hprod₂)

theorem expect_mul_le_of_coordinate_bound (i : α)
    (f g : (α → β) → ℝ) (p : ℝ)
    (hg : ∀ x, 0 ≤ g x)
    (hginv : ∀ x y, g (Function.update x i y) = g x)
    (hf : ∀ x, (𝔼 y, f (Function.update x i y)) ≤ p) :
    (𝔼 x, f x * g x) ≤ p * (𝔼 x, g x) := by
  classical
  rw [← expect_coordinate_refresh i (fun x => f x * g x)]
  calc
    (𝔼 x, 𝔼 y, f (Function.update x i y) * g (Function.update x i y))
        = 𝔼 x, (𝔼 y, f (Function.update x i y)) * g x := by
          apply Finset.expect_congr rfl
          intro x _
          simp_rw [hginv, Finset.expect_mul]
    _ ≤ 𝔼 x, p * g x := by
      apply Finset.expect_le_expect
      intro x _
      exact mul_le_mul_of_nonneg_right (hf x) (hg x)
    _ = p * (𝔼 x, g x) := (Finset.mul_expect _ _ _).symm

theorem expect_prod_le_of_ranked_dependencies
    (s : Finset α) (rank : α → ℕ) (f : α → (α → β) → ℝ) (p : α → ℝ)
    (hnonneg : ∀ i ∈ s, ∀ x, 0 ≤ f i x)
    (hp : ∀ i ∈ s, 0 ≤ p i)
    (hfiber : ∀ i ∈ s, ∀ x, (𝔼 y, f i (Function.update x i y)) ≤ p i)
    (hdep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → rank j ≤ rank i →
      ∀ x y, f i (Function.update x j y) = f i x) :
    (𝔼 x, ∏ i ∈ s, f i x) ≤ ∏ i ∈ s, p i := by
  classical
  revert hnonneg hp hfiber hdep
  refine Finset.strongInductionOn s ?_
  intro s ih hnonneg hp hfiber hdep
  by_cases hs : s = ∅
  · subst s
    simp
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image s rank
    (Finset.nonempty_iff_ne_empty.mpr hs)
  have hsub : s.erase a ⊆ s := Finset.erase_subset a s
  have hih : (𝔼 x, ∏ i ∈ s.erase a, f i x) ≤ ∏ i ∈ s.erase a, p i := by
    apply ih (s.erase a) (Finset.erase_ssubset ha)
    · exact fun i hi => hnonneg i (hsub hi)
    · exact fun i hi => hp i (hsub hi)
    · exact fun i hi => hfiber i (hsub hi)
    · exact fun i hi j hj => hdep i (hsub hi) j (hsub hj)
  have hg : ∀ x, 0 ≤ ∏ i ∈ s.erase a, f i x := by
    intro x
    exact Finset.prod_nonneg (fun i hi => hnonneg i (hsub hi) x)
  have hginv : ∀ x y,
      (∏ i ∈ s.erase a, f i (Function.update x a y)) =
        ∏ i ∈ s.erase a, f i x := by
    intro x y
    apply Finset.prod_congr rfl
    intro i hi
    exact hdep i (hsub hi) a ha (Finset.mem_erase.mp hi).1
      (hmin i (hsub hi)) x y
  calc
    (𝔼 x, ∏ i ∈ s, f i x)
        = 𝔼 x, f a x * ∏ i ∈ s.erase a, f i x := by
          apply Finset.expect_congr rfl
          intro x _
          exact (Finset.mul_prod_erase s (fun i => f i x) ha).symm
    _ ≤ p a * (𝔼 x, ∏ i ∈ s.erase a, f i x) :=
      expect_mul_le_of_coordinate_bound a (f a)
        (fun x => ∏ i ∈ s.erase a, f i x) (p a) hg hginv (hfiber a ha)
    _ ≤ p a * ∏ i ∈ s.erase a, p i := mul_le_mul_of_nonneg_left hih (hp a ha)
    _ = ∏ i ∈ s, p i := Finset.mul_prod_erase s p ha

theorem uniform_event_bound_of_ranked_dependencies
    (s : Finset α) (rank : α → ℕ) (E : α → (α → β) → Prop)
    [∀ i x, Decidable (E i x)] (p : ℝ) (hp : 0 ≤ p)
    (hfiber : ∀ i ∈ s, ∀ x,
      ((Finset.univ.filter (fun y => E i (Function.update x i y))).card : ℝ) /
        Fintype.card β ≤ p)
    (hdep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → rank j ≤ rank i →
      ∀ x y, E i (Function.update x j y) ↔ E i x) :
    ((Finset.univ.filter (fun x => ∀ i ∈ s, E i x)).card : ℝ) /
      Fintype.card (α → β) ≤ p ^ s.card := by
  classical
  have h := expect_prod_le_of_ranked_dependencies s rank
    (fun i x => if E i x then (1 : ℝ) else 0) (fun _ => p)
    (fun _ _ _ => by split_ifs <;> norm_num)
    (fun _ _ => hp) (fun i hi x => ?_) (fun i hi j hj hij hr x y => ?_)
  · have heq : ((Finset.univ.filter (fun x => ∀ i ∈ s, E i x)).card : ℝ) /
          Fintype.card (α → β) =
          𝔼 x, ∏ i ∈ s, (if E i x then (1 : ℝ) else 0) := by
      rw [Fintype.expect_eq_sum_div_card]
      congr 1
      rw [← Finset.sum_boole (R := ℝ) (fun x => ∀ i ∈ s, E i x) Finset.univ]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : ∀ i ∈ s, E i x <;> simp [Finset.prod_boole, hx]
    rw [heq]
    simpa only [Finset.prod_const] using h
  · simpa only [Fintype.expect_eq_sum_div_card, Finset.sum_boole] using hfiber i hi x
  · simp only [hdep i hi j hj hij hr x y]

theorem uniform_event_bound_of_dependency_relation
    (s : Finset α) (R : α → α → Prop) (rank : α → ℕ)
    (E : α → (α → β) → Prop) [∀ i x, Decidable (E i x)]
    (p : ℝ) (hp : 0 ≤ p)
    (hrank : ∀ i ∈ s, ∀ j ∈ s, R i j → rank i < rank j)
    (hfiber : ∀ i ∈ s, ∀ x,
      ((Finset.univ.filter (fun y => E i (Function.update x i y))).card : ℝ) /
        Fintype.card β ≤ p)
    (hsupport : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ R i j →
      ∀ x y, E i (Function.update x j y) ↔ E i x) :
    ((Finset.univ.filter (fun x => ∀ i ∈ s, E i x)).card : ℝ) /
      Fintype.card (α → β) ≤ p ^ s.card := by
  apply uniform_event_bound_of_ranked_dependencies s rank E p hp hfiber
  intro i hi j hj hij hji x y
  apply hsupport i hi j hj hij
  intro hijR
  exact (not_lt_of_ge hji) (hrank i hi j hj hijR)

theorem uniform_probability_eq_filter_card {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (E : Ω → Prop) [DecidablePred E] :
    ((PMF.uniformOfFintype Ω).toOuterMeasure {x | E x}).toReal =
      ((Finset.univ.filter E).card : ℝ) / Fintype.card Ω := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  change (Fintype.card {x : Ω // E x} : ℝ) / (Fintype.card Ω : ℝ) = _
  congr 2
  exact Fintype.card_subtype E

end Balanced.DependencyExtraction

end OAI
