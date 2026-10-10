import Mathlib
import OAI.Geometry.HyperbolicGroups.GeometricAction

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
open scoped BigOperators
namespace FiniteLaw
variable {α : Type*} [Fintype α]
/-- Product of the independent Bernoulli trials in the source table model. -/
def bernoulliProduct {I : Type*} [Fintype I] [DecidableEq I] (p : I → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) : FiniteLaw (I → Bool) where
  mass w := ∏ i, if w i then p i else 1 - p i
  nonneg w := Finset.prod_nonneg (fun i _ => by
    split_ifs
    · exact (hp i).1
    · exact sub_nonneg.mpr (hp i).2)
  sum_one := by
    rw [← Fintype.prod_sum (fun i (b : Bool) => if b then p i else 1 - p i)]
    simp

lemma bernoulliProduct_expect_product {I : Type*} [Fintype I] [DecidableEq I] (p : I → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (f : I → Bool → ℝ) :
    (bernoulliProduct p hp).expect (fun w => ∏ i, f i (w i)) =
      ∏ i, ((1 - p i) * f i false + p i * f i true) := by
  unfold expect bernoulliProduct
  simp only
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) => (if b then p i else 1 - p i) * f i b)]
  simp [add_comm]

/-- Probability of simultaneous inclusion for any specified, distinct trials. -/
lemma bernoulliProduct_all {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (s : Finset I) :
    (bernoulliProduct p hp).expect (fun w => if ∀ i ∈ s, w i = true then 1 else 0) =
      ∏ i ∈ s, p i := by
  classical
  have hprod (w : I → Bool) :
      (if ∀ i ∈ s, w i = true then (1 : ℝ) else 0) =
        ∏ i, if i ∈ s → w i = true then (1 : ℝ) else 0 := by
    rw [Fintype.prod_boole]
  rw [show (fun w : I → Bool => if ∀ i ∈ s, w i = true then (1 : ℝ) else 0) =
      (fun w => ∏ i, if i ∈ s → w i = true then (1 : ℝ) else 0) from funext hprod]
  rw [bernoulliProduct_expect_product p hp (fun i b => if i ∈ s → b = true then 1 else 0)]
  calc
    _ = ∏ i, if i ∈ s then p i else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases h : i ∈ s <;> simp [h]
    _ = ∏ i ∈ s, p i := by simp

/-- Probability, in real rather than ENNReal coordinates, of a finite event. -/
def prob (μ : FiniteLaw α) (E : α → Prop) [DecidablePred E] : ℝ :=
  μ.expect (fun a => if E a then 1 else 0)

lemma prob_nonneg (μ : FiniteLaw α) (E : α → Prop) [DecidablePred E] :
    0 ≤ μ.prob E := by
  unfold prob expect
  exact Finset.sum_nonneg fun a _ => mul_nonneg (μ.nonneg a) (by dsimp only; split_ifs <;> norm_num)

lemma prob_le_one (μ : FiniteLaw α) (E : α → Prop) [DecidablePred E] :
    μ.prob E ≤ 1 := by
  unfold prob expect
  calc
    _ ≤ ∑ a, μ.mass a := by
      apply Finset.sum_le_sum
      intro a _
      dsimp only
      split_ifs <;> simp [μ.nonneg]
    _ = 1 := μ.sum_one

/-- The finite union bound; no independence is assumed here. -/
lemma prob_exists_le {J : Type*} [Fintype J] (μ : FiniteLaw α)
    (E : J → α → Prop) [∀ j, DecidablePred (E j)] :
    μ.prob (fun a => ∃ j, E j a) ≤ ∑ j, μ.prob (E j) := by
  classical
  unfold prob expect
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (μ.nonneg a)
  by_cases h : ∃ j, E j a
  · obtain ⟨j, hj⟩ := h
    simp only [show ∃ j, E j a from ⟨j, hj⟩, ↓reduceIte]
    exact (Finset.single_le_sum (f := fun j => if E j a then (1 : ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ j)).trans' (by simp [hj])
  · simp only [h, ↓reduceIte]
    exact Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num

end FiniteLaw

namespace TableModel
variable {F R A : Type*} [Fintype F] [Fintype R] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq A]

/-- Each table has a distinct type, but all its coordinate fields use the same
alphabet. Coinciding numerical values at different fields are permitted. -/
abbrev Entry (support : R → Finset F) := Σ r, (support r → A)

def row (support : R → Finset F) (σ : F → A) (r : R) : Entry (A := A) support :=
  ⟨r, fun j => σ j⟩

omit [Fintype F] [Fintype R] [Fintype A] [DecidableEq F] [DecidableEq R] [DecidableEq A] in
lemma row_injective (support : R → Finset F) (σ : F → A) :
    Function.Injective (row support σ) := by
  intro r s he
  exact congrArg Sigma.fst he

def law (support : R → Finset F) (p : R → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) :
    FiniteLaw (Entry (A := A) support → Bool) :=
  FiniteLaw.bernoulliProduct (fun e => p e.1) (fun e => hp e.1)

def IsMatch (support : R → Finset F) (w : Entry (A := A) support → Bool)
    (σ : F → A) : Prop := ∀ r, w (row support σ r) = true

instance (support : R → Finset F) (w : Entry (A := A) support → Bool) (σ : F → A) :
    Decidable (IsMatch support w σ) := inferInstanceAs (Decidable (∀ r, w (row support σ r) = true))

omit [Fintype F] in
/-- A master assignment uses exactly one trial of each distinct array. Hence
its inclusion probability is independent of every letter value and collision. -/
theorem prob_isMatch (support : R → Finset F) (p : R → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (σ : F → A) :
    (law support p hp).prob (fun w => IsMatch support w σ) = ∏ r, p r := by
  classical
  have he (w : Entry (A := A) support → Bool) :
      IsMatch support w σ ↔ ∀ e ∈ Finset.univ.image (row support σ), w e = true := by
    simp [IsMatch]
  simp only [FiniteLaw.prob, he, law]
  rw [FiniteLaw.bernoulliProduct_all]
  rw [Finset.prod_image (fun _ _ _ _ heq => row_injective support σ heq)]
  rfl

/-- The number of master matches for the given finite table instance. -/
def matchCount (support : R → Finset F) (w : Entry (A := A) support → Bool) : ℕ :=
  (Finset.univ.filter (IsMatch support w)).card

/-- Exact first moment. No asymptotic approximation or injectivity restriction
on a match is involved, as in source Equation `sample:eq-master-mean`. -/
theorem expect_matchCount (support : R → Finset F) (p : R → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) :
    (law (A := A) support p hp).expect (fun w => (matchCount support w : ℝ)) =
      (Fintype.card A : ℝ) ^ Fintype.card F * ∏ r, p r := by
  classical
  have he (w : Entry (A := A) support → Bool) :
      (matchCount support w : ℝ) = ∑ σ : F → A, if IsMatch support w σ then 1 else 0 := by
    simp [matchCount]
  simp_rw [he]
  unfold FiniteLaw.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ σ : F → A, (∏ r, p r) := by
      apply Finset.sum_congr rfl
      intro σ _
      exact prob_isMatch support p hp σ
    _ = _ := by simp

end TableModel
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
open scoped BigOperators
namespace TableModel
variable {F R A : Type*} [Fintype F] [Fintype R] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq A]

/-- The common entries of two master assignments, counted by array type. -/
def overlapRows (support : R → Finset F) (σ τ : F → A) : Finset R :=
  Finset.univ.filter (fun r => row support σ r = row support τ r)

omit [Fintype F] [Fintype A] [DecidableEq F] in
lemma overlap_image (support : R → Finset F) (σ τ : F → A) :
    (Finset.univ.image (row support σ)) ∩ (Finset.univ.image (row support τ)) =
      (overlapRows support σ τ).image (row support σ) := by
  classical
  ext e
  simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and,
    overlapRows, Finset.mem_filter]
  constructor
  · rintro ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
    have hrs : r = s := congrArg Sigma.fst (hr.trans hs.symm)
    subst s
    exact ⟨r, hr.trans hs.symm, hr⟩
  · rintro ⟨r, he, hr⟩
    exact ⟨⟨r, hr⟩, ⟨r, he.symm.trans hr⟩⟩

omit [Fintype F] in
/-- Exact joint-inclusion identity, retaining the recoverable cost of every
shared entry. Different fields with equal numerical values are not identified. -/
theorem prob_pair_mul_overlap (support : R → Finset F) (p : R → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (σ τ : F → A) :
    (law support p hp).prob (fun w => IsMatch support w σ ∧ IsMatch support w τ) *
      (∏ r ∈ overlapRows support σ τ, p r) = (∏ r, p r) ^ 2 := by
  classical
  have he (w : Entry (A := A) support → Bool) :
      (IsMatch support w σ ∧ IsMatch support w τ) ↔
      ∀ e ∈ Finset.univ.image (row support σ) ∪ Finset.univ.image (row support τ),
        w e = true := by
    simp only [IsMatch, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hσ, hτ⟩ e (⟨r, hr⟩ | ⟨r, hr⟩)
      · simpa only [← hr] using hσ r
      · simpa only [← hr] using hτ r
    · intro hh
      exact ⟨fun r => hh _ (Or.inl ⟨r, rfl⟩), fun r => hh _ (Or.inr ⟨r, rfl⟩)⟩
  simp only [FiniteLaw.prob, he, law]
  rw [FiniteLaw.bernoulliProduct_all]
  have hov : (∏ e ∈ (Finset.univ.image (row support σ)) ∩
      (Finset.univ.image (row support τ)), p e.1) =
      ∏ r ∈ overlapRows support σ τ, p r := by
    rw [overlap_image, Finset.prod_image (fun _ _ _ _ h => row_injective support σ h)]
    rfl
  rw [← hov, Finset.prod_union_inter,
    Finset.prod_image (fun _ _ _ _ h => row_injective support σ h),
    Finset.prod_image (fun _ _ _ _ h => row_injective support τ h)]
  simp [row, pow_two]

omit [Fintype F] in
/-- Inclusion ratio agrees exactly with the product of reciprocal shared-entry
probabilities. Positivity is retained, rather than silently cancelling zero. -/
theorem prob_pair (support : R → Finset F) (p : R → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (hpos : ∀ r, 0 < p r) (σ τ : F → A) :
    (law support p hp).prob (fun w => IsMatch support w σ ∧ IsMatch support w τ) =
      (∏ r, p r) ^ 2 / (∏ r ∈ overlapRows support σ τ, p r) := by
  apply (eq_div_iff (ne_of_gt (Finset.prod_pos (fun r _ => hpos r)))).mpr
  exact prob_pair_mul_overlap support p hp σ τ

/-- Turning the square of the match count into ordered pairs is exact for every
finite table instance. -/
theorem expect_matchCount_sq (support : R → Finset F) (p : R → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) :
    (law (A := A) support p hp).expect (fun w => (matchCount support w : ℝ) ^ 2) =
      ∑ σ : F → A, ∑ τ : F → A,
        (law support p hp).prob (fun w => IsMatch support w σ ∧ IsMatch support w τ) := by
  classical
  have hc (w : Entry (A := A) support → Bool) :
      (matchCount support w : ℝ) ^ 2 =
      ∑ σ : F → A, ∑ τ : F → A, if IsMatch support w σ ∧ IsMatch support w τ then 1 else 0 := by
    have hcount : (matchCount support w : ℝ) =
        ∑ σ : F → A, if IsMatch support w σ then 1 else 0 := by simp [matchCount]
    rw [hcount, pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro τ _
    by_cases hσ : IsMatch support w σ <;> by_cases hτ : IsMatch support w τ <;> simp [hσ, hτ]
  simp_rw [hc]
  unfold FiniteLaw.prob FiniteLaw.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.sum_comm]

end TableModel
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
open scoped BigOperators
namespace TableModel
variable {F R A : Type*} [Fintype F] [Fintype R] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq A]

/-- Coincidence counting uses equality only within each coordinate field;
the letters in other fields range independently over the very same alphabet. -/
lemma sum_coincidence (σ : F → A) (W : Finset F) :
    (∑ τ : F → A, if ∀ i ∈ W, τ i = σ i then (1 : ℝ) else 0) =
      (Fintype.card A : ℝ) ^ (Fintype.card F - W.card) := by
  classical
  have he (τ : F → A) :
      (if ∀ i ∈ W, τ i = σ i then (1 : ℝ) else 0) =
      ∏ i, if i ∈ W → τ i = σ i then (1 : ℝ) else 0 := by
    rw [Fintype.prod_boole]
  simp_rw [he]
  rw [← Fintype.prod_sum (fun i (a : A) => if i ∈ W → a = σ i then (1 : ℝ) else 0)]
  calc
    _ = ∏ i : F, if i ∈ W then (1 : ℝ) else Fintype.card A := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ W <;> simp [hi]
    _ = _ := by
      rw [Finset.prod_ite]
      simp [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.subset_univ W)]

omit [Fintype F] [Fintype R] [Fintype A] [DecidableEq F] [DecidableEq R] [DecidableEq A] in
lemma row_eq_iff (support : R → Finset F) (σ τ : F → A) (r : R) :
    row support σ r = row support τ r ↔ ∀ i ∈ support r, σ i = τ i := by
  classical
  simp only [row, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  constructor
  · intro he i hi
    exact congrFun he ⟨i, hi⟩
  · intro he
    exact funext fun i => he i i.property

omit [Fintype F] [Fintype R] [Fintype A] [DecidableEq R] [DecidableEq A] in
lemma rows_eq_iff (support : R → Finset F) (σ τ : F → A) (J : Finset R) :
    (∀ r ∈ J, row support σ r = row support τ r) ↔
      ∀ i ∈ J.biUnion support, σ i = τ i := by
  classical
  simp only [row_eq_iff, Finset.mem_biUnion]
  constructor
  · rintro hh i ⟨r, hr, hi⟩
    exact hh r hr i hi
  · intro hh r hr i hi
    exact hh i ⟨r, hr, hi⟩

omit [Fintype A] in
/-- Exact expansion of the pair-inclusion ratio by subsets of the shared
row types. This form permits counting prescribed coordinate equalities rather
than making an incorrect disjoint-domain assumption. -/
lemma inverse_overlap_expansion (support : R → Finset F) (p : R → ℝ)
    (σ τ : F → A) :
    (∏ r ∈ overlapRows support σ τ, p r)⁻¹ =
      ∑ J : Finset R, if ∀ i ∈ J.biUnion support, σ i = τ i then
        ∏ r ∈ J, ((p r)⁻¹ - 1) else 0 := by
  classical
  calc
    _ = ∏ r : R, (1 + if row support σ r = row support τ r then (p r)⁻¹ - 1 else 0) := by
      rw [← Finset.prod_inv_distrib]
      simp only [overlapRows, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro r _
      split_ifs <;> ring
    _ = ∑ J ∈ (Finset.univ : Finset R).powerset,
        ∏ r ∈ J, if row support σ r = row support τ r then (p r)⁻¹ - 1 else 0 := by
      rw [Finset.prod_one_add]
    _ = _ := by
      simp only [Finset.powerset_univ]
      apply Finset.sum_congr rfl
      intro J _
      simp only [← rows_eq_iff]
      by_cases hh : ∀ r ∈ J, row support σ r = row support τ r
      · rw [ite_eq_left hh]
        exact Finset.prod_congr rfl fun r hr => ite_eq_left (hh r hr)
      · simp only [hh, ↓reduceIte]
        push Not at hh
        obtain ⟨r, hr, he⟩ := hh
        exact Finset.prod_eq_zero hr (by simp [he])

/-- Summing the exact overlap identity over the second assignment. -/
lemma sum_inverse_overlap (support : R → Finset F) (p : R → ℝ) (σ : F → A) :
    (∑ τ : F → A, (∏ r ∈ overlapRows support σ τ, p r)⁻¹) =
      ∑ J : Finset R, (Fintype.card A : ℝ) ^ (Fintype.card F - (J.biUnion support).card) *
        ∏ r ∈ J, ((p r)⁻¹ - 1) := by
  classical
  simp_rw [inverse_overlap_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  rw [← sum_coincidence σ (J.biUnion support), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro τ _
  have hh : (∀ i ∈ J.biUnion support, σ i = τ i) ↔
      ∀ i ∈ J.biUnion support, τ i = σ i := by simp only [eq_comm]
  simp only [hh]
  split_ifs <;> simp

end TableModel
end HyperbolicObstruction
end
end
end
end

section

end
end

end OAI
