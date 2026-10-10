import Mathlib
import OAI.Computability.DirectedFeedback.RankGraph.CellCount

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem acceptance_le_mul_budget (f : (I → Bool) → Bool) (hf : Monotone f)
    (h0 : f (fun _ => false) = false) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (law p hp0 hp1).probability f ≤ p * budget f := by
  have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := acceptance f) (f' := totalInfluence f) (s := Set.Icc 0 p)
    (C := budget f)
    (fun q _ => (russo f q).hasDerivWithinAt)
    (fun q hq => by
      rw [Real.norm_eq_abs, abs_of_nonneg (influence_nonneg f hf q hq.1 (hq.2.trans hp1))]
      exact influence_le_budget f hf q hq.1 (hq.2.trans hp1))
    (convex_Icc (0 : ℝ) p) (show (0 : ℝ) ∈ Set.Icc 0 p from ⟨le_rfl, hp0⟩)
    (show p ∈ Set.Icc 0 p from ⟨hp0, le_rfl⟩)
  rw [acceptance_zero f h0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hp0, acceptance_eq_probability f p hp0 hp1,
    abs_of_nonneg (FiniteDistribution.probability_nonnegative _ _)] at hbound
  simpa [mul_comm] using hbound

end DirectedFeedback.Pivotal

namespace DirectedFeedback.SourceProbability.FiniteDistribution
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]

theorem probability_or_le_add (μ : FiniteDistribution I) (p q : I → Bool) :
    μ.probability (fun i => p i || q i) ≤ μ.probability p + μ.probability q := by
  unfold probability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  cases hp : p i <;> cases hq : q i <;> simp [hp, hq, μ.nonnegative]

theorem probability_exists_le_sum (μ : FiniteDistribution I) (p : J → I → Bool) :
    μ.probability (fun i => decide (∃ j, p j i = true)) ≤ ∑ j, μ.probability (p j) := by
  classical
  unfold probability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  by_cases h : ∃ j, p j i = true
  · obtain ⟨j, hj⟩ := h
    have he : ∃ j, p j i = true := ⟨j, hj⟩
    simp only [decide_eq_true_eq, he, ↓reduceIte]
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => if p j i then μ.weight i else 0)
      (fun j _ => by split_ifs <;> simp [μ.nonnegative]) (Finset.mem_univ j)
    simpa [hj] using hh
  · simp only [decide_eq_true_eq, h, ↓reduceIte]
    exact Finset.sum_nonneg (fun j _ => by split_ifs <;> simp [μ.nonnegative])

theorem probability_not (μ : FiniteDistribution I) (p : I → Bool) :
    μ.probability (fun i => !(p i)) = 1 - μ.probability p := by
  rw [← μ.normalized]
  unfold probability
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hp : p i <;> simp [hp]

theorem indicator_difference (μ : FiniteDistribution I) (p q : I → Bool)
    (hpq : ∀ i, p i = true → q i = true) :
    μ.probability (fun i => decide (p i ≠ q i)) = μ.probability q - μ.probability p := by
  unfold probability
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hp : p i <;> cases hq : q i <;> simp_all

theorem probability_disagree_triangle (μ : FiniteDistribution I) (p q r : I → Bool) :
    μ.probability (fun i => decide (p i ≠ r i)) ≤
      μ.probability (fun i => decide (p i ≠ q i)) +
      μ.probability (fun i => decide (q i ≠ r i)) := by
  calc
    _ ≤ μ.probability (fun i => decide (p i ≠ q i) || decide (q i ≠ r i)) := by
      apply probability_mono
      intro i hi
      simp only [decide_eq_true_eq, Bool.or_eq_true] at *
      by_cases h : p i = q i
      · exact Or.inr (fun hh => hi (h.trans hh))
      · exact Or.inl h
    _ ≤ _ := probability_or_le_add _ _ _

theorem probability_abs_sub_le_disagree (μ : FiniteDistribution I) (p q : I → Bool) :
    |μ.probability p - μ.probability q| ≤ μ.probability (fun i => decide (p i ≠ q i)) := by
  unfold probability
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(if p i then μ.weight i else 0) - (if q i then μ.weight i else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      cases hp : p i <;> cases hq : q i <;> simp [hp, hq, abs_of_nonneg (μ.nonnegative i)]

theorem pair_event_disagree (μ : FiniteDistribution I) (p p' q q' : I → Bool) :
    |μ.probability (fun i => p i && q i) - μ.probability (fun i => p' i && q' i)| ≤
      μ.probability (fun i => decide (p i ≠ p' i)) +
      μ.probability (fun i => decide (q i ≠ q' i)) := by
  apply (probability_abs_sub_le_disagree μ _ _).trans
  calc
    _ ≤ μ.probability (fun i => decide (p i ≠ p' i) || decide (q i ≠ q' i)) := by
      apply probability_mono
      intro i hi
      simp only [decide_eq_true_eq, Bool.or_eq_true] at *
      by_contra hn
      push Not at hn
      exact hi (by rw [hn.1, hn.2])
    _ ≤ _ := probability_or_le_add _ _ _

end DirectedFeedback.SourceProbability.FiniteDistribution

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]

def point (a : I) : FiniteDistribution I where
  weight x := if x = a then 1 else 0
  nonnegative x := by split_ifs <;> norm_num
  normalized := by simp

@[simp] theorem expectation_point (a : I) (f : I → ℝ) :
    (point a).expectation f = f a := by simp [expectation, point]

@[simp] theorem expectation_sub (μ : FiniteDistribution I) (f g : I → ℝ) :
    μ.expectation (fun x => f x - g x) = μ.expectation f - μ.expectation g := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem expectation_mul_right (μ : FiniteDistribution I) (f : I → ℝ) (c : ℝ) :
    μ.expectation (fun x => f x * c) = μ.expectation f * c := by
  simpa only [mul_comm] using expectation_mul_left μ c f

@[simp] theorem probability_eq_expect (μ : FiniteDistribution I) (p : I → Bool) :
    μ.probability p = μ.expectation (fun x => if p x then 1 else 0) := by
  simp [probability, expectation, mul_ite]

def sigma {F : I → Type*} [∀ i, Fintype (F i)] (μ : FiniteDistribution I)
    (ν : ∀ i, FiniteDistribution (F i)) : FiniteDistribution (Σ i, F i) where
  weight x := μ.weight x.1 * (ν x.1).weight x.2
  nonnegative x := mul_nonneg (μ.nonnegative _) ((ν _).nonnegative _)
  normalized := by
    rw [Fintype.sum_sigma]
    simp only [← Finset.mul_sum, (ν _).normalized, mul_one, μ.normalized]

theorem expectation_sigma {F : I → Type*} [∀ i, Fintype (F i)] (μ : FiniteDistribution I)
    (ν : ∀ i, FiniteDistribution (F i)) (f : (Σ i, F i) → ℝ) :
    (μ.sigma ν).expectation f = μ.expectation (fun i => (ν i).expectation (fun x => f ⟨i, x⟩)) := by
  simp only [expectation, sigma, Fintype.sum_sigma, Finset.mul_sum, mul_assoc]

def bind (μ : FiniteDistribution I) (ν : I → FiniteDistribution J) : FiniteDistribution J :=
  (μ.sigma ν).pushforward Sigma.snd

theorem expectation_bind (μ : FiniteDistribution I) (ν : I → FiniteDistribution J) (f : J → ℝ) :
    (μ.bind ν).expectation f = μ.expectation (fun i => (ν i).expectation f) := by
  rw [bind, expectation_pushforward, expectation_sigma]

theorem expectation_transport (μ : FiniteDistribution I) (e : I ≃ J) (f : J → ℝ) :
    (μ.transport e).expectation f = μ.expectation (fun i => f (e i)) := by
  unfold expectation
  apply Fintype.sum_equiv e.symm
  intro j
  simp only [transport, Equiv.apply_symm_apply]

theorem uniform_transport [Nonempty I] [Nonempty J] (e : I ≃ J) :
    (uniform I).transport e = uniform J := by
  apply eq_of_weight_eq
  intro j
  simp only [transport, uniform, Fintype.card_congr e]

theorem uniform_pushforward [Nonempty I] [Nonempty J] (e : I ≃ J) :
    (uniform I).pushforward e = uniform J := by
  apply eq_of_weight_eq
  intro j
  simp only [pushforward, uniform]
  calc
    _ = ∑ y : J, if y = j then 1 / (Fintype.card I : ℝ) else 0 :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := by simp [Fintype.card_congr e]

theorem uniform_product [Nonempty I] [Nonempty J] :
    (uniform I).product (uniform J) = uniform (I × J) := by
  apply eq_of_weight_eq
  intro x
  simp [product, uniform, Fintype.card_prod, Nat.cast_mul, mul_comm]

theorem probability_ge_atom (μ : FiniteDistribution I) (event : I → Bool) (a : I)
    (h : event a = true) : μ.weight a ≤ μ.probability event := by
  calc
    _ = (if event a then μ.weight a else 0) := by simp [h]
    _ ≤ _ := by
      unfold probability
      exact Finset.single_le_sum (f := fun i => if event i then μ.weight i else 0)
        (fun i _ => by cases event i <;> simp [μ.nonnegative]) (Finset.mem_univ a)

theorem probability_uniform [Nonempty I] (event : I → Bool) :
    (uniform I).probability event =
      ((Finset.univ.filter (fun i => event i = true)).card : ℝ) / Fintype.card I := by
  simp [probability, uniform, ← Finset.sum_filter, div_eq_mul_inv]

theorem expectation_table_pair {F : Type*} [Fintype F] [DecidableEq F]
    (α : I → FiniteDistribution J) (β : F → FiniteDistribution K)
    (i : I) (k : F) (f : J → K → ℝ) :
    (table α).expectation (fun x => (table β).expectation (fun y => f (x i) (y k))) =
      (α i).expectation (fun x => (β k).expectation (f x)) := by
  simp_rw [expectation_table_eval]
  exact expectation_table_eval α i (fun x => (β k).expectation (f x))

theorem probability_product_pattern (μ : FiniteDistribution I) (ν : FiniteDistribution J)
    (f : I → Bool) (g : J → Bool) :
    (μ.product ν).probability (fun x => f x.1 && !(g x.2)) =
      μ.probability f * (1 - ν.probability g) := by
  rw [probability_eq_expect, expectation_product]
  simp_rw [show ∀ i j, (if f i && !(g j) then (1 : ℝ) else 0) =
    (if f i then 1 else 0) * (if !(g j) then 1 else 0) by
      intro i j; cases f i <;> cases g j <;> norm_num]
  simp_rw [expectation_mul_left, ← probability_eq_expect, expectation_mul_right, probability_not]
  rw [probability_eq_expect μ f]

theorem markov_bound (μ : FiniteDistribution I) (B : I → ℝ) (hB : ∀ i, 0 ≤ B i)
    (c : ℝ) (hc : 0 < c) :
    μ.probability (fun i => decide (c < B i)) ≤ μ.expectation B / c := by
  apply (le_div_iff₀ hc).mpr
  rw [probability_eq_expect, ← expectation_mul_right]
  apply expectation_mono
  intro i
  by_cases hi : c < B i
  · simpa [hi] using hi.le
  · simpa [hi] using hB i

end DirectedFeedback.SourceProbability.FiniteDistribution

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}

def insertOrder (j : I) (r : Fin (n+1)) (e : {i : I // i ≠ j} ≃ Fin n) : I ≃ Fin (n+1) :=
  (Equiv.optionSubtypeNe j).symm |>.trans (Equiv.optionCongr e) |>.trans (finSuccEquiv' r).symm

omit [Fintype I] in
@[simp] theorem insertOrder_self (j : I) (r : Fin (n+1)) (e : {i : I // i ≠ j} ≃ Fin n) :
    insertOrder j r e j = r := by
  simp [insertOrder]

omit [Fintype I] in
@[simp] theorem insertOrder_other (j : I) (r : Fin (n+1)) (e : {i : I // i ≠ j} ≃ Fin n)
    (x : {i : I // i ≠ j}) : insertOrder j r e x = r.succAbove (e x) := by
  simp [insertOrder, Equiv.optionSubtypeNe_symm_of_ne x.property]

def deleteOrder (j : I) (e : I ≃ Fin (n+1)) : {i : I // i ≠ j} ≃ Fin n :=
  (e.subtypeEquiv (fun _ => not_congr e.injective.eq_iff.symm)).trans (finSuccAboveEquiv (e j)).symm

omit [Fintype I] [DecidableEq I] in
theorem deleteOrder_spec (j : I) (e : I ≃ Fin (n+1)) (x : {i : I // i ≠ j}) :
    (e j).succAbove (deleteOrder j e x) = e x := by
  have h := (finSuccAboveEquiv (e j)).apply_symm_apply
    (⟨e x, fun h => x.property (e.injective h)⟩ : {y : Fin (n+1) // y ≠ e j})
  exact congrArg Subtype.val h

omit [Fintype I] in
@[simp] theorem insert_delete_order (j : I) (e : I ≃ Fin (n+1)) :
    insertOrder j (e j) (deleteOrder j e) = e := by
  apply Equiv.ext
  intro x
  by_cases hx : x = j
  · subst x; simp
  · exact (insertOrder_other j (e j) (deleteOrder j e) ⟨x,hx⟩).trans (deleteOrder_spec j e ⟨x,hx⟩)

omit [Fintype I] in
@[simp] theorem delete_insert_order (j : I) (r : Fin (n+1)) (e : {i : I // i ≠ j} ≃ Fin n) :
    deleteOrder j (insertOrder j r e) = e := by
  apply Equiv.ext
  intro x
  have h := deleteOrder_spec j (insertOrder j r e) x
  simp only [insertOrder_self, insertOrder_other] at h
  exact Fin.succAbove_right_injective h

def orderDecomposition (j : I) : (I ≃ Fin (n+1)) ≃ Fin (n+1) × ({i : I // i ≠ j} ≃ Fin n) where
  toFun e := (e j, deleteOrder j e)
  invFun q := insertOrder j q.1 q.2
  left_inv e := insert_delete_order j e
  right_inv q := by rcases q with ⟨r,e⟩; simp

def orderHit {J : Type*} [Fintype J] (event : (J → Bool) → Bool)
    (e : J ≃ Fin (Fintype.card J)) : Bool :=
  decide (∃ r ≤ Fintype.card J, event (fun x => decide ((e x).val < r)) = true)

def omittedHit (j : I) (event : ({i : I // i ≠ j} → Bool) → Bool)
    (e : I ≃ Fin (Fintype.card {i : I // i ≠ j} + 1)) : Bool :=
  decide (∃ r ≤ Fintype.card {i : I // i ≠ j} + 1,
    event (fun x => decide ((e x).val < r)) = true)

theorem succAbove_cut_forward (r : Fin (n+1)) (q : ℕ) (x : Fin n) :
    (r.succAbove x).val < (if q ≤ r.val then q else q+1) ↔ x.val < q := by
  unfold Fin.succAbove
  split_ifs <;> simp_all only [Fin.val_castSucc, Fin.val_succ, Fin.lt_def] <;> omega

theorem succAbove_cut_backward (r : Fin (n+1)) (q : ℕ) (x : Fin n) :
    (r.succAbove x).val < q ↔ x.val < (if q ≤ r.val then q else q-1) := by
  unfold Fin.succAbove
  split_ifs <;> simp_all only [Fin.val_castSucc, Fin.val_succ, Fin.lt_def] <;> omega

theorem omittedHit_insert (j : I) (event : ({i : I // i ≠ j} → Bool) → Bool)
    (r : Fin (Fintype.card {i : I // i ≠ j} + 1))
    (e : {i : I // i ≠ j} ≃ Fin (Fintype.card {i : I // i ≠ j})) :
    omittedHit j event (insertOrder j r e) = orderHit event e := by
  apply Bool.eq_iff_iff.mpr
  simp only [omittedHit, orderHit, decide_eq_true_eq]
  constructor
  · rintro ⟨q,hq,he⟩
    refine ⟨if q ≤ r.val then q else q-1, by split_ifs <;> omega, ?_⟩
    convert he using 1
    congr 1
    funext x
    simp only [insertOrder_other, succAbove_cut_backward]
  · rintro ⟨q,hq,he⟩
    refine ⟨if q ≤ r.val then q else q+1, by split_ifs <;> omega, ?_⟩
    convert he using 1
    congr 1
    funext x
    simp only [insertOrder_other, succAbove_cut_forward]

def permutationOrder (J : Type*) [Fintype J] : Equiv.Perm J ≃ (J ≃ Fin (Fintype.card J)) where
  toFun σ := σ.symm.trans (Fintype.equivFin J)
  invFun e := (e.trans (Fintype.equivFin J).symm).symm
  left_inv σ := by ext j; simp
  right_inv e := by ext j; simp

theorem orderHit_permutation {J : Type*} [Fintype J] (event : (J → Bool) → Bool) (σ : Equiv.Perm J) :
    orderHit event (permutationOrder J σ) = chainHit event σ := rfl

instance nonemptyOrder (J : Type*) [Fintype J] : Nonempty (J ≃ Fin (Fintype.card J)) :=
  ⟨Fintype.equivFin J⟩

theorem uniform_deleting (j : I) (event : ({i : I // i ≠ j} → Bool) → Bool) :
    let : Nonempty (I ≃ Fin (Fintype.card {i : I // i ≠ j} + 1)) :=
      ⟨insertOrder j 0 (Fintype.equivFin _)⟩
    (uniform (I ≃ Fin (Fintype.card {i : I // i ≠ j} + 1))).probability (omittedHit j event) =
      chainBudget event := by
  let : Nonempty (I ≃ Fin (Fintype.card {i : I // i ≠ j} + 1)) :=
    ⟨insertOrder j 0 (Fintype.equivFin _)⟩
  change (uniform _).probability (omittedHit j event) = chainBudget event
  rw [probability_eq_expect]
  rw [← uniform_transport (orderDecomposition j).symm, expectation_transport]
  rw [← uniform_product, expectation_product]
  change (uniform (Fin (Fintype.card {i : I // i ≠ j} + 1))).expectation
    (fun r => (uniform ({i : I // i ≠ j} ≃ Fin (Fintype.card {i : I // i ≠ j}))).expectation
      (fun e => if omittedHit j event (insertOrder j r e) then 1 else 0)) = _
  simp only [omittedHit_insert, expectation_const]
  rw [← uniform_transport (permutationOrder {i : I // i ≠ j}), expectation_transport]
  exact (probability_eq_expect _ _).symm

end DirectedFeedback.Pivotal

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype Ω]

abbrev LabelOrder (I : Type*) [Fintype I] [DecidableEq I] :=
  Σ j : I, I ≃ Fin (Fintype.card {i : I // i ≠ j}+1)

instance labelOrderNonempty (j : I) : Nonempty (I ≃ Fin (Fintype.card {i : I // i ≠ j}+1)) :=
  ⟨insertOrder j 0 (Fintype.equivFin _)⟩

def labelOrderLaw : FiniteDistribution (LabelOrder I) :=
  (uniform I).sigma (fun _ => uniform _)

theorem labelOrder_hit_probability (f : (I → Bool) → Bool) :
    labelOrderLaw.probability (fun a : LabelOrder I => omittedHit a.1 (pivotalEvent f a.1) a.2) =
      budget f / Fintype.card I := by
  rw [probability_eq_expect, labelOrderLaw, expectation_sigma]
  simp_rw [← probability_eq_expect, uniform_deleting]
  rw [expectation_uniform]
  simp only [budget, div_eq_mul_inv, mul_comm]

theorem single_label_budget_charge (f : (I → Bool) → Bool) (deleted : LabelOrder I → Bool)
    (hforce : ∀ a, omittedHit a.1 (pivotalEvent f a.1) a.2 = true → deleted a = true) :
    budget f ≤ Fintype.card I * labelOrderLaw.probability deleted := by
  have hm := probability_mono (μ := labelOrderLaw) hforce
  rw [labelOrder_hit_probability] at hm
  have hc : (0:ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  exact (div_le_iff₀ hc).mp hm |>.trans_eq (mul_comm _ _)

omit [Nonempty I] in
theorem budget_nonneg (f : (I → Bool) → Bool) : 0 ≤ budget f := by
  exact Finset.sum_nonneg (fun _ _ => probability_nonnegative _ _)

omit [Nonempty I] in
theorem budget_le_card (f : (I → Bool) → Bool) : budget f ≤ Fintype.card I := by
  calc
    _ ≤ ∑ _ : I, (1:ℝ) := Finset.sum_le_sum (fun _ _ => probability_le_one _ _)
    _ = Fintype.card I := by simp

theorem averaged_budget_charge (μ : FiniteDistribution Ω) (f : Ω → (I → Bool) → Bool)
    (good : Ω → Bool) (deleted : Ω → LabelOrder I → Bool)
    (D ρ : ℝ) (hρ : Fintype.card I * ρ ≤ 1)
    (hbad : μ.probability (fun a => !(good a)) ≤ ρ)
    (hcost : Fintype.card I * μ.expectation (fun a => labelOrderLaw.probability (deleted a)) ≤ D)
    (hforce : ∀ a, good a = true → ∀ o,
      omittedHit o.1 (pivotalEvent (f a) o.1) o.2 = true → deleted a o = true) :
    μ.expectation (fun a => budget (f a)) ≤ D+1 := by
  have hb (a : Ω) : budget (f a) ≤
      Fintype.card I * labelOrderLaw.probability (deleted a) +
      Fintype.card I * (if !(good a) then 1 else 0 : ℝ) := by
    cases hg : good a
    · simp only [Bool.not_false, ↓reduceIte, mul_one]
      have hp := probability_nonnegative labelOrderLaw (deleted a)
      have hc : (0:ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
      have h := budget_le_card (f a)
      nlinarith
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero]
      exact single_label_budget_charge (f a) (deleted a) (hforce a hg)
  have hm := expectation_mono μ hb
  rw [expectation_add, expectation_mul_left, expectation_mul_left, ← probability_eq_expect] at hm
  have hc : (0:ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hbad hc]

end DirectedFeedback.Pivotal

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {I : Type*} [Fintype I]

def splitSnoc (T : ℕ) : (Fin (T+1) → I) ≃ ((Fin T → I) × I) where
  toFun a := (Fin.init a, a (Fin.last T))
  invFun a := Fin.snoc a.1 a.2
  left_inv a := by funext i; exact Fin.lastCases (by simp) (fun j => by simp [Fin.init]) i
  right_inv a := by rcases a with ⟨a,x⟩; simp

theorem iid_snoc_transport (μ : FiniteDistribution I) (T : ℕ) :
    (μ.iid (T+1)).transport (splitSnoc T) = (μ.iid T).product μ := by
  apply eq_of_weight_eq
  intro a
  change (∏ t : Fin (T+1), μ.weight ((Fin.snoc a.1 a.2 : Fin (T+1) → I) t)) =
    (∏ t : Fin T, μ.weight (a.1 t)) * μ.weight a.2
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem expectation_iid_snoc (μ : FiniteDistribution I) (T : ℕ) (f : (Fin (T+1) → I) → ℝ) :
    (μ.iid (T+1)).expectation f =
      (μ.iid T).expectation (fun a => μ.expectation (fun x => f (Fin.snoc a x))) := by
  have h := expectation_transport (μ.iid (T+1)) (splitSnoc T)
    (fun a => f (Fin.snoc a.1 a.2))
  rw [iid_snoc_transport, expectation_product] at h
  simpa only [splitSnoc, Equiv.coe_fn_mk, Fin.snoc_init_self] using h.symm

def takePrefix {t T : ℕ} (h : t ≤ T) (a : Fin T → I) : Fin t → I :=
  fun i => a ⟨i.val, lt_of_lt_of_le i.isLt h⟩

omit [Fintype I] in
@[simp] theorem takePrefix_self {t : ℕ} (a : Fin t → I) : takePrefix le_rfl a = a := rfl

omit [Fintype I] in
theorem take_snoc_eq {t T : ℕ} (h : t ≤ T) (a : Fin T → I) (x : I) :
    takePrefix (by omega : t ≤ T+1) (Fin.snoc a x) = takePrefix h a := by
  funext i
  change (Fin.snoc a x : Fin (T+1) → I) ((Fin.castLE h i).castSucc) = a (Fin.castLE h i)
  simp only [Fin.snoc_castSucc]

theorem expectation_iid_take (μ : FiniteDistribution I) {t T : ℕ} (h : t ≤ T)
    (f : (Fin t → I) → ℝ) :
    (μ.iid T).expectation (fun a => f (takePrefix h a)) = (μ.iid t).expectation f := by
  induction T with
  | zero =>
    have ht : t = 0 := by omega
    subst t
    rfl
  | succ T ih =>
    by_cases ht : t ≤ T
    · rw [expectation_iid_snoc]
      simp_rw [take_snoc_eq ht, expectation_const]
      exact ih ht
    · have he : t = T+1 := by omega
      subst t
      simp

theorem expectation_iid_prefix_fresh (μ : FiniteDistribution I) {t T : ℕ} (h : t < T)
    (f : (Fin t → I) → I → ℝ) :
    (μ.iid T).expectation (fun a => f (takePrefix (by omega) a) (a ⟨t,h⟩)) =
      (μ.iid t).expectation (fun a => μ.expectation (f a)) := by
  have hh := expectation_iid_take μ (show t+1 ≤ T by omega)
    (fun a => f (Fin.init a) (a (Fin.last t)))
  rw [expectation_iid_snoc] at hh
  simp only [Fin.init_snoc, Fin.snoc_last] at hh
  exact hh

end DirectedFeedback.SourceProbability.FiniteDistribution

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.PrefixExperiment
open DirectedFeedback.SourceProbability FiniteDistribution
variable {U I P Ω : Type*} [Fintype U] [Fintype I] [Nonempty I] [Fintype P] [Fintype Ω]

abbrev Atom (U I P : Type*) := U × (Σ _ : I, P)

def atomLaw (μ : FiniteDistribution U) (ν : I → FiniteDistribution P) :
    FiniteDistribution (Atom U I P) := μ.product ((uniform I).sigma ν)

theorem fresh_index_expectation (μ : FiniteDistribution U) (ν : I → FiniteDistribution P)
    (i : I) (f : U → P → ℝ) :
    (atomLaw μ ν).expectation (fun a => if a.2.1 = i then f a.1 a.2.2 else 0) =
      (1 / Fintype.card I) * μ.expectation (fun u => (ν i).expectation (f u)) := by
  rw [atomLaw, expectation_product]
  simp_rw [expectation_sigma, expectation_uniform]
  have hh (u : U) : (∑ j : I, (ν j).expectation (fun p => if j = i then f u p else 0)) =
      (ν i).expectation (f u) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  simp_rw [hh]
  rw [← expectation_mul_left]
  apply congrArg (expectation μ)
  funext u
  ring

def commonLaw (μΩ : FiniteDistribution Ω) (μ : FiniteDistribution U)
    (ν : I → FiniteDistribution P) (T : ℕ) [NeZero T] :
    FiniteDistribution (Ω × (Σ t : Fin T, Fin t.val → Atom U I P)) :=
  μΩ.product ((uniform (Fin T)).sigma (fun t => (atomLaw μ ν).iid t.val))

def count (i : I) {T : ℕ} (f : Ω → (t : ℕ) → (Fin t → Atom U I P) → U → P → ℝ)
    (ω : Ω) (a : Fin T → Atom U I P) : ℝ :=
  ∑ t : Fin T, if (a t).2.1 = i then
    f ω t.val (takePrefix (Nat.le_of_lt t.isLt) a) (a t).1 (a t).2.2 else 0

def acceptance (μ : FiniteDistribution U) (ν : I → FiniteDistribution P) (i : I)
    (f : Ω → (t : ℕ) → (Fin t → Atom U I P) → U → P → ℝ)
    {T : ℕ} (d : Ω × (Σ t : Fin T, Fin t.val → Atom U I P)) : ℝ :=
  μ.expectation (fun u => (ν i).expectation (f d.1 d.2.1.val d.2.2 u))

theorem full_count_expectation (μΩ : FiniteDistribution Ω) (μ : FiniteDistribution U)
    (ν : I → FiniteDistribution P) (i : I) (T : ℕ) [NeZero T]
    (f : Ω → (t : ℕ) → (Fin t → Atom U I P) → U → P → ℝ) :
    (μΩ.product ((atomLaw μ ν).iid T)).expectation (fun a => count i f a.1 a.2) =
      ((T : ℝ) / Fintype.card I) * (commonLaw μΩ μ ν T).expectation (acceptance μ ν i f) := by
  rw [expectation_product]
  simp only [count]
  simp_rw [expectation_sum]
  have ht (ω : Ω) (t : Fin T) :
      ((atomLaw μ ν).iid T).expectation (fun a =>
        if (a t).2.1 = i then f ω t.val (takePrefix (Nat.le_of_lt t.isLt) a)
          (a t).1 (a t).2.2 else 0) =
      (1 / Fintype.card I) * ((atomLaw μ ν).iid t.val).expectation
        (fun a => μ.expectation (fun u => (ν i).expectation (f ω t.val a u))) := by
    rw [expectation_iid_prefix_fresh (atomLaw μ ν) t.isLt
      (fun a q => if q.2.1 = i then f ω t.val a q.1 q.2.2 else 0)]
    simp_rw [fresh_index_expectation, expectation_mul_left]
  simp_rw [ht]
  rw [commonLaw, expectation_product]
  simp_rw [expectation_sigma, expectation_uniform, acceptance]
  rw [← expectation_mul_left, ← expectation_sum]
  apply congrArg (expectation μΩ)
  funext ω
  rw [← Finset.mul_sum]
  simp only [Fintype.card_fin]
  have hT : (T : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne T
  field_simp

theorem acceptance_lower_bound (μΩ : FiniteDistribution Ω) (μ : FiniteDistribution U)
    (ν : I → FiniteDistribution P) (i : I) (T : ℕ) [NeZero T]
    (f : Ω → (t : ℕ) → (Fin t → Atom U I P) → U → P → ℝ)
    (p : ℝ) (hp : 0 ≤ p) (favorable : Ω × (Fin T → Atom U I P) → Bool)
    (hf : ∀ ω t a u q, 0 ≤ f ω t a u q)
    (hprob : 1/2 ≤ (μΩ.product ((atomLaw μ ν).iid T)).probability favorable)
    (hcount : ∀ a, favorable a = true →
      p * T / (2 * Fintype.card I) ≤ count i f a.1 a.2) :
    p/4 ≤ (commonLaw μΩ μ ν T).expectation (acceptance μ ν i f) := by
  have hM : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hT : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T)
  have hnn (a : Ω × (Fin T → Atom U I P)) : 0 ≤ count i f a.1 a.2 := by
    apply Finset.sum_nonneg
    intro t _
    split_ifs <;> simp [hf]
  have hh := expectation_mono (μ := μΩ.product ((atomLaw μ ν).iid T))
    (f := fun a => (p * T / (2 * Fintype.card I)) * if favorable a then 1 else 0)
    (g := fun a => count i f a.1 a.2) (fun a => by
      cases ha : favorable a
      · simpa [ha] using hnn a
      · simpa [ha] using hcount a ha)
  rw [expectation_mul_left, ← probability_eq_expect, full_count_expectation] at hh
  have hmul := mul_le_mul_of_nonneg_left hprob
    (show 0 ≤ p * T / (2 * Fintype.card I) from by positivity)
  have hk : (p * T / (2 * Fintype.card I)) * (1/2) = (T / Fintype.card I) * (p/4) := by ring
  rw [hk] at hmul
  exact (mul_le_mul_iff_right₀ (div_pos hT hM)).mp (hmul.trans hh)

end DirectedFeedback.PrefixExperiment

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {I B C D : Type*} [Fintype I] [Fintype B]

def Uses (S : Finset I) (f : (I → B) → C) : Prop :=
  ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y

def splice (S : Finset I) (x y : I → B) : I → B :=
  fun i => if i ∈ S then x i else y i

def splicePair (S : Finset I) : ((I → B) × (I → B)) ≃ ((I → B) × (I → B)) where
  toFun z := (splice S z.1 z.2, splice S z.2 z.1)
  invFun z := (splice S z.1 z.2, splice S z.2 z.1)
  left_inv z := by ext i <;> by_cases hi : i ∈ S <;> simp [splice, hi]
  right_inv z := by ext i <;> by_cases hi : i ∈ S <;> simp [splice, hi]

theorem splicePair_weight (α : I → FiniteDistribution B) (S : Finset I)
    (z : (I → B) × (I → B)) :
    ((table α).product (table α)).weight (splicePair S z) =
      ((table α).product (table α)).weight z := by
  change (∏ i, (α i).weight (splice S z.1 z.2 i)) *
    (∏ i, (α i).weight (splice S z.2 z.1 i)) =
    (∏ i, (α i).weight (z.1 i)) * (∏ i, (α i).weight (z.2 i))
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp [splice, hi, mul_comm]

theorem expectation_splicePair (α : I → FiniteDistribution B) (S : Finset I)
    (h : ((I → B) × (I → B)) → ℝ) :
    ((table α).product (table α)).expectation (fun z => h (splicePair S z)) =
      ((table α).product (table α)).expectation h := by
  unfold expectation
  apply Fintype.sum_equiv (splicePair S)
  intro z
  rw [splicePair_weight]

theorem expectation_disjoint (α : I → FiniteDistribution B) (S T : Finset I)
    (hST : Disjoint S T) (f g : (I → B) → ℝ) (hf : Uses S f) (hg : Uses T g) :
    (table α).expectation (fun x => f x * g x) =
      (table α).expectation f * (table α).expectation g := by
  have hs (z : (I → B) × (I → B)) : f (splice S z.1 z.2) = f z.1 := by
    apply hf
    intro i hi
    simp [splice, hi]
  have ht (z : (I → B) × (I → B)) : g (splice S z.1 z.2) = g z.2 := by
    apply hg
    intro i hi
    have hn : i ∉ S := fun hx => Finset.disjoint_left.mp hST hx hi
    simp [splice, hn]
  calc
    _ = ((table α).product (table α)).expectation (fun z => f z.1 * g z.1) := by
      rw [expectation_product]
      simp only [expectation_const]
    _ = ((table α).product (table α)).expectation
        (fun z => f (splice S z.1 z.2) * g (splice S z.1 z.2)) :=
      (expectation_splicePair α S (fun z => f z.1 * g z.1)).symm
    _ = ((table α).product (table α)).expectation (fun z => f z.1 * g z.2) := by
      apply expectation_congr
      intro z
      rw [hs, ht]
    _ = _ := by rw [expectation_product]; simp only [expectation_mul_left, expectation_mul_right]

theorem probability_disjoint_pattern (α : I → FiniteDistribution B) (S T : Finset I)
    (hST : Disjoint S T) (f g : (I → B) → Bool) (hf : Uses S f) (hg : Uses T g) :
    (table α).probability (fun x => f x && !(g x)) =
      (table α).probability f * (1 - (table α).probability g) := by
  rw [probability_eq_expect]
  have hid : (fun x => if f x && !(g x) then (1 : ℝ) else 0) =
      fun x => (if f x then 1 else 0) * (if !(g x) then 1 else 0) := by
    funext x
    cases f x <;> cases g x <;> norm_num
  rw [hid, expectation_disjoint α S T hST]
  · rw [← probability_eq_expect, ← probability_eq_expect, probability_not]
  · intro x y hxy
    dsimp only
    rw [hf x y hxy]
  · intro x y hxy
    dsimp only
    rw [hg x y hxy]

end DirectedFeedback.SourceProbability.FiniteDistribution

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Coupling
open DirectedFeedback.SourceProbability FiniteDistribution
open Pivotal
variable {X Y : Type*} [Fintype X] [Fintype Y]

abbrev Block := (Bool × Bool) × Bool

def blockWeight (p : ℝ) : Block → ℝ
  | ((false, false), false) => 1 - 2*p
  | ((false, false), true) => p^2
  | ((false, true), true) => p*(1-p)
  | ((true, false), true) => p*(1-p)
  | ((true, true), true) => p^2
  | _ => 0

def block (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2) : FiniteDistribution Block where
  weight := blockWeight p
  nonnegative z := by
    rcases z with ⟨⟨a,b⟩,c⟩
    have h1 : 0 ≤ 1-p := by linarith
    cases a <;> cases b <;> cases c <;> simp [blockWeight] <;> nlinarith [mul_nonneg hp0 h1]
  normalized := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, blockWeight]
    ring

theorem block_big (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2) :
    (block p hp0 hp).pushforward Prod.fst =
      (coin p hp0 (by linarith)).product (coin p hp0 (by linarith)) := by
  apply eq_of_weight_eq
  rintro ⟨a,b⟩
  cases a <;> cases b <;>
    simp [pushforward, block, blockWeight, coin, product, Fintype.sum_prod_type] <;> ring

theorem block_small (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2) :
    (block p hp0 hp).pushforward Prod.snd = coin (2*p) (by positivity) (by linarith) := by
  apply eq_of_weight_eq
  intro b
  cases b with
  | false => simp [pushforward, block, blockWeight, coin, Fintype.sum_prod_type]
  | true => simp [pushforward, block, blockWeight, coin, Fintype.sum_prod_type]; ring

theorem block_inclusion (p : ℝ) (z : Block) (hz : blockWeight p z ≠ 0) :
    z.1.1 = true ∨ z.1.2 = true → z.2 = true := by
  rcases z with ⟨⟨a,b⟩,c⟩
  cases a <;> cases b <;> cases c <;> simp_all [blockWeight]

def flatten (e : X ≃ Y × Bool) : (Y → Bool × Bool) ≃ (X → Bool) where
  toFun z x := if (e x).2 then (z (e x).1).2 else (z (e x).1).1
  invFun a y := (a (e.symm (y,false)), a (e.symm (y,true)))
  left_inv z := by ext y <;> simp
  right_inv a := by
    ext x
    generalize hx : e x = z
    rcases z with ⟨y,b⟩
    have hh : e.symm (y,b) = x := by rw [← hx]; simp
    dsimp only
    rw [hx]
    cases b <;> simpa using congrArg a hh

def bigBits (e : X ≃ Y × Bool) (z : Y → Block) : X → Bool :=
  flatten e (fun y => (z y).1)

def smallBits (z : Y → Block) : Y → Bool := fun y => (z y).2

def law (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2) : FiniteDistribution (Y → Block) :=
  table (fun _ => block p hp0 hp)

theorem flatten_weight (e : X ≃ Y × Bool) (μ : FiniteDistribution Bool) (z : Y → Bool × Bool) :
    (table (fun _ : X => μ)).weight (flatten e z) =
      (table (fun _ : Y => μ.product μ)).weight z := by
  change (∏ x, μ.weight (flatten e z x)) = ∏ y, μ.weight (z y).1 * μ.weight (z y).2
  calc
    _ = ∏ q : Y × Bool, μ.weight (if q.2 then (z q.1).2 else (z q.1).1) :=
      e.prod_comp _
    _ = _ := by rw [Fintype.prod_prod_type]; simp [mul_comm]

theorem flatten_expectation (e : X ≃ Y × Bool) (μ : FiniteDistribution Bool)
    (f : (X → Bool) → ℝ) :
    (table (fun _ : Y => μ.product μ)).expectation (fun z => f (flatten e z)) =
      (table (fun _ : X => μ)).expectation f := by
  unfold expectation
  apply Fintype.sum_equiv (flatten e)
  intro z
  rw [flatten_weight]

theorem big_expectation (e : X ≃ Y × Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (f : (X → Bool) → ℝ) :
    (law p hp0 hp).expectation (fun z => f (bigBits e z)) =
      (Pivotal.law p hp0 (by linarith)).expectation f := by
  unfold law bigBits
  rw [← expectation_pushforward (table (fun _ : Y => block p hp0 hp))
    (fun z y => (z y).1) (fun a => f (flatten e a)), table_pushforward]
  simp only [block_big]
  exact flatten_expectation e (coin p hp0 _) f

theorem small_expectation (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (f : (Y → Bool) → ℝ) :
    (law p hp0 hp).expectation (fun z => f (smallBits z)) =
      (Pivotal.law (2*p) (by positivity) (by linarith)).expectation f := by
  unfold law smallBits
  rw [← expectation_pushforward (table (fun _ : Y => block p hp0 hp))
    (fun z y => (z y).2) f, table_pushforward]
  simp only [block_small, Pivotal.law]

theorem big_probability (e : X ≃ Y × Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (f : (X → Bool) → Bool) :
    (law p hp0 hp).probability (fun z => f (bigBits e z)) =
      (Pivotal.law p hp0 (by linarith)).probability f := by
  simp only [probability_eq_expect]
  exact big_expectation e p hp0 hp (fun a => if f a then 1 else 0)

theorem small_probability (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (f : (Y → Bool) → Bool) :
    (law p hp0 hp).probability (fun z => f (smallBits z)) =
      (Pivotal.law (2*p) (by positivity) (by linarith)).probability f := by
  simp only [probability_eq_expect]
  exact small_expectation p hp0 hp (fun a => if f a then 1 else 0)

theorem disjoint_pattern (e : X ≃ Y × Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (J : Finset X) (K : Finset Y) (hJK : Disjoint (J.image (fun x => (e x).1)) K)
    (f : (X → Bool) → Bool) (g : (Y → Bool) → Bool) (hf : Uses J f) (hg : Uses K g) :
    (law p hp0 hp).probability (fun z => f (bigBits e z) && !(g (smallBits z))) =
      (Pivotal.law p hp0 (by linarith)).probability f *
        (1 - (Pivotal.law (2*p) (by positivity) (by linarith)).probability g) := by
  have hu : Uses (J.image (fun x => (e x).1)) (fun z => f (bigBits e z)) := by
    intro z w hzw
    apply hf
    intro x hx
    have h := hzw (e x).1 (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    simp only [bigBits, flatten, Equiv.coe_fn_mk, h]
  have hv : Uses K (fun z => g (smallBits z)) := by
    intro z w hzw
    apply hg
    intro y hy
    exact congrArg Prod.snd (hzw y hy)
  rw [show (law p hp0 hp) = table (fun _ : Y => block p hp0 hp) from rfl,
    probability_disjoint_pattern _ _ _ hJK _ _ hu hv]
  rw [← show (law p hp0 hp) = table (fun _ : Y => block p hp0 hp) from rfl,
    big_probability, small_probability]

end DirectedFeedback.Coupling

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Games
open DirectedFeedback.SourceProbability
open FiniteDistribution
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

structure Game (U V E X Y : Type) [Fintype E] where
  edgeLaw : FiniteDistribution E
  left : E → U
  right : E → V
  project : E → X → Y

def Game.score (G : Game U V E X Y) (lu : U → X) (lv : V → Y) : ℝ :=
  G.edgeLaw.probability (fun e => decide (G.project e (lu (G.left e)) = lv (G.right e)))

def Game.Sound (G : Game U V E X Y) (θ : ℝ) : Prop :=
  ∀ lu lv, G.score lu lv ≤ θ

def listChoice (S : Finset X) : FiniteDistribution X :=
  if h : S.Nonempty then
    { weight := fun x => if x ∈ S then 1 / (S.card : ℝ) else 0
      nonnegative := fun x => by split_ifs <;> positivity
      normalized := by
        rw [← Finset.sum_filter]
        rw [show Finset.univ.filter (fun x => x ∈ S) = S by ext x; simp]
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hz : (S.card : ℝ) ≠ 0 := by exact_mod_cast h.card_pos.ne'
        field_simp }
  else point (Classical.choice ‹Nonempty X›)

end DirectedFeedback.Games
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
