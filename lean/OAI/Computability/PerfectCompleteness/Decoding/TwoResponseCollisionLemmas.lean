import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import OAI.Computability.UniqueGames.Foundations.KernelSampling
import OAI.Computability.UniqueGames.Foundations.ValueLemmas

namespace OAI


namespace PerfectCompleteness.TwoResponseCollision

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Ω Y : Type*} [Fintype Ω] [Fintype Y]

def responds (f : Ω → Option Y) (good : Ω → Bool) (y : Y) (x : Ω) : Bool :=
  good x && decide (f x = some y)

def goodDefined (f : Ω → Option Y) (good : Ω → Bool) (x : Ω) : Bool :=
  good x && (f x).isSome

def collision (f : Ω → Option Y) (p : Ω × Ω) : Bool :=
  decide (∃ y, f p.1 = some y ∧ f p.2 = some y)

def goodCollision (f : Ω → Option Y) (good : Ω → Bool) (p : Ω × Ω) : Bool :=
  good p.1 && good p.2 && collision f p

def GoodResponse (f : Ω → Option Y) (good : Ω → Bool) (y : Y) : Prop :=
  ∃ x, good x = true ∧ f x = some y

def responseMass (μ : FiniteDistribution Ω) (f : Ω → Option Y)
    (good : Ω → Bool) (y : Y) : ℝ :=
  μ.probability (responds f good y)

theorem goodDefined_weight_eq_sum (μ : FiniteDistribution Ω) (f : Ω → Option Y)
    (good : Ω → Bool) (x : Ω) :
    (if goodDefined f good x then μ.weight x else 0) =
      ∑ y, if responds f good y x then μ.weight x else 0 := by
  cases hg : good x <;> cases hf : f x <;>
    simp [goodDefined, responds, hg, hf, eq_comm]

theorem goodDefined_probability_eq_sum (μ : FiniteDistribution Ω)
    (f : Ω → Option Y) (good : Ω → Bool) :
    μ.probability (goodDefined f good) = ∑ y, responseMass μ f good y := by
  change (∑ x, if goodDefined f good x then μ.weight x else 0) =
    ∑ y, ∑ x, if responds f good y x then μ.weight x else 0
  simp_rw [goodDefined_weight_eq_sum]
  exact Finset.sum_comm

theorem goodCollision_weight_eq_sum (μ : FiniteDistribution Ω) (f : Ω → Option Y)
    (good : Ω → Bool) (x x' : Ω) :
    (if goodCollision f good (x, x') then μ.weight x * μ.weight x' else 0) =
      ∑ y, (if responds f good y x then μ.weight x else 0) *
        (if responds f good y x' then μ.weight x' else 0) := by
  cases hg : good x <;> cases hg' : good x' <;>
    cases hf : f x <;> cases hf' : f x' <;>
    simp [goodCollision, collision, responds, hg, hg', hf, hf', ite_mul, mul_ite, eq_comm]

theorem goodCollision_probability_eq_sum_sq (μ : FiniteDistribution Ω)
    (f : Ω → Option Y) (good : Ω → Bool) :
    (μ.product μ).probability (goodCollision f good) =
      ∑ y, responseMass μ f good y ^ 2 := by
  change (∑ p : Ω × Ω,
    if goodCollision f good p then μ.weight p.1 * μ.weight p.2 else 0) = _
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ x, ∑ x', ∑ y,
        (if responds f good y x then μ.weight x else 0) *
          (if responds f good y x' then μ.weight x' else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro x' _
      exact goodCollision_weight_eq_sum μ f good x x'
    _ = ∑ x, ∑ y, ∑ x',
        (if responds f good y x then μ.weight x else 0) *
          (if responds f good y x' then μ.weight x' else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = ∑ y, ∑ x, ∑ x',
        (if responds f good y x then μ.weight x else 0) *
          (if responds f good y x' then μ.weight x' else 0) := Finset.sum_comm
    _ = ∑ y, responseMass μ f good y ^ 2 := by
      apply Finset.sum_congr rfl
      intro y _
      change (∑ x, ∑ x',
        (if responds f good y x then μ.weight x else 0) *
          (if responds f good y x' then μ.weight x' else 0)) =
        (∑ x, if responds f good y x then μ.weight x else 0) ^ 2
      rw [← Finset.sum_mul_sum, pow_two]

omit [Fintype Y] in
theorem responseMass_eq_zero_of_not_goodResponse (μ : FiniteDistribution Ω)
    (f : Ω → Option Y) (good : Ω → Bool) (y : Y)
    (hy : ¬GoodResponse f good y) : responseMass μ f good y = 0 := by
  unfold responseMass FiniteDistribution.probability
  apply Finset.sum_eq_zero
  intro x _
  by_cases hg : good x = true
  · have hf : f x ≠ some y := fun hf => hy ⟨x, hg, hf⟩
    simp [responds, hg, hf]
  · simp [responds, hg]

theorem sum_sq_bound_of_support_card_le_two (q : Y → ℝ) (R : Y → Prop)
    (hzero : ∀ y, ¬R y → q y = 0)
    (hcard : Nat.card {y : Y // R y} ≤ 2) :
    (∑ y, q y) ^ 2 ≤ 2 * ∑ y, q y ^ 2 := by
  let S : Finset Y := Finset.univ.filter R
  have hsum : (∑ y ∈ S, q y) = ∑ y, q y := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro y _ hy
    exact hzero y (by simpa [S] using hy)
  have hsumSq : (∑ y ∈ S, q y ^ 2) = ∑ y, q y ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro y _ hy
    rw [hzero y (by simpa [S] using hy)]
    norm_num
  have hcardNat : S.card ≤ 2 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_subtype, S] using hcard
  have hcardReal : (S.card : ℝ) ≤ 2 := by exact_mod_cast hcardNat
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ : Y => (1 : ℝ)) q
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  rw [hsum, hsumSq] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_right hcardReal
    (Finset.sum_nonneg (fun y _ => sq_nonneg (q y))))

theorem goodCollision_probability_ge (μ : FiniteDistribution Ω)
    (f : Ω → Option Y) (good : Ω → Bool)
    (hcard : Nat.card {y : Y // GoodResponse f good y} ≤ 2) :
    μ.probability (goodDefined f good) ^ 2 / 2 ≤
      (μ.product μ).probability (goodCollision f good) := by
  rw [goodDefined_probability_eq_sum, goodCollision_probability_eq_sum_sq]
  have h := sum_sq_bound_of_support_card_le_two (responseMass μ f good)
    (GoodResponse f good) (responseMass_eq_zero_of_not_goodResponse μ f good) hcard
  linarith

theorem collision_probability_ge (μ : FiniteDistribution Ω)
    (f : Ω → Option Y) (good : Ω → Bool)
    (hcard : Nat.card {y : Y // GoodResponse f good y} ≤ 2) :
    μ.probability (goodDefined f good) ^ 2 / 2 ≤
      (μ.product μ).probability (collision f) := by
  apply (goodCollision_probability_ge μ f good hcard).trans
  apply FiniteDistribution.probability_mono
  intro p hp
  exact (Bool.and_eq_true_iff.mp hp).2

theorem collision_probability_ge_of_response_set (μ : FiniteDistribution Ω)
    (f : Ω → Option Y) (good : Ω → Bool) (R : Y → Prop)
    (hcard : Nat.card {y : Y // R y} ≤ 2)
    (hR : ∀ x y, good x = true → f x = some y → R y) :
    μ.probability (goodDefined f good) ^ 2 / 2 ≤
      (μ.product μ).probability (collision f) := by
  let into : {y : Y // GoodResponse f good y} → {y : Y // R y} := fun y =>
    ⟨y.val, by
      obtain ⟨x, hg, hf⟩ := y.property
      exact hR x y.val hg hf⟩
  have hi : Function.Injective into := by
    intro y y' h
    exact Subtype.ext (congrArg (fun z : {y : Y // R y} => z.val) h)
  apply collision_probability_ge μ f good
  exact (Nat.card_le_card_of_injective into hi).trans hcard

theorem collision_probability_ge_of_good_defined (μ : FiniteDistribution Ω)
    (f : Ω → Option Y) (good : Ω → Bool)
    (hdefined : ∀ x, good x = true → ∃ y, f x = some y)
    (hcard : Nat.card {y : Y // GoodResponse f good y} ≤ 2) :
    μ.probability good ^ 2 / 2 ≤ (μ.product μ).probability (collision f) := by
  have hevent : goodDefined f good = good := by
    funext x
    cases hg : good x with
    | false => simp [goodDefined, hg]
    | true =>
      obtain ⟨y, hy⟩ := hdefined x hg
      simp [goodDefined, hg, hy]
  simpa only [hevent] using collision_probability_ge μ f good hcard

end
end PerfectCompleteness.TwoResponseCollision



namespace PerfectCompleteness.DecoderTableAdmissibility

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

section FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem event_of_probability_one (μ : FiniteDistribution Ω) (event : Ω → Bool)
    (hone : μ.probability event = 1) (x : Ω) (hx : μ.weight x ≠ 0) :
    event x = true := by
  by_contra hfalse
  have hle (y : Ω) : (if event y then μ.weight y else 0) ≤ μ.weight y := by
    split
    · exact le_rfl
    · exact μ.nonnegative y
  have hlt : μ.probability event < ∑ y, μ.weight y := by
    unfold FiniteDistribution.probability
    apply Finset.sum_lt_sum (fun y _ => hle y)
    refine ⟨x, Finset.mem_univ _, ?_⟩
    simpa only [ite_eq_right hfalse] using
      lt_of_le_of_ne (μ.nonnegative x) (Ne.symm hx)
  have hbad : (1 : ℝ) < 1 := by simpa only [hone, μ.normalized] using hlt
  exact (lt_irrefl (1 : ℝ)) hbad

theorem probability_one_of_support (μ : FiniteDistribution Ω) (event : Ω → Bool)
    (hevent : ∀ x, μ.weight x ≠ 0 → event x = true) : μ.probability event = 1 := by
  rw [← μ.normalized]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : μ.weight x = 0
  · simp [hx]
  · simp only [hevent x hx, ite_true]

theorem expectation_le_of_support (μ : FiniteDistribution Ω) (score : Ω → ℝ)
    (bound : ℝ) (hbound : ∀ x, μ.weight x ≠ 0 → score x ≤ bound) :
    μ.expectation score ≤ bound := by
  calc
    _ ≤ ∑ x, μ.weight x * bound := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : μ.weight x = 0
      · simp only [hx, zero_mul, le_refl]
      · exact mul_le_mul_of_nonneg_left (hbound x hx) (μ.nonnegative x)
    _ = bound := by rw [← Finset.sum_mul, μ.normalized, one_mul]

end FiniteLaw

variable {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q]

def RowValid (valid : Q → A → Prop) (q : Q) (answer : Option A) : Prop :=
  ∀ a, answer = some a → valid q a

def Admissible (valid : Q → A → Prop) (answers : Q → Option A) : Prop :=
  ∀ q a, answers q = some a → valid q a

theorem table_admissible_of_support (responses : Q → FiniteDistribution (Option A))
    (valid : Q → A → Prop)
    (hvalid : ∀ q a, (responses q).weight (some a) ≠ 0 → valid q a)
    (answers : Q → Option A) (hanswers : (FiniteDistribution.table responses).weight answers ≠ 0) :
    Admissible valid answers := by
  intro q a ha
  apply hvalid q a
  have hrow := FiniteDistribution.table_row_weight_ne_zero responses answers hanswers q
  simpa only [ha] using hrow

omit [Fintype Q] [DecidableEq Q] in
theorem row_valid_of_probability_one (responses : Q → FiniteDistribution (Option A))
    (valid : Q → A → Prop)
    (hvalid : ∀ q, (responses q).probability (fun answer => decide (RowValid valid q answer)) = 1)
    (q : Q) (a : A) (ha : (responses q).weight (some a) ≠ 0) : valid q a := by
  have h := event_of_probability_one (responses q)
    (fun answer => decide (RowValid valid q answer)) (hvalid q) (some a) ha
  exact (of_decide_eq_true h) a rfl

theorem table_admissible_of_probability_one (responses : Q → FiniteDistribution (Option A))
    (valid : Q → A → Prop)
    (hvalid : ∀ q, (responses q).probability (fun answer => decide (RowValid valid q answer)) = 1)
    (answers : Q → Option A) (hanswers : (FiniteDistribution.table responses).weight answers ≠ 0) :
    Admissible valid answers :=
  table_admissible_of_support responses valid
    (row_valid_of_probability_one responses valid hvalid) answers hanswers

theorem table_admissible_probability_one (responses : Q → FiniteDistribution (Option A))
    (valid : Q → A → Prop)
    (hvalid : ∀ q, (responses q).probability (fun answer => decide (RowValid valid q answer)) = 1) :
    (FiniteDistribution.table responses).probability
      (fun answers => decide (Admissible valid answers)) = 1 := by
  apply probability_one_of_support
  intro answers hanswers
  exact decide_eq_true
    (table_admissible_of_probability_one responses valid hvalid answers hanswers)

theorem table_erased_of_support (responses : Q → FiniteDistribution (Option A))
    (erased : Q → Prop)
    (herased : ∀ q, erased q → ∀ a, (responses q).weight (some a) = 0)
    (answers : Q → Option A) (hanswers : (FiniteDistribution.table responses).weight answers ≠ 0)
    (q : Q) (hq : erased q) : answers q = none := by
  cases ha : answers q with
  | none => rfl
  | some a =>
      have hrow := FiniteDistribution.table_row_weight_ne_zero responses answers hanswers q
      rw [ha, herased q hq a] at hrow
      exact False.elim (hrow rfl)

theorem table_erased_of_probability_one (responses : Q → FiniteDistribution (Option A))
    (erased : Q → Prop)
    (herased : ∀ q, erased q →
      (responses q).probability (fun answer => decide (answer = none)) = 1)
    (answers : Q → Option A) (hanswers : (FiniteDistribution.table responses).weight answers ≠ 0)
    (q : Q) (hq : erased q) : answers q = none := by
  exact of_decide_eq_true (event_of_probability_one (responses q)
    (fun answer => decide (answer = none)) (herased q hq) (answers q)
    (FiniteDistribution.table_row_weight_ne_zero responses answers hanswers q))

def eraseTable (erased : Q → Prop) (answers : Q → Option A) (q : Q) : Option A :=
  if erased q then none else answers q

omit [Fintype Q] [Fintype A] [DecidableEq Q] in
theorem eraseTable_admissible (valid : Q → A → Prop) (erased : Q → Prop)
    (answers : Q → Option A) (hanswers : Admissible valid answers) :
    Admissible valid (eraseTable erased answers) := by
  intro q a ha
  by_cases hq : erased q
  · simp only [eraseTable, ite_eq_left hq, reduceCtorEq] at ha
  · exact hanswers q a (by simpa only [eraseTable, ite_eq_right hq] using ha)

theorem eraseTable_eq_of_support (responses : Q → FiniteDistribution (Option A))
    (erased : Q → Prop)
    (herased : ∀ q, erased q → ∀ a, (responses q).weight (some a) = 0)
    (answers : Q → Option A) (hanswers : (FiniteDistribution.table responses).weight answers ≠ 0) :
    eraseTable erased answers = answers := by
  funext q
  by_cases hq : erased q
  · simpa only [eraseTable, ite_eq_left hq] using
      (table_erased_of_support responses erased herased answers hanswers q hq).symm
  · simp only [eraseTable, ite_eq_right hq]

theorem eraseTable_pushforward_eq (responses : Q → FiniteDistribution (Option A))
    (erased : Q → Prop)
    (herased : ∀ q, erased q → ∀ a, (responses q).weight (some a) = 0) :
    (FiniteDistribution.table responses).pushforward (eraseTable erased) =
      FiniteDistribution.table responses := by
  calc
    _ = (FiniteDistribution.table responses).pushforward id := by
      apply FiniteDistribution.pushforward_eq_of_agree_on_support
      intro answers hanswers
      exact eraseTable_eq_of_support responses erased herased answers hanswers
    _ = _ := by
      apply FiniteDistribution.eq_of_weight_eq
      intro answers
      simp only [FiniteDistribution.pushforward, id_eq]
      rw [Finset.sum_eq_single answers]
      · simp
      · intro x _ hx
        exact ite_eq_right hx
      · intro hx
        exact False.elim (hx (Finset.mem_univ answers))

theorem expectation_le_of_admissible (responses : Q → FiniteDistribution (Option A))
    (valid : Q → A → Prop)
    (hvalid : ∀ q a, (responses q).weight (some a) ≠ 0 → valid q a)
    (score : (Q → Option A) → ℝ) (bound : ℝ)
    (hbound : ∀ answers, Admissible valid answers → score answers ≤ bound) :
    (FiniteDistribution.table responses).expectation score ≤ bound := by
  apply expectation_le_of_support
  intro answers hanswers
  exact hbound answers (table_admissible_of_support responses valid hvalid answers hanswers)

theorem expectation_le_of_probability_one (responses : Q → FiniteDistribution (Option A))
    (valid : Q → A → Prop)
    (hvalid : ∀ q, (responses q).probability (fun answer => decide (RowValid valid q answer)) = 1)
    (score : (Q → Option A) → ℝ) (bound : ℝ)
    (hbound : ∀ answers, Admissible valid answers → score answers ≤ bound) :
    (FiniteDistribution.table responses).expectation score ≤ bound :=
  expectation_le_of_admissible responses valid
    (row_valid_of_probability_one responses valid hvalid) score bound hbound

theorem collision_expectation_le (responses : Q → FiniteDistribution (Option A))
    (valid : Q → A → Prop)
    (hvalid : ∀ q, (responses q).probability (fun answer => decide (RowValid valid q answer)) = 1)
    (questions : FiniteDistribution (Q × Q)) (bound : ℝ)
    (hbound : ∀ answers, Admissible valid answers →
      questions.probability (TwoResponseCollision.collision answers) ≤ bound) :
    (FiniteDistribution.table responses).expectation
      (fun answers => questions.probability (TwoResponseCollision.collision answers)) ≤ bound :=
  expectation_le_of_probability_one responses valid hvalid _ bound hbound

end
end PerfectCompleteness.DecoderTableAdmissibility



namespace PerfectCompleteness.UpperParameterScalars

noncomputable section

def h (r ℓ : Nat) : ℝ := 1 / (2 : ℝ) ^ (r * ℓ)

def g (η : ℝ) (r ℓ : Nat) : ℝ := (η ^ 2 / 4) * h r ℓ

def q (η : ℝ) (r ℓ : Nat) : ℝ := g η r ℓ * h r ℓ

def rhoPred (κ α : ℝ) : ℝ := κ * α / 4

def b (κ α η : ℝ) (r ℓ : Nat) : ℝ := rhoPred κ α * q η r ℓ

def tau (κ α : ℝ) (r ℓ : Nat) : ℝ := rhoPred κ α * h r ℓ / 4

def gamma (κ α η : ℝ) (r ℓ : Nat) : ℝ :=
  b κ α η r ℓ * (1 / (2 : ℝ) ^ (ℓ + r)) * tau κ α r ℓ ^ 2 / 2

theorem h_pos (r ℓ : Nat) : 0 < h r ℓ := by unfold h; positivity

theorem g_pos {η : ℝ} (hη : 0 < η) (r ℓ : Nat) : 0 < g η r ℓ := by
  unfold g
  exact mul_pos (by positivity) (h_pos r ℓ)

theorem q_pos {η : ℝ} (hη : 0 < η) (r ℓ : Nat) : 0 < q η r ℓ :=
  mul_pos (g_pos hη r ℓ) (h_pos r ℓ)

theorem rhoPred_pos {κ α : ℝ} (hκ : 0 < κ) (hα : 0 < α) : 0 < rhoPred κ α := by
  unfold rhoPred
  positivity

theorem b_pos {κ α η : ℝ} (hκ : 0 < κ) (hα : 0 < α) (hη : 0 < η)
    (r ℓ : Nat) : 0 < b κ α η r ℓ :=
  mul_pos (rhoPred_pos hκ hα) (q_pos hη r ℓ)

theorem tau_pos {κ α : ℝ} (hκ : 0 < κ) (hα : 0 < α)
    (r ℓ : Nat) : 0 < tau κ α r ℓ := by
  unfold tau
  exact div_pos (mul_pos (rhoPred_pos hκ hα) (h_pos r ℓ)) (by norm_num)

theorem gamma_pos {κ α η : ℝ} (hκ : 0 < κ) (hα : 0 < α) (hη : 0 < η)
    (r ℓ : Nat) : 0 < gamma κ α η r ℓ := by
  unfold gamma
  have hb := b_pos hκ hα hη r ℓ
  have ht := tau_pos hκ hα r ℓ
  positivity

theorem all_pos {κ α η : ℝ} (hκ : 0 < κ) (hα : 0 < α) (hη : 0 < η)
    (r ℓ : Nat) :
    0 < h r ℓ ∧ 0 < g η r ℓ ∧ 0 < q η r ℓ ∧ 0 < rhoPred κ α ∧
      0 < b κ α η r ℓ ∧ 0 < tau κ α r ℓ ∧ 0 < gamma κ α η r ℓ :=
  ⟨h_pos r ℓ, g_pos hη r ℓ, q_pos hη r ℓ, rhoPred_pos hκ hα,
    b_pos hκ hα hη r ℓ, tau_pos hκ hα r ℓ, gamma_pos hκ hα hη r ℓ⟩

theorem reciprocal_pow_eq_zpow (k : Nat) :
    1 / (2 : ℝ) ^ k = (2 : ℝ) ^ (-(k : ℤ)) := by
  simp only [one_div, zpow_neg, zpow_natCast]

theorem gamma_eq_neg_zpow (κ α η : ℝ) (r ℓ : Nat) :
    gamma κ α η r ℓ =
      b κ α η r ℓ * (2 : ℝ) ^ (-(ℓ : ℤ) - (r : ℤ)) * tau κ α r ℓ ^ 2 / 2 := by
  have hexp : -((ℓ + r : Nat) : ℤ) = -(ℓ : ℤ) - (r : ℤ) := by
    simp only [Nat.cast_add]
    omega
  rw [gamma, reciprocal_pow_eq_zpow, hexp]

theorem reciprocal_power_sub_antitone (r : Nat) {ℓ ℓ' : Nat} (hℓ : ℓ ≤ ℓ') :
    1 / (2 : ℝ) ^ (ℓ' - r) ≤ 1 / (2 : ℝ) ^ (ℓ - r) := by
  have hp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) (Nat.sub_le_sub_right hℓ r)
  simpa only [div_pow, one_pow] using hp

theorem exists_rows_upward (minimum r : Nat) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ℓ : Nat, minimum ≤ ℓ ∧ r ≤ ℓ ∧ 1 ≤ ℓ ∧
      ∀ ℓ' : Nat, ℓ ≤ ℓ' → 1 / (2 : ℝ) ^ (ℓ' - r) < ρ / 8 := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (show 0 < ρ / 8 by positivity) (by norm_num : (1 / 2 : ℝ) < 1)
  let ℓ := r + k + minimum + 1
  refine ⟨ℓ, by dsimp [ℓ]; omega, by dsimp [ℓ]; omega,
    by dsimp [ℓ]; omega, ?_⟩
  intro ℓ' hℓ'
  have hkℓ : k ≤ ℓ' - r := by dsimp [ℓ] at hℓ'; omega
  have hp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) hkℓ
  simpa only [div_pow, one_pow] using hp.trans_lt hk

theorem exists_rows (minimum r : Nat) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ℓ : Nat, minimum ≤ ℓ ∧ r ≤ ℓ ∧ 1 ≤ ℓ ∧
      1 / (2 : ℝ) ^ (ℓ - r) < ρ / 8 := by
  obtain ⟨ℓ, hmin, hr, hpos, hbound⟩ := exists_rows_upward minimum r hρ
  exact ⟨ℓ, hmin, hr, hpos, hbound ℓ le_rfl⟩

theorem exists_rows_rhoPred (minimum r : Nat) {κ α : ℝ}
    (hκ : 0 < κ) (hα : 0 < α) :
    ∃ ℓ : Nat, minimum ≤ ℓ ∧ r ≤ ℓ ∧ 1 ≤ ℓ ∧
      1 / (2 : ℝ) ^ (ℓ - r) < rhoPred κ α / 8 :=
  exists_rows minimum r (rhoPred_pos hκ hα)

theorem exists_repeats_upward {h₀ τ : ℝ} (hh : 0 < h₀) (hτ : 0 < τ) :
    ∃ R : Nat, 6 ≤ R ∧ ∀ R' : Nat, R ≤ R' →
      (7 / 8 : ℝ) ^ R' ≤ min (h₀ / 2) (τ ^ 2 / 2) := by
  have htarget : 0 < min (h₀ / 2) (τ ^ 2 / 2) := by positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one htarget
    (by norm_num : (7 / 8 : ℝ) < 1)
  refine ⟨k + 6, by omega, ?_⟩
  intro R hR
  have hp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 7 / 8)
    (by norm_num : (7 / 8 : ℝ) ≤ 1) (show k ≤ R by omega)
  exact hp.trans hk.le

theorem exists_repeats {h₀ τ : ℝ} (hh : 0 < h₀) (hτ : 0 < τ) :
    ∃ R : Nat, 6 ≤ R ∧ (7 / 8 : ℝ) ^ R ≤ min (h₀ / 2) (τ ^ 2 / 2) := by
  obtain ⟨R, hR, hbound⟩ := exists_repeats_upward hh hτ
  exact ⟨R, hR, hbound R le_rfl⟩

theorem exists_upper_repeats {κ α : ℝ} (hκ : 0 < κ) (hα : 0 < α)
    (r ℓ : Nat) :
    ∃ R : Nat, 6 ≤ R ∧ (7 / 8 : ℝ) ^ R ≤
      min (h r ℓ / 2) (tau κ α r ℓ ^ 2 / 2) :=
  exists_repeats (h_pos r ℓ) (tau_pos hκ hα r ℓ)

theorem exists_upper_choices (minimum r : Nat) {κ α : ℝ}
    (hκ : 0 < κ) (hα : 0 < α) :
    ∃ ℓ R : Nat, minimum ≤ ℓ ∧ r ≤ ℓ ∧ 1 ≤ ℓ ∧
      1 / (2 : ℝ) ^ (ℓ - r) < rhoPred κ α / 8 ∧ 6 ≤ R ∧
      (7 / 8 : ℝ) ^ R ≤ min (h r ℓ / 2) (tau κ α r ℓ ^ 2 / 2) := by
  obtain ⟨ℓ, hmin, hr, hpos, hrow⟩ := exists_rows_rhoPred minimum r hκ hα
  obtain ⟨R, hR, hrep⟩ := exists_upper_repeats hκ hα r ℓ
  exact ⟨ℓ, R, hmin, hr, hpos, hrow, hR, hrep⟩

end
end PerfectCompleteness.UpperParameterScalars

end OAI
