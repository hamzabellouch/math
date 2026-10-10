import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Foundations.Conditioning
import OAI.Computability.UniqueGames.Foundations.MixtureLemmas
import OAI.Computability.UniqueGames.Foundations.ValueLemmas

namespace OAI

section

/-!
Exact finite sampling laws used to identify verifier distributions with repeated
game question laws. These are finite sum/product identities, not independence
assumptions about an unspecified distribution.
-/

namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section

theorem iid_pushforward {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (f : Ω → Γ) (n : Nat) :
    (μ.pushforward f).iid n =
      (μ.iid n).pushforward (fun answers i => f (answers i)) := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [iid, pushforward]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (fun i => f (x i)) = y
  · have hp : ∀ i, f (x i) = y i := congrFun h
    simp [hp]
  · rw [ite_eq_right h]
    have hn : ¬ ∀ i, f (x i) = y i := fun hp => h (funext hp)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteDistribution Ω where
  weight _ := 1 / (Fintype.card Ω : ℝ)
  nonnegative _ := div_nonneg zero_le_one (Nat.cast_nonneg _)
  normalized := by
    have hn : (Fintype.card Ω : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_div]
    exact mul_inv_cancel₀ hn

theorem iid_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] (n : Nat) :
    (uniform Ω).iid n = uniform (Fin n → Ω) := by
  classical
  apply eq_of_weight_eq
  intro x
  simp [iid, uniform, Nat.cast_pow, one_div]

theorem expectation_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    (uniform Ω).expectation f = (∑ x, f x) / (Fintype.card Ω : ℝ) := by
  unfold expectation uniform
  rw [← Finset.mul_sum]
  simp [div_eq_mul_inv, mul_comm]

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

section

/-!
Coordinate reindexing for actual finite distributions and repeated games.
The joint questions are iid across coordinates; coordinate-success events
need not be independent. Strategies permute each player's local questions
and answers, so the resulting strategies remain local.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

namespace FiniteDistribution

def reindexEquiv {ι κ Ω : Type*} (e : κ ≃ ι) : (ι → Ω) ≃ (κ → Ω) where
  toFun f := f ∘ e
  invFun g := g ∘ e.symm
  left_inv f := by funext i; simp
  right_inv g := by funext i; simp

theorem pushforward_equiv {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (e : Ω ≃ Γ) :
    μ.pushforward e = μ.transport e := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [pushforward, transport]
  have he : ∀ x : Ω, (e x = y) = (x = e.symm y) := by
    intro x
    apply propext
    constructor
    · intro h
      simpa using congrArg e.symm h
    · intro h
      rw [h, e.apply_symm_apply]
  simp_rw [he]
  simp

theorem table_const_reindex {ι κ Ω : Type*}
    [Fintype ι] [Fintype κ] [Fintype Ω] [DecidableEq ι] [DecidableEq κ]
    (μ : FiniteDistribution Ω) (e : κ ≃ ι) :
    (table (fun _ : ι => μ)).pushforward (fun f => f ∘ e) =
      table (fun _ : κ => μ) := by
  classical
  change (table (fun _ : ι => μ)).pushforward (reindexEquiv e) = _
  rw [pushforward_equiv]
  apply eq_of_weight_eq
  intro g
  change (∏ i : ι, μ.weight (g (e.symm i))) = ∏ k : κ, μ.weight (g k)
  exact e.symm.prod_comp (fun k => μ.weight (g k))

theorem iid_reindex {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) {n m : Nat} (e : Fin m ≃ Fin n) :
    (μ.iid n).pushforward (fun f => f ∘ e) = μ.iid m := by
  classical
  change (μ.iid n).pushforward (reindexEquiv e) = _
  rw [pushforward_equiv]
  apply eq_of_weight_eq
  intro g
  change (∏ i : Fin n, μ.weight (g (e.symm i))) = ∏ k : Fin m, μ.weight (g k)
  exact e.symm.prod_comp (fun k => μ.weight (g k))

/-- Weighted finite change of variables; no independence hypothesis. -/
theorem probability_reindex_of_weight {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ) (e : Ω ≃ Γ)
    (hweight : ∀ x, ν.weight (e x) = μ.weight x) (event : Γ → Bool) :
    ν.probability event = μ.probability (fun x => event (e x)) := by
  classical
  change (∑ y, if event y then ν.weight y else 0) =
    ∑ x, if event (e x) then μ.weight x else 0
  rw [← e.sum_comp (fun y => if event y then ν.weight y else 0)]
  apply Finset.sum_congr rfl
  intro x _
  rw [hweight]

end FiniteDistribution

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
variable [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def questionReindexEquiv {n m : Nat} (e : Fin m ≃ Fin n) :
    ((Fin n → Q₁) × (Fin n → Q₂)) ≃ ((Fin m → Q₁) × (Fin m → Q₂)) :=
  Equiv.prodCongr (FiniteDistribution.reindexEquiv e)
    (FiniteDistribution.reindexEquiv e)

/-- Each player only permutes that player's own questions and answers. -/
def reindexStrategy {n m : Nat} (e : Fin m ≃ Fin n)
    (s : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    Strategy (Fin m → Q₁) (Fin m → Q₂) (Fin m → A₁) (Fin m → A₂) :=
  (fun x i => s.1 (x ∘ e.symm) (e i),
   fun y i => s.2 (y ∘ e.symm) (e i))

/-- Simultaneous coordinate permutation preserves the actual joint question weight. -/
theorem repetition_question_weight_reindex (G : Game Q₁ Q₂ A₁ A₂)
    {n m : Nat} (e : Fin m ≃ Fin n)
    (q : (Fin n → Q₁) × (Fin n → Q₂)) :
    (G.repetition m).questions.weight (questionReindexEquiv e q) =
      (G.repetition n).questions.weight q := by
  classical
  rw [repetition_question_weight, repetition_question_weight]
  change (∏ i : Fin m, G.questions.weight (q.1 (e i), q.2 (e i))) =
    ∏ j : Fin n, G.questions.weight (q.1 j, q.2 j)
  exact e.prod_comp (fun j => G.questions.weight (q.1 j, q.2 j))

theorem repetition_questions_reindex (G : Game Q₁ Q₂ A₁ A₂)
    {n m : Nat} (e : Fin m ≃ Fin n) :
    (G.repetition n).questions.pushforward (questionReindexEquiv e) =
      (G.repetition m).questions := by
  classical
  rw [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro q
  change (G.repetition n).questions.weight ((questionReindexEquiv e).symm q) =
    (G.repetition m).questions.weight q
  have h := repetition_question_weight_reindex G e ((questionReindexEquiv e).symm q)
  simpa only [Equiv.apply_symm_apply] using h.symm

/-- Coordinate successes transform pointwise; they are not assumed independent. -/
theorem coordinateWin_reindex (G : Game Q₁ Q₂ A₁ A₂)
    {n m : Nat} (e : Fin m ≃ Fin n)
    (s : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (i : Fin m) (q : (Fin n → Q₁) × (Fin n → Q₂)) :
    G.coordinateWin (reindexStrategy e s) i (questionReindexEquiv e q) =
      G.coordinateWin s (e i) q := by
  have h₁ : (fun j : Fin n => q.1 (e (e.symm j))) = q.1 := by
    funext j
    rw [e.apply_symm_apply]
  have h₂ : (fun j : Fin n => q.2 (e (e.symm j))) = q.2 := by
    funext j
    rw [e.apply_symm_apply]
  change G.accepts (q.1 (e i)) (q.2 (e i))
      (s.1 (fun j => q.1 (e (e.symm j))) (e i))
      (s.2 (fun j => q.2 (e (e.symm j))) (e i)) =
    G.accepts (q.1 (e i)) (q.2 (e i)) (s.1 q.1 (e i)) (s.2 q.2 (e i))
  rw [h₁, h₂]

theorem selectedWins_reindex (G : Game Q₁ Q₂ A₁ A₂)
    {n m : Nat} (e : Fin m ≃ Fin n)
    (s : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (S : Finset (Fin m)) (q : (Fin n → Q₁) × (Fin n → Q₂)) :
    G.selectedWins (reindexStrategy e s) S (questionReindexEquiv e q) =
      G.selectedWins s (S.map e.toEmbedding) q := by
  classical
  unfold selectedWins
  congr 1
  apply propext
  constructor
  · intro h j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    have hw := h i hi
    rw [coordinateWin_reindex] at hw
    exact hw
  · intro h i hi
    rw [coordinateWin_reindex]
    exact h (e i) (Finset.mem_map.mpr ⟨i, hi, rfl⟩)

/-- The actual selected-success probability is invariant under the same relabeling. -/
theorem selectedSuccess_reindex (G : Game Q₁ Q₂ A₁ A₂)
    {n m : Nat} (e : Fin m ≃ Fin n)
    (s : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (S : Finset (Fin m)) :
    G.selectedSuccess (reindexStrategy e s) S =
      G.selectedSuccess s (S.map e.toEmbedding) := by
  classical
  unfold selectedSuccess
  rw [FiniteDistribution.probability_reindex_of_weight
    (G.repetition n).questions (G.repetition m).questions (questionReindexEquiv e)
    (repetition_question_weight_reindex G e)]
  congr 1
  funext q
  exact selectedWins_reindex G e s S q

/-- Full repetition success is a special case, including zero repetitions. -/
theorem repetition_success_reindex (G : Game Q₁ Q₂ A₁ A₂)
    {n m : Nat} (e : Fin m ≃ Fin n)
    (s : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    (G.repetition m).success (reindexStrategy e s) =
      (G.repetition n).success s := by
  classical
  have huniv : (Finset.univ : Finset (Fin m)).map e.toEmbedding = Finset.univ := by
    ext j
    constructor
    · intro _
      exact Finset.mem_univ j
    · intro _
      exact Finset.mem_map.mpr ⟨e.symm j, Finset.mem_univ _, e.apply_symm_apply j⟩
  have h := selectedSuccess_reindex G e s Finset.univ
  rw [huniv, selectedSuccess_univ, selectedSuccess_univ] at h
  exact h

end Game
end UniqueGamesTheorem.Foundations.Games

end

end

section

/-!
Finite real probability vectors and information inequalities.

`relativeEntropy` uses the natural logarithm and a real-valued finite sum.
Its theorems require support containment, so a positive numerator is never
silently assigned finite divergence against a zero denominator.
-/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

def IsProbability (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

def SupportedBy (p q : α → ℝ) : Prop := ∀ a, p a ≠ 0 → q a ≠ 0

noncomputable def relativeEntropy (p q : α → ℝ) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)

noncomputable def totalVariation (p q : α → ℝ) : ℝ :=
  (∑ a, |p a - q a|) / 2

noncomputable def posterior (p w : α → ℝ) (z : ℝ) : α → ℝ :=
  fun a => p a * w a / z

theorem posterior_isProbability (p w : α → ℝ) (hp : IsProbability p)
    (hw : ∀ a, 0 ≤ w a) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ a, p a * w a = z) : IsProbability (posterior p w z) := by
  constructor
  · intro a
    exact div_nonneg (mul_nonneg (hp.1 a) (hw a)) hz.le
  · simp only [posterior, div_eq_mul_inv, ← Finset.sum_mul, hmass,
      mul_inv_cancel₀ hz.ne']

omit [Fintype α] in
theorem posterior_supportedBy (p w : α → ℝ) (z : ℝ) :
    SupportedBy (posterior p w z) p := by
  intro a ha hp
  exact ha (by simp [posterior, hp])

theorem mul_log_div_ge_sub {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x - y ≤ x * Real.log (x / y) := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
  have hm := mul_le_mul_of_nonneg_left h hx.le
  have he : x * (1 - (x / y)⁻¹) = x - y := by
    field_simp [hx.ne', hy.ne']
  rwa [he] at hm

theorem relativeEntropy_nonneg (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) (hs : SupportedBy p q) : 0 ≤ relativeEntropy p q := by
  have hpoint : ∀ a, p a - q a ≤ p a * Real.log (p a / q a) := by
    intro a
    by_cases hpa : p a = 0
    · simp only [hpa, zero_sub, zero_div, zero_mul]
      exact neg_nonpos.mpr (hq.1 a)
    · exact mul_log_div_ge_sub (lt_of_le_of_ne (hp.1 a) (Ne.symm hpa))
        (lt_of_le_of_ne (hq.1 a) (Ne.symm (hs a hpa)))
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simpa [relativeEntropy, Finset.sum_sub_distrib, hp.2, hq.2] using hsum

theorem posterior_relativeEntropy_le (p w : α → ℝ) (hp : IsProbability p)
    (hw : ∀ a, 0 ≤ w a) (hw_one : ∀ a, w a ≤ 1) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ a, p a * w a = z) :
    relativeEntropy (posterior p w z) p ≤ Real.log (1 / z) := by
  have hpost := posterior_isProbability p w hp hw hz hmass
  have hpoint : ∀ a, posterior p w z a * Real.log (posterior p w z a / p a) ≤
      posterior p w z a * Real.log (1 / z) := by
    intro a
    by_cases hpa : posterior p w z a = 0
    · simp [hpa]
    have hpne := posterior_supportedBy p w z a hpa
    have hppos : 0 < p a := lt_of_le_of_ne (hp.1 a) (Ne.symm hpne)
    have hpostpos : 0 < posterior p w z a :=
      lt_of_le_of_ne (hpost.1 a) (Ne.symm hpa)
    have hr : posterior p w z a / p a = w a / z := by
      dsimp [posterior]
      field_simp [hpne, hz.ne']
    apply mul_le_mul_of_nonneg_left _ (hpost.1 a)
    apply Real.log_le_log (div_pos hpostpos hppos)
    rw [hr]
    exact div_le_div_of_nonneg_right (hw_one a) hz.le
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simpa only [relativeEntropy, ← Finset.sum_mul, hpost.2, one_mul] using hsum

theorem totalVariation_nonneg (p q : α → ℝ) : 0 ≤ totalVariation p q := by
  exact div_nonneg (Finset.sum_nonneg (fun a _ => abs_nonneg (p a - q a))) (by norm_num)

theorem totalVariation_symm (p q : α → ℝ) : totalVariation p q = totalVariation q p := by
  simp only [totalVariation, abs_sub_comm]

theorem totalVariation_le_one (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) : totalVariation p q ≤ 1 := by
  have hpoint : ∀ a, |p a - q a| ≤ p a + q a := by
    intro a
    rw [abs_le]
    constructor <;> linarith [hp.1 a, hq.1 a]
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [Finset.sum_add_distrib, hp.2, hq.2] at hsum
  dsimp [totalVariation]
  linarith

theorem le_binaryLog_of_le_log {r x : ℝ} (hr : 0 ≤ r) (h : r ≤ Real.log x) :
    r ≤ Real.log x / Real.log 2 := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwo_one : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    exact ht
  apply (le_div_iff₀ htwo).2
  exact (mul_le_mul_of_nonneg_left htwo_one hr).trans (by simpa using h)

/-- Finite weighted Cauchy–Schwarz for probability weights. The summands
need not be nonnegative. -/
theorem weighted_sum_sq_le (w x : α → ℝ) (hw : IsProbability w) :
    (∑ a, w a * x a)^2 ≤ ∑ a, w a * (x a)^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun a => Real.sqrt (w a)) (fun a => Real.sqrt (w a) * x a)
  have hfirst : ∀ a, Real.sqrt (w a) * (Real.sqrt (w a) * x a) = w a * x a := by
    intro a
    rw [← mul_assoc, Real.mul_self_sqrt (hw.1 a)]
  have hsecond : ∀ a, (Real.sqrt (w a) * x a)^2 = w a * (x a)^2 := by
    intro a
    rw [mul_pow, Real.sq_sqrt (hw.1 a)]
  simpa only [hfirst, hsecond, Real.sq_sqrt (hw.1 _), hw.2, one_mul] using hcs

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Finite product-reference entropy decomposition, including zero-probability fibers. -/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def firstMarginal (p : α × β → ℝ) (a : α) : ℝ := ∑ b, p (a, b)

noncomputable def secondMarginal (p : α × β → ℝ) (b : β) : ℝ := ∑ a, p (a, b)

def product (p : α → ℝ) (q : β → ℝ) : α × β → ℝ := fun ab => p ab.1 * q ab.2

theorem firstMarginal_isProbability (p : α × β → ℝ) (hp : IsProbability p) :
    IsProbability (firstMarginal p) := by
  constructor
  · intro a
    exact Finset.sum_nonneg (fun b _ => hp.1 (a, b))
  · simpa only [firstMarginal, Fintype.sum_prod_type] using hp.2

theorem secondMarginal_isProbability (p : α × β → ℝ) (hp : IsProbability p) :
    IsProbability (secondMarginal p) := by
  constructor
  · intro b
    exact Finset.sum_nonneg (fun a _ => hp.1 (a, b))
  · change (∑ b, ∑ a, p (a, b)) = 1
    rw [Finset.sum_comm]
    exact (firstMarginal_isProbability p hp).2

theorem product_isProbability (p : α → ℝ) (q : β → ℝ)
    (hp : IsProbability p) (hq : IsProbability q) : IsProbability (product p q) := by
  constructor
  · intro ab
    exact mul_nonneg (hp.1 ab.1) (hq.1 ab.2)
  · simp only [product, Fintype.sum_prod_type, ← Finset.mul_sum, hq.2, mul_one, hp.2]

theorem point_le_firstMarginal (p : α × β → ℝ) (hp : IsProbability p) (a : α) (b : β) :
    p (a, b) ≤ firstMarginal p a := by
  classical
  exact Finset.single_le_sum (fun b _ => hp.1 (a, b)) (Finset.mem_univ b)

theorem point_le_secondMarginal (p : α × β → ℝ) (hp : IsProbability p) (a : α) (b : β) :
    p (a, b) ≤ secondMarginal p b := by
  classical
  exact Finset.single_le_sum (fun a _ => hp.1 (a, b)) (Finset.mem_univ a)

theorem joint_supportedBy_product_marginals (p : α × β → ℝ) (hp : IsProbability p) :
    SupportedBy p (product (firstMarginal p) (secondMarginal p)) := by
  intro ab hpne
  have hpos : 0 < p ab := lt_of_le_of_ne (hp.1 ab) (Ne.symm hpne)
  exact mul_ne_zero
    (ne_of_gt (hpos.trans_le (point_le_firstMarginal p hp ab.1 ab.2)))
    (ne_of_gt (hpos.trans_le (point_le_secondMarginal p hp ab.1 ab.2)))

theorem relativeEntropy_product_reference (p : α × β → ℝ) (u : α → ℝ) (v : β → ℝ)
    (hp : IsProbability p) (_hu : IsProbability u) (_hv : IsProbability v)
    (hsu : SupportedBy (firstMarginal p) u) (hsv : SupportedBy (secondMarginal p) v) :
    relativeEntropy p (product u v) =
      relativeEntropy p (product (firstMarginal p) (secondMarginal p)) +
        relativeEntropy (firstMarginal p) u + relativeEntropy (secondMarginal p) v := by
  have hpoint : ∀ ab : α × β, p ab * Real.log (p ab / product u v ab) =
      p ab * Real.log (p ab / product (firstMarginal p) (secondMarginal p) ab) +
      p ab * Real.log (firstMarginal p ab.1 / u ab.1) +
      p ab * Real.log (secondMarginal p ab.2 / v ab.2) := by
    intro ab
    by_cases hzero : p ab = 0
    · simp [hzero]
    have hpos : 0 < p ab := lt_of_le_of_ne (hp.1 ab) (Ne.symm hzero)
    have hleft := ne_of_gt (hpos.trans_le (point_le_firstMarginal p hp ab.1 ab.2))
    have hright := ne_of_gt (hpos.trans_le (point_le_secondMarginal p hp ab.1 ab.2))
    have hune := hsu ab.1 hleft
    have hvne := hsv ab.2 hright
    simp only [product, Real.log_div hzero (mul_ne_zero hune hvne),
      Real.log_div hzero (mul_ne_zero hleft hright), Real.log_mul hune hvne,
      Real.log_mul hleft hright, Real.log_div hleft hune, Real.log_div hright hvne]
    ring
  have hleftSum : (∑ ab : α × β, p ab * Real.log (firstMarginal p ab.1 / u ab.1)) =
      relativeEntropy (firstMarginal p) u := by
    simp only [Fintype.sum_prod_type, ← Finset.sum_mul, relativeEntropy, firstMarginal]
  have hrightSum : (∑ ab : α × β, p ab * Real.log (secondMarginal p ab.2 / v ab.2)) =
      relativeEntropy (secondMarginal p) v := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [← Finset.sum_mul, relativeEntropy, secondMarginal]
  unfold relativeEntropy
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hleftSum, hrightSum]
  rfl

theorem marginal_relativeEntropy_sum_le (p : α × β → ℝ) (u : α → ℝ) (v : β → ℝ)
    (hp : IsProbability p) (hu : IsProbability u) (hv : IsProbability v)
    (hsu : SupportedBy (firstMarginal p) u) (hsv : SupportedBy (secondMarginal p) v) :
    relativeEntropy (firstMarginal p) u + relativeEntropy (secondMarginal p) v ≤
      relativeEntropy p (product u v) := by
  rw [relativeEntropy_product_reference p u v hp hu hv hsu hsv]
  have hn := relativeEntropy_nonneg p (product (firstMarginal p) (secondMarginal p)) hp
    (product_isProbability _ _ (firstMarginal_isProbability p hp)
      (secondMarginal_isProbability p hp)) (joint_supportedBy_product_marginals p hp)
  linarith

end UniqueGamesTheorem.Foundations.Information

end

section

/-!
Conditional laws on finite spaces, with a normalized default on null rows.
The default remains a probability law when a new input law charges a row
that had zero probability in the original joint distribution.
-/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def conditionalKernel
    (p : α × β → ℝ) (fallback : β → ℝ) (a : α) (b : β) : ℝ := by
  classical
  exact if firstMarginal p a = 0 then fallback b
    else p (a, b) / firstMarginal p a

theorem conditionalKernel_isProbability
    (p : α × β → ℝ) (fallback : β → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) (a : α) :
    IsProbability (conditionalKernel p fallback a) := by
  classical
  by_cases hm : firstMarginal p a = 0
  · simpa only [IsProbability, conditionalKernel, ite_eq_left hm] using hf
  · constructor
    · intro b
      simp only [conditionalKernel, ite_eq_right hm]
      exact div_nonneg (hp.1 (a, b))
        ((firstMarginal_isProbability p hp).1 a)
    · simp only [conditionalKernel, ite_eq_right hm, div_eq_mul_inv, ← Finset.sum_mul]
      change firstMarginal p a * (firstMarginal p a)⁻¹ = 1
      exact mul_inv_cancel₀ hm

theorem marginal_mul_conditionalKernel
    (p : α × β → ℝ) (fallback : β → ℝ)
    (hp : IsProbability p) (a : α) (b : β) :
    firstMarginal p a * conditionalKernel p fallback a b = p (a, b) := by
  classical
  by_cases hm : firstMarginal p a = 0
  · have hpoint := point_le_firstMarginal p hp a b
    rw [hm] at hpoint
    have hz : p (a, b) = 0 := le_antisymm hpoint (hp.1 (a, b))
    simp [conditionalKernel, hm, hz]
  · simp only [conditionalKernel, ite_eq_right hm]
    calc
      firstMarginal p a * (p (a, b) / firstMarginal p a)
          = p (a, b) *
              (firstMarginal p a / firstMarginal p a) := by ring
      _ = p (a, b) := by rw [div_self hm, mul_one]

theorem law_of_total_probability
    (p : α × β → ℝ) (fallback : β → ℝ)
    (hp : IsProbability p) (b : β) :
    (∑ a, firstMarginal p a * conditionalKernel p fallback a b) =
      secondMarginal p b := by
  simp only [marginal_mul_conditionalKernel p fallback hp, secondMarginal]

theorem kernelProduct_isProbability
    (r : α → ℝ) (k : α → β → ℝ)
    (hr : IsProbability r) (hk : ∀ a, IsProbability (k a)) :
    IsProbability (fun ab : α × β => r ab.1 * k ab.1 ab.2) := by
  constructor
  · intro ab
    exact mul_nonneg (hr.1 ab.1) ((hk ab.1).1 ab.2)
  · simp only [Fintype.sum_prod_type, ← Finset.mul_sum,
      (hk _).2, mul_one, hr.2]

theorem alternativeInput_conditionalProduct_isProbability
    (p : α × β → ℝ) (fallback : β → ℝ) (r : α → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback)
    (hr : IsProbability r) :
    IsProbability
      (fun ab : α × β => r ab.1 * conditionalKernel p fallback ab.1 ab.2) :=
  kernelProduct_isProbability r (conditionalKernel p fallback) hr
    (conditionalKernel_isProbability p fallback hp hf)

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Exact interfaces between the information vectors and finite game laws. -/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

theorem gameLaw_isProbability (μ : Games.FiniteDistribution α) : IsProbability μ.weight :=
  ⟨μ.nonnegative, μ.normalized⟩

def toGameLaw (p : α → ℝ) (hp : IsProbability p) : Games.FiniteDistribution α where
  weight := p
  nonnegative := hp.1
  normalized := hp.2

def gameLawEquiv : Games.FiniteDistribution α ≃ {p : α → ℝ // IsProbability p} where
  toFun μ := ⟨μ.weight, gameLaw_isProbability μ⟩
  invFun p := toGameLaw p.1 p.2
  left_inv μ := by cases μ; rfl
  right_inv p := by cases p; rfl

theorem totalVariation_gameLaw (μ ν : Games.FiniteDistribution α) :
    totalVariation μ.weight ν.weight = μ.totalVariation ν := rfl

noncomputable def gameConditionalKernel (μ : Games.FiniteDistribution (α × β))
    (fallback : Games.FiniteDistribution β) (a : α) : Games.FiniteDistribution β :=
  toGameLaw (conditionalKernel μ.weight fallback.weight a)
    (conditionalKernel_isProbability μ.weight fallback.weight
      (gameLaw_isProbability μ) (gameLaw_isProbability fallback) a)

theorem gameConditionalKernel_recombine (μ : Games.FiniteDistribution (α × β))
    (fallback : Games.FiniteDistribution β) (a : α) (b : β) :
    firstMarginal μ.weight a * (gameConditionalKernel μ fallback a).weight b =
      μ.weight (a, b) :=
  marginal_mul_conditionalKernel μ.weight fallback.weight (gameLaw_isProbability μ) a b

noncomputable def gameConditionalProduct (μ : Games.FiniteDistribution (α × β))
    (fallback : Games.FiniteDistribution β) (newInput : Games.FiniteDistribution α) :
    Games.FiniteDistribution (α × β) :=
  toGameLaw (fun ab => newInput.weight ab.1 * conditionalKernel μ.weight fallback.weight ab.1 ab.2)
    (alternativeInput_conditionalProduct_isProbability μ.weight fallback.weight newInput.weight
      (gameLaw_isProbability μ) (gameLaw_isProbability fallback) (gameLaw_isProbability newInput))

theorem gameConditionalProduct_weight (μ : Games.FiniteDistribution (α × β))
    (fallback : Games.FiniteDistribution β) (newInput : Games.FiniteDistribution α)
    (a : α) (b : β) :
    (gameConditionalProduct μ fallback newInput).weight (a, b) =
      newInput.weight a * (gameConditionalKernel μ fallback a).weight b := rfl

theorem gameCondition_weight (μ : Games.FiniteDistribution α) (event : α → Bool)
    (positive : 0 < μ.probability event) :
    (μ.condition event positive).weight =
      posterior μ.weight (fun a => if event a then 1 else 0) (μ.probability event) := by
  funext a
  cases he : event a <;> simp [Games.FiniteDistribution.condition, posterior, he]

theorem gameCondition_relativeEntropy_le (μ : Games.FiniteDistribution α) (event : α → Bool)
    (positive : 0 < μ.probability event) :
    relativeEntropy (μ.condition event positive).weight μ.weight ≤
      Real.log (1 / μ.probability event) := by
  rw [gameCondition_weight]
  apply posterior_relativeEntropy_le μ.weight (fun a => if event a then 1 else 0)
    (gameLaw_isProbability μ)
  · intro a
    cases event a <;> norm_num
  · intro a
    cases event a <;> norm_num
  · exact positive
  · unfold Games.FiniteDistribution.probability
    apply Finset.sum_congr rfl
    intro a _
    cases event a <;> simp

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Statistical distance under finite kernels and event restriction. -/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

theorem totalVariation_joint_common_weights (w : α → ℝ) (p q : α → β → ℝ)
    (hw : ∀ a, 0 ≤ w a) :
    totalVariation (fun ab : α × β => w ab.1 * p ab.1 ab.2)
      (fun ab : α × β => w ab.1 * q ab.1 ab.2) =
        ∑ a, w a * totalVariation (p a) (q a) := by
  have hpoint : ∀ a b, |w a * p a b - w a * q a b| = w a * |p a b - q a b| := by
    intro a b
    rw [← mul_sub, abs_mul, abs_of_nonneg (hw a)]
  simp only [totalVariation, Fintype.sum_prod_type, hpoint, ← Finset.mul_sum,
    div_eq_mul_inv, Finset.sum_mul, mul_assoc]

theorem totalVariation_joint_common_kernel (p q : α → ℝ) (k : α → β → ℝ)
    (hk : ∀ a, IsProbability (k a)) :
    totalVariation (fun ab : α × β => p ab.1 * k ab.1 ab.2)
      (fun ab : α × β => q ab.1 * k ab.1 ab.2) = totalVariation p q := by
  have hpoint : ∀ a b, |p a * k a b - q a * k a b| = |p a - q a| * k a b := by
    intro a b
    rw [← sub_mul, abs_mul, abs_of_nonneg ((hk a).1 b)]
  simp only [totalVariation, Fintype.sum_prod_type, hpoint, ← Finset.mul_sum,
    (hk _).2, mul_one]

theorem totalVariation_condition_le (p q : α → ℝ) (event : α → Prop)
    [DecidablePred event] {c : ℝ} (hc : 0 < c) :
    totalVariation (fun a => if event a then p a / c else 0)
      (fun a => if event a then q a / c else 0) ≤ totalVariation p q / c := by
  have hpoint : ∀ a, |(if event a then p a / c else 0) -
      (if event a then q a / c else 0)| ≤ |p a - q a| / c := by
    intro a
    by_cases he : event a
    · simp only [ite_eq_left he, ← sub_div, abs_div, abs_of_pos hc, le_refl]
    · simp only [ite_eq_right he, sub_self, abs_zero]
      exact div_nonneg (abs_nonneg _) hc.le
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [div_eq_mul_inv, ← Finset.sum_mul] at hsum
  have hd := div_le_div_of_nonneg_right hsum (show (0 : ℝ) ≤ 2 by norm_num)
  have hreorder : ((∑ a, |p a - q a|) * c⁻¹) / 2 =
      ((∑ a, |p a - q a|) / 2) / c := by ring
  rw [hreorder] at hd
  simpa only [totalVariation, div_eq_mul_inv] using hd

theorem weighted_coordinate_sum_sq_le
    (w : α → ℝ) (d : α → β → ℝ) (C : α → ℝ)
    (hw : IsProbability w)
    (hbudget : ∀ a, w a * (∑ b, d a b ^ 2) ≤ w a * C a) :
    (∑ b, ∑ a, w a * d a b)^2 ≤
      (Fintype.card β : ℝ) * (∑ a, w a * C a) := by
  have hv := Finset.sum_le_sum
    (fun b (_ : b ∈ (Finset.univ : Finset β)) =>
      weighted_sum_sq_le w (fun a => d a b) hw)
  have he :
      (∑ b, ∑ a, w a * d a b ^ 2) =
        ∑ a, w a * (∑ b, d a b ^ 2) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [he] at hv
  have hb := Finset.sum_le_sum
    (fun a (_ : a ∈ (Finset.univ : Finset α)) => hbudget a)
  have hs := hv.trans hb
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset β)
    (fun b => ∑ a, w a * d a b) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
  calc
    (∑ b, ∑ a, w a * d a b)^2
        ≤ (∑ b, (∑ a, w a * d a b)^2) *
            (Fintype.card β : ℝ) := hcs
    _ = (Fintype.card β : ℝ) *
          (∑ b, (∑ a, w a * d a b)^2) := mul_comm _ _
    _ ≤ (Fintype.card β : ℝ) * (∑ a, w a * C a) :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Finite log-sum estimates, including the side-information entropy budget. -/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem normalize_isProbability (b : α → ℝ) (hb : ∀ a, 0 ≤ b a)
    {B : ℝ} (hB : 0 < B) (hmass : ∑ a, b a = B) :
    IsProbability (fun a => b a / B) := by
  constructor
  · intro a
    exact div_nonneg (hb a) hB.le
  · simp only [div_eq_mul_inv, ← Finset.sum_mul, hmass, mul_inv_cancel₀ hB.ne']

theorem relativeEntropy_normalize_right (p b : α → ℝ) (hp : IsProbability p)
    (hs : SupportedBy p b) {B : ℝ} (hB : 0 < B) :
    relativeEntropy p (fun a => b a / B) = relativeEntropy p b + Real.log B := by
  have hpoint : ∀ a, p a * Real.log (p a / (b a / B)) =
      p a * Real.log (p a / b a) + p a * Real.log B := by
    intro a
    by_cases hpa : p a = 0
    · simp [hpa]
    have hbne := hs a hpa
    rw [Real.log_div hpa (div_ne_zero hbne hB.ne'), Real.log_div hbne hB.ne',
      Real.log_div hpa hbne]
    ring
  simp only [relativeEntropy, hpoint, Finset.sum_add_distrib, ← Finset.sum_mul, hp.2, one_mul]

theorem neg_relativeEntropy_le_log_mass (p b : α → ℝ) (hp : IsProbability p)
    (hb : ∀ a, 0 ≤ b a) (hs : SupportedBy p b) {B : ℝ} (hB : 0 < B)
    (hmass : ∑ a, b a = B) : -relativeEntropy p b ≤ Real.log B := by
  have hs' : SupportedBy p (fun a => b a / B) :=
    fun a ha => div_ne_zero (hs a ha) hB.ne'
  have hnonneg := relativeEntropy_nonneg p (fun a => b a / B) hp
    (normalize_isProbability b hb hB hmass) hs'
  rw [relativeEntropy_normalize_right p b hp hs hB] at hnonneg
  linarith

/-- Entropy budget for a finite posterior indexed by side information.
The baseline masses `b` may have total mass `B`, rather than one. In the
application, `b(t,v)=P_T(t)` and `B` is the number of possible side labels. -/
theorem posterior_weighted_log_inverse_le (p b c : α → ℝ) (hp : IsProbability p)
    (hb : ∀ a, 0 ≤ b a) {z B : ℝ} (hz : 0 < z) (hB : 0 < B)
    (hmass : ∑ a, b a = B) (hpost : ∀ a, p a = b a * c a / z) :
    (∑ a, p a * Real.log (1 / c a)) ≤ Real.log (B / z) := by
  have hs : SupportedBy p b := by
    intro a ha hba
    apply ha
    rw [hpost, hba, zero_mul, zero_div]
  have hpoint : ∀ a, p a * Real.log (1 / c a) =
      p a * Real.log (1 / z) - p a * Real.log (p a / b a) := by
    intro a
    by_cases hpa : p a = 0
    · simp [hpa]
    have hbne := hs a hpa
    have hcne : c a ≠ 0 := by
      intro hca
      apply hpa
      rw [hpost, hca, mul_zero, zero_div]
    have hratio : p a / b a = c a / z := by
      rw [hpost]
      field_simp [hbne, hz.ne']
    rw [hratio, Real.log_div hcne hz.ne', Real.log_div one_ne_zero hcne,
      Real.log_div one_ne_zero hz.ne', Real.log_one]
    ring
  have hid : (∑ a, p a * Real.log (1 / c a)) =
      Real.log (1 / z) - relativeEntropy p b := by
    simp only [hpoint, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul,
      relativeEntropy]
  have hkl := neg_relativeEntropy_le_log_mass p b hp hb hs hB hmass
  rw [hid, Real.log_div hB.ne' hz.ne', Real.log_div one_ne_zero hz.ne', Real.log_one]
  linarith

end UniqueGamesTheorem.Foundations.Information

end

end OAI
