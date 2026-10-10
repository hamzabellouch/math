import Mathlib
import OAI.LinearAlgebra.MatrixFields.Entropy.ZeroLeafRateFormula

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation

open scoped BigOperators

variable {A I J : Type*} [Fintype A] [DecidableEq A] [Fintype I] [Fintype J]
  [DecidableEq I]

def wordPopulation (w : I → A) (a : A) : ℕ := Fintype.card {i // w i = a}

omit [DecidableEq I] in
theorem wordPopulation_sum (w : I → A) :
    ∑ a, wordPopulation w a = Fintype.card I := by
  simpa [wordPopulation] using Fintype.card_congr (Equiv.sigmaFiberEquiv w)

omit [Fintype A] [DecidableEq I] in
theorem wordPopulation_reindex (w : I → A) (e : J ≃ I) (a : A) :
    wordPopulation (w ∘ e) a = wordPopulation w a :=
  Fintype.card_congr (Equiv.subtypeEquiv e fun _ => Iff.rfl)

abbrev ExactWords (counts : A → ℕ) :=
  {w : Fin (∑ a, counts a) → A // ∀ a, wordPopulation w a = counts a}

theorem wordPopulation_sigma_fst (counts : A → ℕ) (a : A) :
    wordPopulation (fun i : Σ b, Fin (counts b) => i.1) a = counts a := by
  let e : {i : Σ b, Fin (counts b) // i.1 = a} ≃ Fin (counts a) :=
    { toFun := fun i => i.property ▸ i.val.2
      invFun := fun i => ⟨⟨a, i⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨b, i⟩, h⟩
        cases h
        rfl
      right_inv := by intro i; rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

theorem exactWords_nonempty (counts : A → ℕ) : Nonempty (ExactWords counts) := by
  classical
  let e : Fin (∑ a, counts a) ≃ (Σ a, Fin (counts a)) :=
    Fintype.equivOfCardEq (by simp)
  refine ⟨⟨(fun i : Σ a, Fin (counts a) => i.1) ∘ e, ?_⟩⟩
  intro a
  rw [wordPopulation_reindex, wordPopulation_sigma_fst]

omit [Fintype A] [DecidableEq I] in
theorem samePopulation_iff_permutation (w v : I → A) :
    (∀ a, wordPopulation v a = wordPopulation w a) ↔
      ∃ e : Equiv.Perm I, w ∘ e = v := by
  classical
  constructor
  · intro h
    let es : ∀ a, {i // v i = a} ≃ {i // w i = a} :=
      fun a => Fintype.equivOfCardEq (h a)
    refine ⟨Equiv.ofFiberEquiv es, ?_⟩
    funext i
    exact Equiv.ofFiberEquiv_map es i
  · rintro ⟨e, rfl⟩ a
    exact wordPopulation_reindex w e a

theorem samePopulation_card_mul (w : I → A) :
    Fintype.card {v : I → A // ∀ a, wordPopulation v a = wordPopulation w a} *
      (∏ a, (wordPopulation w a).factorial) = (Fintype.card I).factorial := by
  classical
  let G := DomMulAct (Equiv.Perm I)
  let : Fintype G := Fintype.ofEquiv (Equiv.Perm I) DomMulAct.mk
  let eOrbit : {v : I → A // ∀ a, wordPopulation v a = wordPopulation w a} ≃
      MulAction.orbit G w :=
    Equiv.subtypeEquivRight fun v => by
      rw [samePopulation_iff_permutation, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨e, he⟩
        exact ⟨DomMulAct.mk e, he⟩
      · rintro ⟨g, hg⟩
        exact ⟨DomMulAct.mk.symm g, hg⟩
  let eStab : MulAction.stabilizer G w ≃
      {e : Equiv.Perm I // w ∘ e = w} :=
    Equiv.subtypeEquiv DomMulAct.mk.symm fun _ => DomMulAct.mem_stabilizer_iff
  have hstab : Fintype.card (MulAction.stabilizer G w) =
      ∏ a, (wordPopulation w a).factorial := by
    rw [Fintype.card_congr eStab]
    exact DomMulAct.stabilizer_card w
  have hgroup : Fintype.card G = (Fintype.card I).factorial :=
    (Fintype.card_congr DomMulAct.mk.symm).trans Fintype.card_perm
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G w
  rw [← Fintype.card_congr eOrbit, hstab, hgroup] at h
  exact h

theorem exactWords_card (counts : A → ℕ) :
    Fintype.card (ExactWords counts) = Nat.multinomial Finset.univ counts := by
  classical
  obtain ⟨w⟩ := exactWords_nonempty counts
  let e : ExactWords counts ≃
      {v : Fin (∑ a, counts a) → A // ∀ a,
        wordPopulation v a = wordPopulation w.val a} :=
    Equiv.subtypeEquivRight fun v => by simp only [w.property]
  have h := samePopulation_card_mul w.val
  rw [← Fintype.card_congr e] at h
  simp only [w.property, Fintype.card_fin] at h
  exact Nat.eq_div_of_mul_eq_left
    (ne_of_gt (Nat.prod_factorial_pos Finset.univ counts)) h

theorem exactWords_card_pos (counts : A → ℕ) : 0 < Fintype.card (ExactWords counts) := by
  rw [exactWords_card]
  exact Nat.multinomial_pos Finset.univ counts

theorem exactWords_card_le (counts : A → ℕ) :
    Fintype.card (ExactWords counts) ≤ (Fintype.card A) ^ (∑ a, counts a) := by
  classical
  calc
    Fintype.card (ExactWords counts) ≤
        Fintype.card (Fin (∑ a, counts a) → A) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = _ := by simp

end MatrixMultiplication.Foundation





namespace MatrixMultiplication.Foundation

open scoped BigOperators

variable {A B I : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]

abbrev PopulationWords (I : Type*) [Fintype I] (counts : A → ℕ) :=
  {w : I → A // ∀ a, wordPopulation w a = counts a}

noncomputable def populationWordsEquiv (counts : A → ℕ)
    (h : Fintype.card I = ∑ a, counts a) : PopulationWords I counts ≃ ExactWords counts := by
  let e : I ≃ Fin (∑ a, counts a) := Fintype.equivFinOfCardEq h
  exact
    { toFun := fun w =>
        ⟨w.val ∘ e.symm, fun a => (wordPopulation_reindex w.val e.symm a).trans (w.property a)⟩
      invFun := fun w =>
        ⟨w.val ∘ e, fun a => (wordPopulation_reindex w.val e a).trans (w.property a)⟩
      left_inv := by
        intro w
        apply Subtype.ext
        funext i
        simp
      right_inv := by
        intro w
        apply Subtype.ext
        funext i
        simp }

theorem populationWords_card (counts : A → ℕ)
    (h : Fintype.card I = ∑ a, counts a) :
    Fintype.card (PopulationWords I counts) = Nat.multinomial Finset.univ counts := by
  rw [Fintype.card_congr (populationWordsEquiv counts h), exactWords_card]

abbrev ConditionalWords (w : I → A) (counts : A → B → ℕ) :=
  {r : I → B // ∀ a b, Fintype.card {i // w i = a ∧ r i = b} = counts a b}

def fiberWordEquiv (w : I → A) : (I → B) ≃ (∀ a, {i // w i = a} → B) where
  toFun r _ i := r i.val
  invFun r i := r (w i) ⟨i, rfl⟩
  left_inv _ := rfl
  right_inv := by
    intro r
    funext a i
    rcases i with ⟨i, hi⟩
    cases hi
    rfl

omit [Fintype A] [Fintype B] [DecidableEq I] in
theorem wordPopulation_fiber (w : I → A) (r : I → B) (a : A) (b : B) :
    wordPopulation (fun i : {i // w i = a} => r i.val) b =
      Fintype.card {i // w i = a ∧ r i = b} :=
  Fintype.card_congr
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun i => w i = a) (fun i => r i = b))

def conditionalWordsEquiv (w : I → A) (counts : A → B → ℕ) :
    ConditionalWords w counts ≃ ∀ a, PopulationWords {i // w i = a} (counts a) := by
  let e : ConditionalWords w counts ≃
      {r : ∀ a, {i // w i = a} → B // ∀ a b, wordPopulation (r a) b = counts a b} :=
    Equiv.subtypeEquiv (fiberWordEquiv w) fun r => by
      change (∀ a b, Fintype.card {i // w i = a ∧ r i = b} = counts a b) ↔
        ∀ a b, wordPopulation (fun i : {i // w i = a} => r i.val) b = counts a b
      simp only [wordPopulation_fiber]
  exact e.trans (Equiv.subtypePiEquivPi
    (β := fun a : A => {i // w i = a} → B)
    (p := fun a r => ∀ b, wordPopulation r b = counts a b))

theorem conditionalWords_card (w : I → A) (counts : A → B → ℕ)
    (h : ∀ a, wordPopulation w a = ∑ b, counts a b) :
    Fintype.card (ConditionalWords w counts) =
      ∏ a, Nat.multinomial Finset.univ (counts a) := by
  rw [Fintype.card_congr (conditionalWordsEquiv w counts), Fintype.card_pi]
  exact Finset.prod_congr rfl fun a _ => populationWords_card (counts a) (h a)

theorem conditionalWords_card_pos (w : I → A) (counts : A → B → ℕ)
    (h : ∀ a, wordPopulation w a = ∑ b, counts a b) :
    0 < Fintype.card (ConditionalWords w counts) := by
  rw [conditionalWords_card w counts h]
  exact Finset.prod_pos fun a _ => Nat.multinomial_pos Finset.univ (counts a)

theorem conditionalWords_nonempty (w : I → A) (counts : A → B → ℕ)
    (h : ∀ a, wordPopulation w a = ∑ b, counts a b) :
    Nonempty (ConditionalWords w counts) :=
  Fintype.card_pos_iff.mp (conditionalWords_card_pos w counts h)

theorem conditionalWords_nonempty_iff (w : I → A) (counts : A → B → ℕ) :
    Nonempty (ConditionalWords w counts) ↔
      ∀ a, wordPopulation w a = ∑ b, counts a b := by
  constructor
  · rintro ⟨r⟩ a
    calc
      wordPopulation w a =
          ∑ b, wordPopulation (fun i : {i // w i = a} => r.val i.val) b :=
        (wordPopulation_sum _).symm
      _ = ∑ b, counts a b := by
        apply Finset.sum_congr rfl
        intro b _
        rw [wordPopulation_fiber, r.property]
  · exact conditionalWords_nonempty w counts

omit [DecidableEq A] [DecidableEq B] in
theorem multinomial_prod_counts (counts : A × B → ℕ) :
    Nat.multinomial Finset.univ counts =
      Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) *
        ∏ a, Nat.multinomial Finset.univ (fun b => counts (a, b)) := by
  apply Nat.mul_left_cancel (Nat.prod_factorial_pos Finset.univ counts)
  rw [Nat.multinomial_spec]
  symm
  calc
    (∏ ab, (counts ab).factorial) *
        (Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) *
          ∏ a, Nat.multinomial Finset.univ (fun b => counts (a, b))) =
        ((∏ a, ∏ b, (counts (a, b)).factorial) *
          ∏ a, Nat.multinomial Finset.univ (fun b => counts (a, b))) *
          Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) := by
      rw [Fintype.prod_prod_type]
      ac_rfl
    _ = (∏ a, ((∏ b, (counts (a, b)).factorial) *
          Nat.multinomial Finset.univ (fun b => counts (a, b)))) *
          Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ a, (∑ b, counts (a, b)).factorial) *
          Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) := by
      congr 1
      apply Finset.prod_congr rfl
      intro a _
      exact Nat.multinomial_spec Finset.univ (fun b => counts (a, b))
    _ = (∑ a, ∑ b, counts (a, b)).factorial :=
      Nat.multinomial_spec Finset.univ (fun a => ∑ b, counts (a, b))
    _ = (∑ ab, counts ab).factorial := by rw [Fintype.sum_prod_type]

theorem exactWords_card_prod_counts (counts : A × B → ℕ) :
    Fintype.card (ExactWords counts) =
      Fintype.card (ExactWords (fun a => ∑ b, counts (a, b))) *
        ∏ a, Fintype.card (ExactWords (fun b => counts (a, b))) := by
  simpa only [exactWords_card] using multinomial_prod_counts counts

theorem exactWords_card_eq_coarse_mul_conditional (counts : A × B → ℕ)
    (w : ExactWords (fun a => ∑ b, counts (a, b))) :
    Fintype.card (ExactWords counts) =
      Fintype.card (ExactWords (fun a => ∑ b, counts (a, b))) *
        Fintype.card (ConditionalWords w.val (fun a b => counts (a, b))) := by
  rw [conditionalWords_card w.val (fun a b => counts (a, b)) w.property]
  simpa only [exactWords_card] using multinomial_prod_counts counts

end MatrixMultiplication.Foundation





noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators

universe u v

def pushforwardCounts {A B : Type*} [Fintype A]
    (counts : A → ℕ) (label : A → B) (b : B) : ℕ := by
  classical
  exact ∑ a, if label a = b then counts a else 0

theorem pushforwardCounts_sum {A B : Type*} [Fintype A] [Fintype B]
    (counts : A → ℕ) (label : A → B) :
    (∑ b, pushforwardCounts counts label b) = ∑ a, counts a := by
  classical
  unfold pushforwardCounts
  rw [Finset.sum_comm]
  simp

theorem pushforwardCounts_apply {A B : Type*} [Fintype A]
    (counts : A → ℕ) (label : A → B) (hinjective : Function.Injective label)
    (a : A) : pushforwardCounts counts label (label a) = counts a := by
  classical
  simp [pushforwardCounts, hinjective.eq_iff]

theorem pushforwardCounts_sum_pair {A B C : Type*}
    [Fintype A] [Fintype C] (counts : A → ℕ)
    (coarse : A → B) (fine : A → C) (b : B) :
    (∑ c, pushforwardCounts counts (fun a => (coarse a, fine a)) (b, c)) =
      pushforwardCounts counts coarse b := by
  classical
  unfold pushforwardCounts
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hab : coarse a = b
  · simp [Prod.mk.injEq, hab]
  · simp [Prod.mk.injEq, hab]

theorem pushforwardCounts_factorial_prod_of_injective {A B : Type*}
    [Fintype A] [Fintype B] (counts : A → ℕ) (label : A → B)
    (hinjective : Function.Injective label) :
    (∏ b, (pushforwardCounts counts label b).factorial) =
      ∏ a, (counts a).factorial := by
  classical
  have hfactor (b : B) : (pushforwardCounts counts label b).factorial =
      ∏ a, if label a = b then (counts a).factorial else 1 := by
    by_cases hb : ∃ a, label a = b
    · obtain ⟨a, rfl⟩ := hb
      rw [pushforwardCounts_apply counts label hinjective]
      simp [hinjective.eq_iff]
    · simp [pushforwardCounts, not_exists.mp hb]
  simp_rw [hfactor]
  rw [Finset.prod_comm]
  simp

theorem multinomial_pushforwardCounts_of_injective {A B : Type*}
    [Fintype A] [Fintype B] (counts : A → ℕ) (label : A → B)
    (hinjective : Function.Injective label) :
    Nat.multinomial Finset.univ (pushforwardCounts counts label) =
      Nat.multinomial Finset.univ counts := by
  simp only [Nat.multinomial, pushforwardCounts_sum,
    pushforwardCounts_factorial_prod_of_injective counts label hinjective]

namespace LabelHierarchyCounts

variable {Label : ℕ → Type u} [∀ n, Fintype (Label n)]

def refinementCount (counts : ∀ n, LabelRecord Label n → ℕ) (n : ℕ) : ℕ :=
  ∏ r : LabelRecord Label n,
    Nat.multinomial Finset.univ (fun s : Label n => counts (n + 1) (r, s))

theorem multinomial_succ (counts : ∀ n, LabelRecord Label n → ℕ) (n : ℕ)
    (compatible : ∀ r, counts n r = ∑ s : Label n, counts (n + 1) (r, s)) :
    Nat.multinomial Finset.univ (counts (n + 1)) =
      Nat.multinomial Finset.univ (counts n) * refinementCount counts n := by
  classical
  erw [multinomial_prod_counts]
  have hrows : (fun r => ∑ s : Label n, counts (n + 1) (r, s)) = counts n :=
    funext fun r => (compatible r).symm
  rw [hrows]
  rfl

theorem pool_multinomial_eq_one_of_zero
    (counts : ∀ n, LabelRecord Label n → ℕ) (n : ℕ)
    (compatible : ∀ r, counts n r = ∑ s : Label n, counts (n + 1) (r, s))
    (r : LabelRecord Label n) (hzero : counts n r = 0) :
    Nat.multinomial Finset.univ (fun s : Label n => counts (n + 1) (r, s)) = 1 := by
  have hchild (s : Label n) : counts (n + 1) (r, s) = 0 := by
    apply Nat.eq_zero_of_le_zero
    calc
      counts (n + 1) (r, s) ≤ ∑ t : Label n, counts (n + 1) (r, t) :=
        Finset.single_le_sum (f := fun t : Label n => counts (n + 1) (r, t))
          (fun t _ => Nat.zero_le _) (Finset.mem_univ s)
      _ = 0 := (compatible r).symm.trans hzero
  simp [Nat.multinomial, hchild]

theorem multinomial_eq_refinementCount_product
    (counts : ∀ n, LabelRecord Label n → ℕ) (depth : ℕ)
    (compatible : ∀ n < depth, ∀ r,
      counts n r = ∑ s : Label n, counts (n + 1) (r, s)) :
    Nat.multinomial Finset.univ (counts depth) =
      ∏ n ∈ Finset.range depth, refinementCount counts n := by
  classical
  induction depth with
  | zero =>
      have hroot : (Finset.univ : Finset (LabelRecord Label 0)) = {PUnit.unit} := rfl
      erw [hroot, Nat.multinomial_singleton]
      simp
  | succ depth ih =>
      rw [multinomial_succ counts depth (compatible depth (Nat.lt_succ_self depth))]
      rw [ih (fun n hn => compatible n (Nat.lt_trans hn (Nat.lt_succ_self depth))),
        Finset.prod_range_succ]

def sourcePrefixCounts {A : Type v} [Fintype A] (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (n : ℕ) : LabelRecord Label n → ℕ :=
  pushforwardCounts counts (labelRecordOf labels n)

theorem sourcePrefixCounts_compatible {A : Type v} [Fintype A]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (n : ℕ)
    (r : LabelRecord Label n) :
    sourcePrefixCounts counts labels n r =
      ∑ s : Label n, sourcePrefixCounts counts labels (n + 1) (r, s) :=
  (pushforwardCounts_sum_pair counts (labelRecordOf labels n) (labels n) r).symm

theorem source_refinementCount_product {A : Type v} [Fintype A]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    (∏ n ∈ Finset.range depth, refinementCount (sourcePrefixCounts counts labels) n) =
      Nat.multinomial Finset.univ counts := by
  calc
    (∏ n ∈ Finset.range depth, refinementCount (sourcePrefixCounts counts labels) n) =
        Nat.multinomial Finset.univ (sourcePrefixCounts counts labels depth) :=
      (multinomial_eq_refinementCount_product (sourcePrefixCounts counts labels) depth
        (fun n _ r => sourcePrefixCounts_compatible counts labels n r)).symm
    _ = Nat.multinomial Finset.univ counts :=
      multinomial_pushforwardCounts_of_injective counts
        (labelRecordOf labels depth) hinjective

theorem source_refinementCount_product_eq_exactWords_card
    {A : Type v} [Fintype A] [DecidableEq A]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    (∏ n ∈ Finset.range depth, refinementCount (sourcePrefixCounts counts labels) n) =
      Fintype.card (ExactWords counts) := by
  rw [source_refinementCount_product counts labels depth hinjective, exactWords_card]

end LabelHierarchyCounts
end MatrixMultiplication.Foundation






namespace MatrixMultiplication.JointPairClassWindows

open MatrixMultiplication.Foundation

attribute [local instance] Classical.propDecidable

variable {I A C : Type*} [Fintype I] [Fintype A] [Fintype C]
  [DecidableEq I] [DecidableEq A] [DecidableEq C]

abbrev Fiber (k : I → C) (c : C) := {i : I // k i = c}

def fiberWord (z : I → A) (k : I → C) (c : C) : Fiber k c → A :=
  fun i => z i.val

omit [Fintype A] [Fintype C] [DecidableEq I] in
theorem fiber_population (z : I → A) (k : I → C) (f : A → C)
    (hf : ∀ i, f (z i) = k i) (c : C) (a : A) :
    wordPopulation (fiberWord z k c) a =
      if f a = c then wordPopulation z a else 0 := by
  classical
  by_cases ha : f a = c
  · rw [ite_eq_left ha]
    unfold wordPopulation
    apply Fintype.card_congr
    exact
      { toFun := fun i => ⟨i.val.val, i.property⟩
        invFun := fun i => ⟨⟨i.val, by rw [← hf i.val, i.property, ha]⟩, i.property⟩
        left_inv := fun ⟨⟨i, hi⟩, hia⟩ => rfl
        right_inv := fun ⟨i, hia⟩ => rfl }
  · rw [ite_eq_right ha]
    let : IsEmpty {i : Fiber k c // fiberWord z k c i = a} :=
      ⟨fun i => ha (calc
        f a = f (z i.val.val) := congrArg f i.property.symm
        _ = k i.val.val := hf _
        _ = c := i.val.property)⟩
    exact Fintype.card_eq_zero

omit [Fintype C] [DecidableEq I] in
theorem fiber_card (k : I → C) (c : C) :
    Fintype.card (Fiber k c) = wordPopulation k c := rfl

def conditionalCenter (f : A → C) (c : C) (q : A → ℝ) (mass : ℝ) : A → ℝ :=
  fun a => if f a = c then q a / mass else 0

omit [Fintype A] [Fintype C] [DecidableEq I] in
theorem fiber_window (z : I → A) (k : I → C) (f : A → C)
    (hf : ∀ i, f (z i) = k i) (c : C) (q : A → ℝ) (mass η : ℝ)
    (hmass : 0 < mass) (hη : 0 ≤ η)
    (hclass : (Fintype.card (Fiber k c) : ℝ) = (Fintype.card I : ℝ) * mass)
    (hwindow : ∀ a, |(wordPopulation z a : ℝ) / Fintype.card I - q a| ≤ η) :
    ∀ a, |(wordPopulation (fiberWord z k c) a : ℝ) / Fintype.card (Fiber k c) -
      conditionalCenter f c q mass a| ≤ η / mass := by
  intro a
  rw [fiber_population z k f hf c a]
  by_cases ha : f a = c
  · simp only [ha, ite_true, conditionalCenter]
    rw [hclass]
    have hid : (wordPopulation z a : ℝ) / ((Fintype.card I : ℝ) * mass) - q a / mass =
        ((wordPopulation z a : ℝ) / Fintype.card I - q a) / mass := by
      rw [sub_div, div_div]
    rw [hid, abs_div, abs_of_pos hmass]
    exact div_le_div_of_nonneg_right (hwindow a) hmass.le
  · simp only [ha, ite_false, Nat.cast_zero, zero_div, conditionalCenter, sub_zero, abs_zero]
    exact div_nonneg hη hmass.le

omit [Fintype A] [Fintype C] [DecidableEq I] in
theorem fiber_count_window (z : I → A) (k : I → C) (f : A → C)
    (hf : ∀ i, f (z i) = k i) (c : C) (q : A → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hwindow : ∀ a,
      |(wordPopulation z a : ℝ) - (Fintype.card I : ℝ) * q a| ≤ (Fintype.card I : ℝ) * η) :
    ∀ a, |(wordPopulation (fiberWord z k c) a : ℝ) -
      (Fintype.card I : ℝ) * (if f a = c then q a else 0)| ≤ (Fintype.card I : ℝ) * η := by
  intro a
  rw [fiber_population z k f hf c a]
  by_cases ha : f a = c
  · simpa only [ha, ite_true] using hwindow a
  · simp only [ha, ite_false, Nat.cast_zero, mul_zero, sub_zero, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hη

end MatrixMultiplication.JointPairClassWindows

end
end

end MatrixAllFields

end OAI
