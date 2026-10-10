import Mathlib

namespace OAI

namespace Balanced.PatternMoments

open scoped BigOperators

variable {Ω A Y : Type*} [Fintype Ω] [Fintype A] [Fintype Y]

def expectation (p : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, p ω * f ω

lemma expectation_sum (p : Ω → ℝ) (f : A → Ω → ℝ) :
    expectation p (fun ω => ∑ a, f a ω) = ∑ a, expectation p (f a) := by
  classical
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

lemma expectation_mul_const (p : Ω → ℝ) (f : Ω → ℝ) (c : ℝ) :
    expectation p (fun ω => f ω * c) = expectation p f * c := by
  simp only [expectation, Finset.sum_mul, mul_assoc]

lemma expectation_const_mul (p : Ω → ℝ) (f : Ω → ℝ) (c : ℝ) :
    expectation p (fun ω => c * f ω) = c * expectation p f := by
  simp [expectation, Finset.mul_sum, mul_left_comm]

theorem weighted_fiber_bound [DecidableEq Y] (p Z f : Ω → ℝ) (expose : Ω → Y) (M : ℝ)
    (hf : ∀ ω, 0 ≤ f ω)
    (hconst : ∀ ω ω', expose ω = expose ω' → f ω = f ω')
    (hbound : ∀ y, (∑ ω : {ω // expose ω = y}, p ω * Z ω) ≤
      M * ∑ ω : {ω // expose ω = y}, p ω) :
    expectation p (fun ω => f ω * Z ω) ≤ M * expectation p f := by
  classical
  unfold expectation
  rw [← Fintype.sum_fiberwise expose (fun ω => p ω * (f ω * Z ω)),
    ← Fintype.sum_fiberwise expose (fun ω => p ω * f ω), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  cases isEmpty_or_nonempty {ω // expose ω = y} with
  | inl h =>
      let := h
      simp
  | inr h =>
      obtain ⟨x⟩ := h
      have heq (ω : {ω // expose ω = y}) : f ω = f x :=
        hconst ω x (ω.property.trans x.property.symm)
      simp_rw [heq]
      calc
        (∑ ω : {ω // expose ω = y}, p ω * (f x * Z ω)) =
            f x * ∑ ω : {ω // expose ω = y}, p ω * Z ω := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ω _
          ring
        _ ≤ f x * (M * ∑ ω : {ω // expose ω = y}, p ω) :=
          mul_le_mul_of_nonneg_left (hbound y) (hf x)
        _ = M * ∑ ω : {ω // expose ω = y}, p ω * f x := by
          rw [← Finset.sum_mul]
          ring

def count (I : A → Ω → ℝ) (ω : Ω) : ℝ := ∑ a, I a ω

lemma power_expansion (p : Ω → ℝ) (I : A → Ω → ℝ) (n : ℕ) :
    expectation p (fun ω => count I ω ^ n) =
      ∑ a : Fin n → A, expectation p (fun ω => ∏ i, I (a i) ω) := by
  classical
  simp_rw [count, Fintype.sum_pow]
  exact expectation_sum p _

theorem moment_bound_of_prefix_bounds
    (p : Ω → ℝ) (I : A → Ω → ℝ) (s : ℕ) (M : ℝ)
    (hp : ∑ ω, p ω = 1) (hM : 0 ≤ M)
    (hprefix : ∀ n < s, ∀ a : Fin n → A,
      expectation p (fun ω => (∏ i, I (a i) ω) * count I ω) ≤
        M * expectation p (fun ω => ∏ i, I (a i) ω)) :
    expectation p (fun ω => count I ω ^ s) ≤ M ^ s := by
  classical
  have main : ∀ n ≤ s, expectation p (fun ω => count I ω ^ n) ≤ M ^ n := by
    intro n
    induction n with
    | zero =>
        intro _
        simp [expectation, hp]
    | succ n ih =>
        intro hn
        have hns : n < s := Nat.lt_of_succ_le hn
        calc
          expectation p (fun ω => count I ω ^ (n + 1)) =
              ∑ a : Fin n → A,
                expectation p (fun ω => (∏ i, I (a i) ω) * count I ω) := by
            simp_rw [pow_succ, count, Fintype.sum_pow, Finset.sum_mul]
            exact expectation_sum p _
          _ ≤ ∑ a : Fin n → A,
                M * expectation p (fun ω => ∏ i, I (a i) ω) := by
            exact Finset.sum_le_sum fun a _ => hprefix n hns a
          _ = M * expectation p (fun ω => count I ω ^ n) := by
            rw [← Finset.mul_sum, power_expansion]
          _ ≤ M * M ^ n := mul_le_mul_of_nonneg_left (ih (Nat.le_of_succ_le hn)) hM
          _ = M ^ (n + 1) := by ring
  exact main s le_rfl

def scheduledWeight (W : List A → ℝ) (overlap : List A → A → Prop)
    [∀ pre a, Decidable (overlap pre a)] :
    List Bool → List A → ℝ
  | [], pre => W pre
  | root :: rest, pre => ∑ a,
      if root = true ∨ overlap pre a then
        scheduledWeight W overlap rest (a :: pre) else 0

def scheduleCost (M L : ℝ) : List Bool → ℝ
  | [] => 1
  | root :: rest => (if root then M else L) * scheduleCost M L rest

lemma scheduleCost_nonneg {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (schedule : List Bool) : 0 ≤ scheduleCost M L schedule := by
  induction schedule with
  | nil => simp [scheduleCost]
  | cons root rest ih =>
      simp only [scheduleCost]
      exact mul_nonneg (by split <;> assumption) ih

theorem scheduledWeight_le
    (W : List A → ℝ) (overlap : List A → A → Prop)
    [∀ pre a, Decidable (overlap pre a)]
    (N : ℕ) (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hfree : ∀ pre, pre.length < N →
      (∑ a, W (a :: pre)) ≤ M * W pre)
    (htouch : ∀ pre, pre.length < N →
      (∑ a, if overlap pre a then W (a :: pre) else 0) ≤ L * W pre)
    (schedule : List Bool) (pre : List A)
    (hlen : pre.length + schedule.length ≤ N) :
    scheduledWeight W overlap schedule pre ≤
      scheduleCost M L schedule * W pre := by
  classical
  induction schedule generalizing pre with
  | nil => simp [scheduledWeight, scheduleCost]
  | cons root rest ih =>
      have hshort : pre.length < N := by simp only [List.length_cons] at hlen; omega
      have hrest (a : A) : (a :: pre).length + rest.length ≤ N := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlen
      have hnonneg := scheduleCost_nonneg hM hL rest
      calc
        scheduledWeight W overlap (root :: rest) pre ≤
            ∑ a, if root = true ∨ overlap pre a then
              scheduleCost M L rest * W (a :: pre) else 0 := by
          apply Finset.sum_le_sum
          intro a _
          split_ifs
          · exact ih (a :: pre) (hrest a)
          · exact le_rfl
        _ = scheduleCost M L rest *
            (∑ a, if root = true ∨ overlap pre a then W (a :: pre) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          split_ifs <;> simp
        _ ≤ scheduleCost M L rest * ((if root then M else L) * W pre) := by
          apply mul_le_mul_of_nonneg_left _ hnonneg
          cases root with
          | false => simpa using htouch pre hshort
          | true => simpa using hfree pre hshort
        _ = scheduleCost M L (root :: rest) * W pre := by
          simp only [scheduleCost]
          ring

def rootCount : List Bool → ℕ
  | [] => 0
  | root :: rest => (if root then 1 else 0) + rootCount rest

lemma scheduleCost_eq (C q : ℝ) (schedule : List Bool) :
    scheduleCost (C * q) C schedule = C ^ schedule.length * q ^ rootCount schedule := by
  induction schedule with
  | nil => simp [scheduleCost, rootCount]
  | cons root rest ih =>
      cases root <;> simp [scheduleCost, rootCount, ih, pow_succ, pow_add] <;> ring

theorem scheduleCost_le_power {C q : ℝ} (hC : 0 ≤ C) (hq : 1 ≤ q)
    (schedule : List Bool) (s : ℕ) (hroots : rootCount schedule ≤ s) :
    scheduleCost (C * q) C schedule ≤ C ^ schedule.length * q ^ s := by
  rw [scheduleCost_eq]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hroots) (pow_nonneg hC _)

attribute [local instance] Classical.propDecidable

def scheduleAllowed (overlap : List A → A → Prop) :
    List Bool → List A → List A → Prop
  | [], [], _ => True
  | root :: rest, a :: labels, pre =>
      (root = true ∨ overlap pre a) ∧ scheduleAllowed overlap rest labels (a :: pre)
  | _, _, _ => False

theorem scheduledWeight_eq_sum
    (W : List A → ℝ) (overlap : List A → A → Prop)
    [∀ pre a, Decidable (overlap pre a)]
    (schedule : List Bool) (pre : List A) :
    scheduledWeight W overlap schedule pre =
      ∑ a : Fin schedule.length → A,
        if scheduleAllowed overlap schedule (List.ofFn a) pre then
          W ((List.ofFn a).reverse ++ pre) else 0 := by
  classical
  induction schedule generalizing pre with
  | nil => simp [scheduledWeight, scheduleAllowed]
  | cons root rest ih =>
      simp only [List.length_cons]
      rw [← (Fin.consEquiv (fun _ : Fin (rest.length + 1) => A)).sum_comp
        (fun a => if scheduleAllowed overlap (root :: rest) (List.ofFn a) pre then
          W ((List.ofFn a).reverse ++ pre) else 0), Fintype.sum_prod_type]
      simp only [scheduledWeight]
      apply Finset.sum_congr rfl
      intro a _
      rw [ih]
      by_cases ha : root = true ∨ overlap pre a
      · simp [ha, Fin.consEquiv, scheduleAllowed, List.reverse_cons,
          List.append_assoc]
      · simp [ha, Fin.consEquiv, scheduleAllowed]

theorem scheduledWeight_eq_sum_of_length
    (W : List A → ℝ) (overlap : List A → A → Prop)
    [∀ pre a, Decidable (overlap pre a)]
    (schedule : List Bool) (pre : List A) (n : ℕ) (hlen : schedule.length = n) :
    scheduledWeight W overlap schedule pre =
      ∑ a : Fin n → A, if scheduleAllowed overlap schedule (List.ofFn a) pre then
        W ((List.ofFn a).reverse ++ pre) else 0 := by
  subst n
  exact scheduledWeight_eq_sum W overlap schedule pre

theorem sum_le_card_mul_of_reordered_cover
    {T : Type*} [Fintype T]
    (W : A → ℝ) (eligible : A → Prop) (test : T → A → Prop)
    (reorder : T → Equiv.Perm A) (B : ℝ)
    (hW : ∀ a, 0 ≤ W a)
    (hinvariant : ∀ t a, W (reorder t a) = W a)
    (hcover : ∀ a, eligible a → ∃ t, test t (reorder t a))
    (hbound : ∀ t, (∑ a, if test t a then W a else 0) ≤ B) :
    (∑ a, if eligible a then W a else 0) ≤ (Fintype.card T : ℝ) * B := by
  classical
  calc
    (∑ a, if eligible a then W a else 0) ≤
        ∑ a, ∑ t, if test t (reorder t a) then W (reorder t a) else 0 := by
      apply Finset.sum_le_sum
      intro a _
      by_cases he : eligible a
      · obtain ⟨t, ht⟩ := hcover a he
        rw [ite_eq_left he, ← hinvariant t a]
        exact (by simpa [ht] using
          (Finset.single_le_sum
            (f := fun t => if test t (reorder t a) then W (reorder t a) else 0)
            (fun t _ => by split_ifs <;> first | exact hW _ | exact le_rfl)
            (Finset.mem_univ t) :
            (if test t (reorder t a) then W (reorder t a) else 0) ≤
              ∑ t, if test t (reorder t a) then W (reorder t a) else 0))
      · simp only [ite_eq_right he]
        exact Finset.sum_nonneg fun t _ => by split_ifs <;> first | exact hW _ | exact le_rfl
    _ = ∑ t, ∑ a, if test t a then W a else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      exact Equiv.sum_comp (reorder t) (fun a => if test t a then W a else 0)
    _ ≤ ∑ _t : T, B := Finset.sum_le_sum fun t _ => hbound t
    _ = (Fintype.card T : ℝ) * B := by simp

def tuplePermutation {n : ℕ} (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n → A) where
  toFun a i := a (π i)
  invFun a i := a (π.symm i)
  left_inv a := by funext i; simp
  right_inv a := by funext i; simp

theorem weighted_ordering_bound
    (W : List A → ℝ) (overlap : List A → A → Prop)
    [∀ pre a, Decidable (overlap pre a)]
    (n s : ℕ) (C q : ℝ) (hC : 0 ≤ C) (hq : 1 ≤ q)
    (eligible : (Fin n → A) → Prop)
    (hW : ∀ pre, 0 ≤ W pre) (hnil : W [] = 1)
    (hperm : ∀ l₁ l₂, l₁.Perm l₂ → W l₁ = W l₂)
    (hfree : ∀ pre, pre.length < n →
      (∑ a, W (a :: pre)) ≤ (C * q) * W pre)
    (htouch : ∀ pre, pre.length < n →
      (∑ a, if overlap pre a then W (a :: pre) else 0) ≤ C * W pre)
    (hordering : ∀ a, eligible a → ∃ π : Equiv.Perm (Fin n),
      ∃ σ : Fin n → Bool, rootCount (List.ofFn σ) ≤ s ∧
        scheduleAllowed overlap (List.ofFn σ) (List.ofFn (fun i => a (π i))) []) :
    (∑ a : Fin n → A, if eligible a then W (List.ofFn a).reverse else 0) ≤
      (Nat.factorial n : ℝ) * 2 ^ n * C ^ n * q ^ s := by
  classical
  let T := Equiv.Perm (Fin n) × (Fin n → Bool)
  let test : T → (Fin n → A) → Prop := fun t a =>
    rootCount (List.ofFn t.2) ≤ s ∧
      scheduleAllowed overlap (List.ofFn t.2) (List.ofFn a) []
  have hinvariant (t : T) (a : Fin n → A) :
      W (List.ofFn (tuplePermutation t.1 a)).reverse = W (List.ofFn a).reverse := by
    apply hperm
    exact (List.reverse_perm _).trans ((t.1.ofFn_comp_perm a).trans (List.reverse_perm _).symm)
  have hcover (a : Fin n → A) (ha : eligible a) :
      ∃ t : T, test t (tuplePermutation t.1 a) := by
    obtain ⟨π, σ, hs, ha'⟩ := hordering a ha
    exact ⟨(π, σ), hs, ha'⟩
  have hbound (t : T) :
      (∑ a : Fin n → A, if test t a then W (List.ofFn a).reverse else 0) ≤
        C ^ n * q ^ s := by
    by_cases hs : rootCount (List.ofFn t.2) ≤ s
    · have hexpand := scheduledWeight_eq_sum_of_length W overlap (List.ofFn t.2) [] n
        (List.length_ofFn (f := t.2))
      simp only [List.append_nil] at hexpand
      calc
        (∑ a : Fin n → A, if test t a then W (List.ofFn a).reverse else 0) =
            scheduledWeight W overlap (List.ofFn t.2) [] := by
          simpa only [test, hs, true_and] using hexpand.symm
        _ ≤ scheduleCost (C * q) C (List.ofFn t.2) * W [] := by
          apply scheduledWeight_le W overlap n (C * q) C
            (mul_nonneg hC (le_trans (by norm_num) hq)) hC hfree htouch
          simp
        _ ≤ C ^ n * q ^ s := by
          rw [hnil, mul_one]
          simpa using scheduleCost_le_power hC hq (List.ofFn t.2) s hs
    · simp [test, hs, mul_nonneg (pow_nonneg hC _) (pow_nonneg (by linarith : 0 ≤ q) _)]
  have hfinal := sum_le_card_mul_of_reordered_cover
    (fun a : Fin n → A => W (List.ofFn a).reverse) eligible test
    (fun t : T => tuplePermutation t.1) (C ^ n * q ^ s)
    (fun a => hW _) hinvariant hcover (fun t => by
      convert hbound t using 1
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> rfl)
  convert hfinal using 1
  simp only [T, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin,
    Fintype.card_fun, Fintype.card_bool, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

end Balanced.PatternMoments

end OAI
