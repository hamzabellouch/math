import OAI.Combinatorics.LowSpaceSubsetSum.Counting.BalancedPartitions
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.PrimeHash
import Mathlib.Data.Nat.Log

namespace OAI

/-!
# Bounded rejection sampling

The executable sampler reads at most the supplied number of candidates. All
probability statements use the uniform law on the finite candidate tuples,
which is exactly independent sampling with replacement.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

variable {Ω : Type*}

theorem finiteUniformProbability_eq_cardRatio [Fintype Ω]
    (A : Ω → Prop) [DecidablePred A] :
    finiteUniformProbability A = (Fintype.card {x : Ω // A x} : ℝ) / Fintype.card Ω := by
  simp only [finiteUniformProbability, ← Nat.card_eq_fintype_card]

/-- Read candidates in their given order and return the first eligible value. -/
def firstAccept (A : Ω → Prop) [DecidablePred A] :
    (N : ℕ) → (Fin N → Ω) → Option Ω
  | 0, _ => none
  | N + 1, f => if A (f 0) then some (f 0)
      else firstAccept A N (fun i => f i.succ)

theorem firstAccept_eq_none_iff (A : Ω → Prop) [DecidablePred A]
    (N : ℕ) (f : Fin N → Ω) : firstAccept A N f = none ↔ ∀ i, ¬A (f i) := by
  induction N with
  | zero => simp [firstAccept]
  | succ N ih =>
    simp only [firstAccept, Fin.forall_fin_succ]
    split_ifs with h
    · simp [h]
    · simpa [h] using ih (fun i => f i.succ)

theorem firstAccept_some_eligible (A : Ω → Prop) [DecidablePred A]
    (N : ℕ) (f : Fin N → Ω) {a : Ω} (h : firstAccept A N f = some a) : A a := by
  induction N with
  | zero => simp [firstAccept] at h
  | succ N ih =>
    simp only [firstAccept] at h
    split_ifs at h with ha
    · exact Option.some.inj h ▸ ha
    · exact ih (fun i => f i.succ) h

theorem firstAccept_failure [Fintype Ω] [Nonempty Ω]
    (A : Ω → Prop) [DecidablePred A] (N : ℕ) :
    finiteUniformProbability (fun f : Fin N → Ω => firstAccept A N f = none) =
      (1 - finiteUniformProbability A) ^ N := by
  have hpred : (fun f : Fin N → Ω => firstAccept A N f = none) =
      (fun f => ∀ i, ¬A (f i)) := by
    funext f
    exact propext (firstAccept_eq_none_iff A N f)
  rw [hpred, uniform_family_failure]

noncomputable def firstAcceptCount [Fintype Ω]
    (A : Ω → Prop) [DecidablePred A] (N : ℕ) (a : Ω) : ℕ := by
  classical
  exact Fintype.card {f : Fin N → Ω // firstAccept A N f = some a}

private def firstAcceptFiberSuccEquiv (A : Ω → Prop) [DecidablePred A]
    (N : ℕ) (a : Ω) (ha : A a) :
    {f : Fin (N + 1) → Ω // firstAccept A (N + 1) f = some a} ≃
      (Fin N → Ω) ⊕
        ({b : Ω // ¬A b} × {f : Fin N → Ω // firstAccept A N f = some a}) := by
  let forward : {f : Fin (N + 1) → Ω // firstAccept A (N + 1) f = some a} →
      (Fin N → Ω) ⊕
        ({b : Ω // ¬A b} × {f : Fin N → Ω // firstAccept A N f = some a}) :=
    fun f => if h : A (f.1 0) then Sum.inl (fun i => f.1 i.succ)
      else Sum.inr (⟨f.1 0, h⟩, ⟨fun i => f.1 i.succ, by
        simpa [firstAccept, h] using f.2⟩)
  let backward : (Fin N → Ω) ⊕
      ({b : Ω // ¬A b} × {f : Fin N → Ω // firstAccept A N f = some a}) →
      {f : Fin (N + 1) → Ω // firstAccept A (N + 1) f = some a} :=
    Sum.elim
      (fun f => ⟨Fin.cons a f, by simp [firstAccept, ha]⟩)
      (fun z => ⟨Fin.cons z.1.1 z.2.1, by simpa [firstAccept, z.1.2] using z.2.2⟩)
  refine ⟨forward, backward, ?_, ?_⟩
  · intro f
    apply Subtype.ext
    by_cases h : A (f.1 0)
    · have he : f.1 0 = a := Option.some.inj (by
        simpa [firstAccept, h] using f.2)
      change (backward (forward f)).val = f.val
      simp only [forward, dite_eq_left h, backward, Sum.elim_inl]
      funext i
      refine Fin.cases ?_ (fun _ => rfl) i
      simpa using he.symm
    · change (backward (forward f)).val = f.val
      simp only [forward, dite_eq_right h, backward, Sum.elim_inr]
      exact Fin.cons_self_tail _
  · intro z
    rcases z with f | ⟨⟨b, hb⟩, ⟨f, hf⟩⟩
    · simp [forward, backward, ha]
    · simp [forward, backward, hb]

theorem firstAcceptCount_succ [Fintype Ω]
    (A : Ω → Prop) [DecidablePred A] (N : ℕ) (a : Ω) (ha : A a) :
    firstAcceptCount A (N + 1) a = Fintype.card Ω ^ N +
      Fintype.card {b : Ω // ¬A b} * firstAcceptCount A N a := by
  classical
  unfold firstAcceptCount
  rw [Fintype.card_congr (firstAcceptFiberSuccEquiv A N a ha)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]

theorem firstAcceptCount_conservation [Fintype Ω]
    (A : Ω → Prop) [DecidablePred A] (N : ℕ) (a : Ω) (ha : A a) :
    Fintype.card {b : Ω // A b} * firstAcceptCount A N a +
      Fintype.card {b : Ω // ¬A b} ^ N = Fintype.card Ω ^ N := by
  classical
  induction N with
  | zero => simp [firstAcceptCount, firstAccept]
  | succ N ih =>
    rw [firstAcceptCount_succ A N a ha, pow_succ, pow_succ]
    have hsum : Fintype.card {b : Ω // A b} + Fintype.card {b : Ω // ¬A b} =
        Fintype.card Ω := by
      rw [Fintype.card_subtype_compl]
      exact Nat.add_sub_of_le (Fintype.card_subtype_le A)
    calc
      _ = Fintype.card {b : Ω // A b} * Fintype.card Ω ^ N +
          Fintype.card {b : Ω // ¬A b} *
            (Fintype.card {b : Ω // A b} * firstAcceptCount A N a +
              Fintype.card {b : Ω // ¬A b} ^ N) := by ring
      _ = _ := by rw [ih, ← add_mul, hsum, mul_comm]

/-- The exact subprobability of every eligible return value. -/
theorem firstAccept_value_probability [Fintype Ω] [Nonempty Ω]
    (A : Ω → Prop) [DecidablePred A] (N : ℕ) (a : Ω) (ha : A a) :
    finiteUniformProbability (fun f : Fin N → Ω => firstAccept A N f = some a) =
      (1 - (1 - finiteUniformProbability A) ^ N) / Fintype.card {b : Ω // A b} := by
  classical
  have hc : (Fintype.card {b : Ω // A b} : ℝ) * firstAcceptCount A N a +
      (Fintype.card {b : Ω // ¬A b} : ℝ) ^ N = (Fintype.card Ω : ℝ) ^ N := by
    exact_mod_cast firstAcceptCount_conservation A N a ha
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hA : (Fintype.card {b : Ω // A b} : ℝ) ≠ 0 := by
    have : Nonempty {b : Ω // A b} := ⟨⟨a, ha⟩⟩
    exact_mod_cast Fintype.card_ne_zero
  have hvalue : finiteUniformProbability
      (fun f : Fin N → Ω => firstAccept A N f = some a) =
      (firstAcceptCount A N a : ℝ) / (Fintype.card Ω : ℝ) ^ N := by
    simp only [finiteUniformProbability, firstAcceptCount, ← Nat.card_eq_fintype_card,
      Nat.card_fun, Nat.card_fin, Nat.cast_pow]
  rw [hvalue, ← finiteUniformProbability_compl A, finiteUniformProbability_eq_cardRatio]
  rw [div_pow]
  field_simp [hΩ, hA]
  nlinarith [hc]

theorem firstAccept_acceptance [Fintype Ω] [Nonempty Ω]
    (A : Ω → Prop) [DecidablePred A] (N : ℕ) :
    finiteUniformProbability (fun f : Fin N → Ω => firstAccept A N f ≠ none) =
      1 - (1 - finiteUniformProbability A) ^ N := by
  rw [finiteUniformProbability_compl, firstAccept_failure]

/-- Conditioning only this call on acceptance gives the uniform eligible law. -/
theorem firstAccept_conditional_uniform [Fintype Ω] [Nonempty Ω]
    (A : Ω → Prop) [DecidablePred A] (N : ℕ) (hN : 0 < N) (a : Ω) (ha : A a) :
    finiteUniformProbability (fun f : Fin N → Ω => firstAccept A N f = some a) /
        finiteUniformProbability (fun f : Fin N → Ω => firstAccept A N f ≠ none) =
      1 / Fintype.card {b : Ω // A b} := by
  classical
  have hA : 0 < finiteUniformProbability A := by
    have : Nonempty {b : Ω // A b} := ⟨⟨a, ha⟩⟩
    rw [finiteUniformProbability_eq_cardRatio]
    exact div_pos (by exact_mod_cast Fintype.card_pos) (by exact_mod_cast Fintype.card_pos)
  have hA1 := finiteUniformProbability_le_one A
  have hpow : (1 - finiteUniformProbability A) ^ N < 1 :=
    pow_lt_one₀ (by linarith) (by linarith) (by omega)
  rw [firstAccept_value_probability A N a ha, firstAccept_acceptance]
  have hnz : 1 - (1 - finiteUniformProbability A) ^ N ≠ 0 := by linarith
  field_simp

theorem firstAccept_failure_le_exp [Fintype Ω] [Nonempty Ω]
    (A : Ω → Prop) [DecidablePred A] (N : ℕ) {ρ : ℝ}
    (hρ : ρ ≤ finiteUniformProbability A) :
    finiteUniformProbability (fun f : Fin N → Ω => firstAccept A N f = none) ≤
      Real.exp (-(N : ℝ) * ρ) := by
  rw [firstAccept_failure]
  have hA1 := finiteUniformProbability_le_one A
  have hbase : 1 - finiteUniformProbability A ≤ Real.exp (-ρ) := by
    linarith [Real.add_one_le_exp (-ρ)]
  have h := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - finiteUniformProbability A) hbase N
  rw [← Real.exp_nat_mul] at h
  convert h using 1
  congr 1
  ring

private theorem card_fin_lt (D B : ℕ) (hDB : D ≤ B) :
    Fintype.card {x : Fin B // x.val < D} = D := by
  let e : {x : Fin B // x.val < D} ≃ Fin D :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.trans_le hDB⟩, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin D)

/-- Rejection predicate for the `clog₂ D` fresh low bits. -/
def rangeEligible (D : ℕ) (x : Fin (2 ^ Nat.clog 2 D)) : Prop := x.val < D

instance (D : ℕ) : DecidablePred (rangeEligible D) := fun _ => inferInstanceAs (Decidable (_ < _))

theorem rangeEligible_probability (D : ℕ) :
    finiteUniformProbability (rangeEligible D) = (D : ℝ) / (2 : ℝ) ^ Nat.clog 2 D := by
  have hc : Fintype.card {x : Fin (2 ^ Nat.clog 2 D) // rangeEligible D x} = D := by
    calc
      _ = Nat.card {x : Fin (2 ^ Nat.clog 2 D) // rangeEligible D x} :=
        Nat.card_eq_fintype_card.symm
      _ = Nat.card {x : Fin (2 ^ Nat.clog 2 D) // x.val < D} := rfl
      _ = Fintype.card {x : Fin (2 ^ Nat.clog 2 D) // x.val < D} :=
        Nat.card_eq_fintype_card
      _ = D := card_fin_lt D (2 ^ Nat.clog 2 D) (Nat.le_pow_clog (by decide : 1 < 2) D)
  rw [finiteUniformProbability_eq_cardRatio]
  rw [hc, Fintype.card_fin]
  norm_cast

theorem rangeEligible_probability_lower {D : ℕ} (hD : 1 < D) :
    (1 : ℝ) / 2 ≤ finiteUniformProbability (rangeEligible D) := by
  rw [rangeEligible_probability]
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hD
  have hpos := Nat.clog_pos (by decide : 1 < 2) hD
  have hbits : 2 ^ Nat.clog 2 D ≤ 2 * D := by
    rw [show Nat.clog 2 D = (Nat.clog 2 D).pred + 1 from
      (Nat.succ_pred_eq_of_pos hpos).symm, pow_succ]
    omega
  have hb : (2 : ℝ) ^ Nat.clog 2 D ≤ 2 * D := by exact_mod_cast hbits
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ Nat.clog 2 D)).mpr
  linarith

theorem rangeSampler_failure {D : ℕ} (hD : 1 < D) (n : ℕ) :
    finiteUniformProbability (fun f : Fin (n ^ 3) → Fin (2 ^ Nat.clog 2 D) =>
      firstAccept (rangeEligible D) (n ^ 3) f = none) ≤ 1 / (2 : ℝ) ^ (n ^ 3) := by
  rw [firstAccept_failure]
  have hlow := rangeEligible_probability_lower hD
  have hupp := finiteUniformProbability_le_one (rangeEligible D)
  have h := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - finiteUniformProbability (rangeEligible D))
    (by linarith : 1 - finiteUniformProbability (rangeEligible D) ≤ 1 / 2) (n ^ 3)
  simpa only [one_div_pow] using h

/-- Exactly the prime test performed on an `ell`-bit candidate. -/
def primeEligible (ell : ℕ) (x : Fin (2 ^ ell)) : Prop := x.val ∈ primeRange ell

instance (ell : ℕ) : DecidablePred (primeEligible ell) := fun _ => inferInstanceAs (Decidable (_ ∈ _))

theorem primeEligible_probability {ell : ℕ} (hell : 4 ≤ ell) :
    finiteUniformProbability (primeEligible ell) =
      ((primeRange ell).card : ℝ) / (2 : ℝ) ^ ell := by
  classical
  let e : {x : Fin (2 ^ ell) // primeEligible ell x} ≃ {p : ℕ // p ∈ primeRange ell} :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun p => ⟨⟨p.1, primeRange_lt hell p.2⟩, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [finiteUniformProbability_eq_cardRatio]
  rw [Fintype.card_congr e, Fintype.card_coe, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]

theorem primeEligible_probability_lower {ell : ℕ} (hell : 4 ≤ ell) :
    1 / (4 * (ell : ℝ)) ≤ finiteUniformProbability (primeEligible ell) := by
  rw [primeEligible_probability hell]
  have h : (2 : ℝ) ^ ell ≤ 4 * ell * (primeRange ell).card := by
    exact_mod_cast primeRange_card_lower hell
  have he : (0 : ℝ) < ell := by exact_mod_cast (by omega : 0 < ell)
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * ell) (by positivity)).mpr
  simpa only [one_mul, mul_comm] using h

theorem primeSampler_failure {ell n : ℕ} (hell : 4 ≤ ell) (hen : ell ≤ n) :
    finiteUniformProbability (fun f : Fin (n ^ 3) → Fin (2 ^ ell) =>
      firstAccept (primeEligible ell) (n ^ 3) f = none) ≤
      Real.exp (-((n : ℝ) ^ 2 / 4)) := by
  apply (firstAccept_failure_le_exp (primeEligible ell) (n ^ 3)
    (primeEligible_probability_lower hell)).trans
  apply Real.exp_le_exp.mpr
  have he : (0 : ℝ) < ell := by exact_mod_cast (by omega : 0 < ell)
  have hen' : (ell : ℝ) ≤ n := by exact_mod_cast hen
  push_cast
  rw [neg_mul, mul_one_div, neg_le_neg_iff]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * ell)).mpr
  nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.mpr hen')]

/-- Complete an exhausted bounded call with an independent eligible backup.
This is the ideal marginal in the explicit one-call coupling. -/
def completedFirstAccept (A : Ω → Prop) [DecidablePred A] (N : ℕ)
    (f : Fin N → Ω) (backup : {a : Ω // A a}) : Ω :=
  (firstAccept A N f).getD backup.val

theorem completedFirstAccept_eligible (A : Ω → Prop) [DecidablePred A] (N : ℕ)
    (f : Fin N → Ω) (backup : {a : Ω // A a}) : A (completedFirstAccept A N f backup) := by
  cases h : firstAccept A N f with
  | none => simpa [completedFirstAccept, h] using backup.property
  | some a => simpa [completedFirstAccept, h] using firstAccept_some_eligible A N f h

theorem completedFirstAccept_mismatch_iff (A : Ω → Prop) [DecidablePred A] (N : ℕ)
    (f : Fin N → Ω) (backup : {a : Ω // A a}) :
    some (completedFirstAccept A N f backup) ≠ firstAccept A N f ↔
      firstAccept A N f = none := by
  cases h : firstAccept A N f <;> simp [completedFirstAccept, h]

private def firstAcceptNoneEquiv (A : Ω → Prop) [DecidablePred A] (N : ℕ) :
    {f : Fin N → Ω // firstAccept A N f = none} ≃ (Fin N → {a : Ω // ¬A a}) where
  toFun f i := ⟨f.val i, (firstAccept_eq_none_iff A N f.val).mp f.property i⟩
  invFun f := ⟨fun i => (f i).val,
    (firstAccept_eq_none_iff A N _).mpr (fun i => (f i).property)⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

private theorem firstAccept_none_card [Fintype Ω]
    (A : Ω → Prop) [DecidablePred A] (N : ℕ) :
    Nat.card {f : Fin N → Ω // firstAccept A N f = none} =
      Fintype.card {a : Ω // ¬A a} ^ N := by
  rw [Nat.card_congr (firstAcceptNoneEquiv A N), Nat.card_fun]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]

private noncomputable def completedFirstAcceptFiberEquiv
    (A : Ω → Prop) [DecidablePred A] (N : ℕ) (a : Ω) (ha : A a) :
    {z : (Fin N → Ω) × {b : Ω // A b} // completedFirstAccept A N z.1 z.2 = a} ≃
      ({f : Fin N → Ω // firstAccept A N f = some a} × {b : Ω // A b}) ⊕
        {f : Fin N → Ω // firstAccept A N f = none} := by
  classical
  let forward :
      {z : (Fin N → Ω) × {b : Ω // A b} // completedFirstAccept A N z.1 z.2 = a} →
      ({f : Fin N → Ω // firstAccept A N f = some a} × {b : Ω // A b}) ⊕
        {f : Fin N → Ω // firstAccept A N f = none} := fun z =>
    if h : firstAccept A N z.1.1 = none then Sum.inr ⟨z.1.1, h⟩ else
      Sum.inl (⟨z.1.1, by
        cases hf : firstAccept A N z.1.1 with
        | none => exact (h hf).elim
        | some b =>
          have hb : b = a := by simpa [completedFirstAccept, hf] using z.2
          simp only [hb]⟩, z.1.2)
  let backward :
      ({f : Fin N → Ω // firstAccept A N f = some a} × {b : Ω // A b}) ⊕
        {f : Fin N → Ω // firstAccept A N f = none} →
      {z : (Fin N → Ω) × {b : Ω // A b} // completedFirstAccept A N z.1 z.2 = a} :=
    Sum.elim
      (fun z => ⟨(z.1.val, z.2), by simp [completedFirstAccept, z.1.property]⟩)
      (fun f => ⟨(f.val, ⟨a, ha⟩), by simp [completedFirstAccept, f.property]⟩)
  refine ⟨forward, backward, ?_, ?_⟩
  · intro z
    apply Subtype.ext
    by_cases h : firstAccept A N z.1.1 = none
    · simp only [forward, dite_eq_left h, backward, Sum.elim_inr]
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        have hb : z.1.2.val = a := by simpa [completedFirstAccept, h] using z.2
        exact hb.symm
    · simp only [forward, dite_eq_right h, backward, Sum.elim_inl]
  · intro z
    rcases z with ⟨f, backup⟩ | f
    · simp [forward, backward, f.property]
    · simp [forward, backward, f.property]

/-- The ideal marginal is exactly uniform; the backup introduces no bias. -/
theorem completedFirstAccept_uniform [Fintype Ω] [Nonempty Ω]
    (A : Ω → Prop) [DecidablePred A] (N : ℕ) (a : Ω) (ha : A a) :
    finiteUniformProbability
      (fun z : (Fin N → Ω) × {b : Ω // A b} => completedFirstAccept A N z.1 z.2 = a) =
        1 / Fintype.card {b : Ω // A b} := by
  classical
  have hc : Nat.card
      {z : (Fin N → Ω) × {b : Ω // A b} // completedFirstAccept A N z.1 z.2 = a} =
        Fintype.card Ω ^ N := by
    rw [Nat.card_congr (completedFirstAcceptFiberEquiv A N a ha), Nat.card_sum,
      Nat.card_prod, firstAccept_none_card]
    have he : Nat.card {f : Fin N → Ω // firstAccept A N f = some a} =
        firstAcceptCount A N a := by
      simp only [firstAcceptCount, ← Nat.card_eq_fintype_card]
    rw [he, Nat.card_eq_fintype_card]
    simpa only [Nat.mul_comm] using firstAcceptCount_conservation A N a ha
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hA : (Fintype.card {b : Ω // A b} : ℝ) ≠ 0 := by
    have : Nonempty {b : Ω // A b} := ⟨⟨a, ha⟩⟩
    exact_mod_cast Fintype.card_ne_zero
  simp only [finiteUniformProbability, ← Nat.card_eq_fintype_card, Nat.card_prod,
    Nat.card_fun, Nat.card_fin, Nat.cast_mul, Nat.cast_pow]
  rw [hc, Nat.cast_pow]
  simp only [Nat.card_eq_fintype_card]
  field_simp [hΩ, hA]

theorem finiteUniformProbability_fst [Fintype Ω] {Ψ : Type*} [Fintype Ψ] [Nonempty Ψ]
    (P : Ω → Prop) :
    finiteUniformProbability (fun z : Ω × Ψ => P z.1) = finiteUniformProbability P := by
  classical
  let e : {z : Ω × Ψ // P z.1} ≃ {x : Ω // P x} × Ψ :=
    { toFun := fun z => (⟨z.1.1, z.2⟩, z.1.2)
      invFun := fun z => ⟨(z.1.val, z.2), z.1.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc : Nat.card {z : Ω × Ψ // P z.1} = Nat.card {x : Ω // P x} * Nat.card Ψ := by
    rw [Nat.card_congr e, Nat.card_prod]
  have hΨ : (Nat.card Ψ : ℝ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  simp only [finiteUniformProbability, ← Nat.card_eq_fintype_card, Nat.card_prod,
    Nat.cast_mul]
  rw [hc, Nat.cast_mul]
  exact mul_div_mul_right _ _ hΨ

/-- In the explicit finite coupling, disagreement is exactly exhaustion of the
bounded call. The first marginal is the original independent candidate tuple. -/
theorem firstAccept_coupling_mismatch [Fintype Ω] [Nonempty Ω]
    (A : Ω → Prop) [DecidablePred A] [Nonempty {a : Ω // A a}] (N : ℕ) :
    finiteUniformProbability
      (fun z : (Fin N → Ω) × {a : Ω // A a} =>
        some (completedFirstAccept A N z.1 z.2) ≠ firstAccept A N z.1) =
      (1 - finiteUniformProbability A) ^ N := by
  have hpred : (fun z : (Fin N → Ω) × {a : Ω // A a} =>
      some (completedFirstAccept A N z.1 z.2) ≠ firstAccept A N z.1) =
      (fun z => firstAccept A N z.1 = none) := by
    funext z
    exact propext (completedFirstAccept_mismatch_iff A N z.1 z.2)
  rw [hpred]
  calc
    _ = finiteUniformProbability (fun f : Fin N → Ω => firstAccept A N f = none) :=
      finiteUniformProbability_fst (Ψ := {a : Ω // A a})
        (fun f : Fin N → Ω => firstAccept A N f = none)
    _ = _ := firstAccept_failure A N

end LowSpaceSubsetSum

end OAI
