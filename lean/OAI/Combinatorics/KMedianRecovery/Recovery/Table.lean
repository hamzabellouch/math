import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.SetFunction
import OAI.Combinatorics.KMedianRecovery.Recovery.Average

namespace OAI

namespace MetricKMedianRecovery
namespace Categorical

open FiniteSampling
variable {E Ω : Type*} [Fintype E] [DecidableEq E] [Fintype Ω] [Nonempty Ω]

abbrev Table (Ω E : Type*) := Ω → Option E

noncomputable def tableWeights (r : Table Ω E) (e : E) : ℝ :=
  probability (fun ω => r ω = some e)

omit [Nonempty Ω] in
lemma average_option (r : Table Ω E) (v : Option E → ℝ) :
    average (fun ω => v (r ω)) = probability (fun ω => r ω = none) * v none +
      ∑ e, tableWeights r e * v (some e) := by
  classical
  unfold tableWeights probability
  simp_rw [← average_mul_const]
  rw [← average_sum, ← average_add]
  apply average_congr
  intro ω
  by_cases hn : r ω = none
  · simp [hn]
  · have hex : ∃ e, r ω = some e := by
      cases h : r ω with
      | none => exact (hn h).elim
      | some e => exact ⟨e,rfl⟩
    obtain ⟨e,he⟩ := hex
    simp [he]

lemma tableWeights_total (r : Table Ω E) :
    probability (fun ω => r ω = none) + ∑ e, tableWeights r e = 1 := by
  have h := average_option r (fun _ => 1)
  simpa only [average_const, mul_one] using h.symm

lemma tableWeights_valid (r : Table Ω E) : IsWeight (tableWeights r) := by
  refine ⟨fun e => probability_nonneg _, ?_⟩
  have h := tableWeights_total r
  have hp := probability_nonneg (fun ω => r ω = none)
  linarith

lemma table_operator (r : Table Ω E) (g : SetFunction E) (S : Finset E) :
    operator (tableWeights r) g S = average (fun ω =>
      match r ω with | none => g S | some e => g (insert e S)) := by
  rw [average_option r (fun o => match o with | none => g S | some e => g (insert e S))]
  have ht := tableWeights_total r
  dsimp only
  unfold operator
  rw [show 1 - ∑ e, tableWeights r e = probability (fun ω => r ω = none) by linarith]

omit [Nonempty Ω] in
lemma average_update [DecidableEq Ω] (X : Ω → ℝ) (ω : Ω) (v : ℝ) :
    average (Function.update X ω v) = average X + (v-X ω)/(Fintype.card Ω) := by
  rw [average, Fintype.expect_eq_sum_div_card, average, Fintype.expect_eq_sum_div_card]
  have hsum : ∑ ξ, Function.update X ω v ξ = (∑ ξ, X ξ) + (v-X ω) := by
    have hp (ξ : Ω) : Function.update X ω v ξ =
        X ξ + if ξ = ω then v-X ω else 0 := by
      by_cases h : ξ = ω <;> simp [h]
    simp_rw [hp, Finset.sum_add_distrib]
    simp
  rw [hsum, add_div]

omit [Fintype E] [Nonempty Ω] in
lemma tableWeights_update [DecidableEq Ω] (r : Table Ω E) (ω : Ω) (e : E)
    (hr : r ω = none) :
    tableWeights (Function.update r ω (some e)) =
      addMass (tableWeights r) e (1 / (Fintype.card Ω : ℝ)) := by
  classical
  funext f
  unfold tableWeights probability
  calc
    _ = average (Function.update (fun ξ => if r ξ = some f then (1:ℝ) else 0) ω
        (if f = e then 1 else 0)) := by
      apply average_congr
      intro ξ
      by_cases h : ξ = ω <;> simp [h, eq_comm]
    _ = _ := by
      rw [average_update]
      unfold addMass
      simp only [hr, reduceCtorEq, ite_false, sub_zero]
      split_ifs <;> simp
      all_goals
        apply average_congr
        intro ξ
        by_cases h : r ξ = some f <;> simp [h]

omit [Fintype E] [DecidableEq E] [Nonempty Ω] in
lemma average_comm {Ξ : Type*} [Fintype Ξ] (X : Ω → Ξ → ℝ) :
    average (fun ω => average (X ω)) = average (fun ξ => average (fun ω => X ω ξ)) := by
  exact Finset.expect_comm Finset.univ Finset.univ X

def put (o : Option E) (S : Finset E) : Finset E :=
  match o with | none => S | some e => insert e S

def draw : (a : ℕ) → (Fin a → Table Ω E) → (Fin a → Ω) → Finset E → Finset E
  | 0, _, _, S => S
  | a+1, r, seed, S => put (r 0 (seed 0)) (draw a (Fin.tail r) (Fin.tail seed) S)

noncomputable def batch {a : ℕ} (r : Fin a → Table Ω E) (c : Fin a → E) : Batch E :=
  List.ofFn (fun j => (tableWeights (r j), c j))

omit [Fintype E] [DecidableEq E] [Nonempty Ω] in
lemma batch_cons {a : ℕ} (r : Fin (a+1) → Table Ω E) (c : Fin (a+1) → E) :
    batch r c = (tableWeights (r 0), c 0) :: batch (Fin.tail r) (Fin.tail c) := by
  exact List.ofFn_succ

lemma average_draw (a : ℕ) (r : Fin a → Table Ω E) (c : Fin a → E)
    (g : SetFunction E) (S : Finset E) :
    average (fun seed : Fin a → Ω => g (draw a r seed S)) = evaluate (batch r c) g S := by
  induction a generalizing g S with
  | zero => simp [draw, batch, evaluate]
  | succ a ih =>
    rw [average_fin_succ, batch_cons]
    change average (fun ω => average (fun seed : Fin a → Ω =>
      g (put (r 0 ω) (draw a (Fin.tail r) seed S)))) = _
    rw [average_comm]
    have ht (U : Finset E) : average (fun ω => g (put (r 0 ω) U)) =
        operator (tableWeights (r 0)) g U := by
      rw [table_operator]
      apply average_congr
      intro ω
      cases r 0 ω <;> rfl
    simp_rw [ht]
    exact ih (Fin.tail r) (Fin.tail c) _ S

omit [Fintype E] [Fintype Ω] [Nonempty Ω] in
lemma mem_draw {a : ℕ} (r : Fin a → Table Ω E) (seed : Fin a → Ω)
    (S : Finset E) (e : E) :
    e ∈ draw a r seed S ↔ e ∈ S ∨ ∃ j, r j (seed j) = some e := by
  induction a with
  | zero => simp [draw]
  | succ a ih =>
    simp only [draw]
    have he : (∃ j : Fin (a+1), r j (seed j) = some e) ↔
      r 0 (seed 0) = some e ∨ ∃ j : Fin a, r j.succ (seed j.succ) = some e := Fin.exists_fin_succ
    rw [he]
    cases h : r 0 (seed 0) with
    | none => simpa [put, h, Fin.tail_def] using ih (Fin.tail r) (Fin.tail seed)
    | some f =>
      simp only [put, Finset.mem_insert, ih, Fin.tail_def, Option.some.injEq]
      tauto

lemma batch_valid {a : ℕ} (r : Fin a → Table Ω E) (c : Fin a → E) :
    ∀ p ∈ batch r c, IsWeight p.1 := by
  intro p hp
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
  exact tableWeights_valid _

omit [Fintype E] [DecidableEq E] [Nonempty Ω] in
lemma batch_length {a : ℕ} (r : Fin a → Table Ω E) (c : Fin a → E) :
    (batch r c).length = a := List.length_ofFn

lemma operator_zero (g : SetFunction E) : operator (fun _ => 0) g = g := by
  funext S
  simp [operator]

omit [Fintype E] [DecidableEq E] [Nonempty Ω] in
lemma tableWeights_none : tableWeights (fun _ : Ω => (none : Option E)) = fun _ => 0 := by
  funext e
  unfold tableWeights
  simpa using probability_false (Ω := Ω)

omit [Fintype E] [DecidableEq E] [Nonempty Ω] in
lemma batch_sameweights {a : ℕ} (r : Fin a → Table Ω E) (c d : Fin a → E) :
    SameWeights (batch r c) (batch r d) := by
  induction a with
  | zero => exact List.Forall₂.nil
  | succ a ih =>
    rw [batch_cons, batch_cons]
    exact List.Forall₂.cons rfl (ih (Fin.tail r) (Fin.tail c) (Fin.tail d))

noncomputable def derivative {a : ℕ} (r : Fin a → Table Ω E) (c : Fin a → E)
    (j : Fin a) (e : E) (g : SetFunction E) (S : Finset E) : ℝ :=
  evaluate (batch (Function.update r j (fun _ => none)) c) (marginal g e) S

omit [Nonempty Ω] in
lemma partial_choice {a : ℕ} (r : Fin a → Table Ω E) (c d : Fin a → E)
    (j : Fin a) (e : E) (g : SetFunction E) (S : Finset E) :
    derivative r c j e g S = derivative r d j e g S := by
  exact evaluate_eq_of_sameWeights _ _ (batch_sameweights _ _ _) _ _

lemma partial_sample {a : ℕ} (r : Fin a → Table Ω E) (c : Fin a → E)
    (j : Fin a) (e : E) (g : SetFunction E) (S : Finset E) :
    derivative r c j e g S = average (fun seed : Fin a → Ω =>
      marginal g e (draw a (Function.update r j (fun _ => none)) seed S)) := by
  exact (average_draw _ _ _ _ _).symm

omit [Nonempty Ω] in
lemma partial_zero {a : ℕ} (r : Fin (a+1) → Table Ω E) (c : Fin (a+1) → E)
    (e : E) (g : SetFunction E) (S : Finset E) :
    derivative r c 0 e g S = evaluate (batch (Fin.tail r) (Fin.tail c)) (marginal g e) S := by
  unfold derivative
  rw [batch_cons]
  simp only [Function.update_self, tableWeights_none, evaluate, operator_zero]
  have ht : Fin.tail (Function.update r 0 (fun _ => none)) = Fin.tail r := by
    funext j
    simp [Fin.tail_def]
  rw [ht]

omit [Nonempty Ω] in
lemma partial_succ {a : ℕ} (r : Fin (a+1) → Table Ω E) (c : Fin (a+1) → E)
    (j : Fin a) (e : E) (g : SetFunction E) (S : Finset E) :
    derivative r c j.succ e g S =
      derivative (Fin.tail r) (Fin.tail c) j e (operator (tableWeights (r 0)) g) S := by
  unfold derivative
  rw [batch_cons]
  simp only [Function.update_of_ne (Fin.succ_ne_zero j).symm, evaluate]
  have ht : Fin.tail (Function.update r j.succ (fun _ => none)) =
      Function.update (Fin.tail r) j (fun _ => none) := by
    funext k
    by_cases h : k = j
    · subst k; simp [Fin.tail_def]
    · simp [Fin.tail_def, Fin.succ_inj, h]
  rw [ht]
  congr 1
  funext U
  exact (marginal_operator _ _ _ _).symm

omit [Nonempty Ω] in
lemma direction_sum {a : ℕ} (r : Fin a → Table Ω E) (c : Fin a → E)
    (g : SetFunction E) (S : Finset E) :
    direction (batch r c) g S = ∑ j, derivative r c j (c j) g S := by
  induction a generalizing g with
  | zero => simp [batch, direction]
  | succ a ih =>
    rw [batch_cons, direction, Fin.sum_univ_succ, partial_zero]
    simp_rw [partial_succ]
    congr 1
    exact ih _ _ _

end Categorical
end MetricKMedianRecovery

end OAI
