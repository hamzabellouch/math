import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Table

namespace OAI

namespace MetricKMedianRecovery.Categorical

open FiniteSampling

def advance {E Ω : Type*} [DecidableEq Ω] {a : ℕ}
    (r : Fin a → Table Ω E) (ω : Ω) (c : Fin a → E) : Fin a → Table Ω E :=
  fun j => Function.update (r j) ω (some (c j))

section TableAdvance
variable {E Ω : Type*} [Fintype E] [DecidableEq E] [Fintype Ω] [DecidableEq Ω]

omit [Fintype E] in
lemma batch_advance {a : ℕ} (r : Fin a → Table Ω E) (ω : Ω) (c : Fin a → E)
    (h : ∀ j, r j ω = none) :
    batch (advance r ω c) c = update (1 / (Fintype.card Ω : ℝ)) (batch r c) := by
  unfold batch update advance
  rw [List.map_ofFn]
  congr 1
  funext j
  rw [tableWeights_update (r j) ω (c j) (h j)]
  rfl

lemma batch_room [Nonempty Ω] {a : ℕ} (r : Fin a → Table Ω E) (ω : Ω)
    (c : Fin a → E) (h : ∀ j, r j ω = none) :
    HasRoom (1 / (Fintype.card Ω : ℝ)) (batch r c) := by
  intro p hp
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
  refine ⟨tableWeights_valid _, ?_⟩
  have hv := (tableWeights_valid (Function.update (r j) ω (some (c j)))).2
  rw [tableWeights_update (r j) ω (c j) (h j), sum_addMass] at hv
  exact hv

end TableAdvance

section SampledDirection
variable {E Ω : Type*} [Fintype E] [DecidableEq E] [Fintype Ω] [Nonempty Ω]

omit [Fintype E] [Nonempty Ω] in
lemma choices_batch {a : ℕ} (r : Fin a → Table Ω E) (c : Fin a → E) :
    choices (batch r c) = Finset.univ.image c := by
  induction a with
  | zero => simp [batch, choices]
  | succ a ih =>
    rw [batch_cons, choices, ih]
    ext e
    simp [Fin.exists_fin_succ, Fin.tail_def, eq_comm]

lemma sampled_direction {a : ℕ} (r : Fin a → Table Ω E)
    (c o : Fin a → E) (g : SetFunction E) (S : Finset E)
    (hmono : Monotone g) (hsub : Diminishing g) {tol : ℝ}
    (hchoice : ∀ j, derivative r c j (o j) g S ≤
      derivative r c j (c j) g S + 2 * tol) :
    g (Finset.univ.image o) - evaluate (batch r c) g S - 2 * a * tol ≤
      direction (batch r c) g S := by
  have hc := categorical_comparison_direction (batch r o) g (batch_valid r o)
    hmono hsub S
  rw [choices_batch, ← evaluate_eq_of_sameWeights (batch r c) (batch r o)
    (batch_sameweights r c o) g S] at hc
  have hd : direction (batch r o) g S ≤ direction (batch r c) g S + 2 * a * tol := by
    rw [direction_sum, direction_sum]
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hchoice j)
    simp_rw [partial_choice r o c]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hs
    nlinarith only [hs]
  linarith

lemma derivative_bounds {a : ℕ} (r : Fin a → Table Ω E) (c : Fin a → E)
    (j : Fin a) (e : E) (g : SetFunction E) (S : Finset E) {M : ℝ}
    (hg : BoundedMarginals g M) :
    0 ≤ derivative r c j e g S ∧ derivative r c j e g S ≤ M := by
  exact evaluate_bounds _ (batch_valid _ c) (marginal g e) 0 M (hg e) S

end SampledDirection

section Select
variable {E : Type*} [Fintype E] [DecidableEq E] {a : ℕ}

noncomputable def select (part : E → Fin a) (hp : Function.Surjective part)
    (score : E → ℝ) (j : Fin a) : E := by
  classical
  have hs : (Finset.univ.filter (fun e => part e = j)).Nonempty := by
    obtain ⟨e,he⟩ := hp j
    exact ⟨e, by simp [he]⟩
  exact (Finset.exists_max_image _ score hs).choose

omit [DecidableEq E] in
lemma select_spec (part : E → Fin a) (hp : Function.Surjective part)
    (score : E → ℝ) (j : Fin a) :
    part (select part hp score j) = j ∧
      ∀ e, part e = j → score e ≤ score (select part hp score j) := by
  classical
  unfold select
  have hs : (Finset.univ.filter (fun e => part e = j)).Nonempty := by
    obtain ⟨e,he⟩ := hp j
    exact ⟨e, by simp [he]⟩
  have h := (Finset.exists_max_image _ score hs).choose_spec
  exact ⟨(Finset.mem_filter.mp h.1).2, fun e he => h.2 e (by simp [he])⟩

end Select
end MetricKMedianRecovery.Categorical

namespace MetricKMedianRecovery.FiniteSampling

def adaptiveRun {S Ω : Type*} (f : S → Ω → S) :
    (n : ℕ) → S → (Fin n → Ω) → S
  | 0, s, _ => s
  | n+1, s, seed => adaptiveRun f n (f s (seed 0)) (Fin.tail seed)

lemma adaptiveRun_invariant {S Ω : Type*} (f : S → Ω → S) (Inv : S → Prop)
    (hInv : ∀ s, Inv s → ∀ ω, Inv (f s ω)) (n : ℕ)
    (s : S) (hs : Inv s) (seed : Fin n → Ω) : Inv (adaptiveRun f n s seed) := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih => exact ih _ (hInv s hs (seed 0)) (Fin.tail seed)

lemma adaptiveRun_growth {S Ω : Type*} (f : S → Ω → S) (bad : S → Ω → Prop)
    (Inv : S → Prop) (clock : S → ℕ) (V : S → ℝ) (T : ℕ) {r Q : ℝ}
    (hr : 0 ≤ r)
    (hInv : ∀ s, Inv s → ∀ ω, Inv (f s ω))
    (hclock : ∀ s, clock s < T → ∀ ω, clock (f s ω) = clock s + 1)
    (hstep : ∀ s, Inv s → clock s < T → ∀ ω, ¬bad s ω →
      r * V s + (1-r) * Q ≤ V (f s ω))
    (n : ℕ) (s : S) (hs : Inv s) (hn : clock s + n ≤ T)
    (seed : Fin n → Ω) (hg : ¬adaptiveBad f bad n s seed) :
    r^n * V s + (1-r^n) * Q ≤ V (adaptiveRun f n s seed) := by
  induction n generalizing s with
  | zero => simp [adaptiveRun]
  | succ n ih =>
    have hlt : clock s < T := by omega
    have hgood : ¬bad s (seed 0) ∧
        ¬adaptiveBad f bad n (f s (seed 0)) (Fin.tail seed) := not_or.mp hg
    have hi := ih (f s (seed 0)) (hInv s hs (seed 0))
      (by rw [hclock s hlt]; omega) (Fin.tail seed) hgood.2
    have hl := mul_le_mul_of_nonneg_left
      (hstep s hs hlt (seed 0) hgood.1) (pow_nonneg hr n)
    change _ ≤ V (adaptiveRun f n (f s (seed 0)) (Fin.tail seed))
    rw [pow_succ]
    nlinarith

end MetricKMedianRecovery.FiniteSampling

end OAI
