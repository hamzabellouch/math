import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.DirectionChoiceErrors
import OAI.Combinatorics.KMedianRecovery.Recovery.Advance

namespace OAI

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

noncomputable def tableValue {E Ω : Type*} [DecidableEq E] [Fintype Ω]
    {a : ℕ} (g : SetFunction E) (r : Fin a → Table Ω E) : ℝ :=
  average (fun seed : Fin a → Ω => g (draw a r seed ∅))

section GreedyStep
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ}

abbrev GreedyState (E : Type*) (a T : ℕ) := ℕ × (Fin a → Table (Fin T) E)
abbrev OracleSeed (E : Type*) (a T L : ℕ) := E → Fin L → Fin a → Fin T

noncomputable def marginalSample (part : E → Fin a) (g : SetFunction E)
    (r : Fin a → Table (Fin T) E) (e : E) (seed : Fin a → Fin T) : ℝ :=
  marginal g e (draw a (Function.update r (part e) (fun _ => none)) seed ∅)

noncomputable def scores (part : E → Fin a) (g : SetFunction E)
    (r : Fin a → Table (Fin T) E) (seed : OracleSeed E a T L) (e : E) : ℝ :=
  sampleMean L (marginalSample part g r e) (seed e)

noncomputable def greedyStep (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (s : GreedyState E a T) (seed : OracleSeed E a T L) :
    GreedyState E a T :=
  if h : s.1 < T then
    (s.1+1, advance s.2 ⟨s.1,h⟩ (select part hp (scores part g s.2 seed)))
  else s

def GreedyInvariant (part : E → Fin a) (s : GreedyState E a T) : Prop :=
  (∀ j ω e, s.2 j ω = some e → part e = j) ∧
    (∀ j ω, s.1 ≤ ω.val → s.2 j ω = none)

lemma greedyStep_clock (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (s : GreedyState E a T) (ht : s.1 < T)
    (seed : OracleSeed E a T L) : (greedyStep part hp g s seed).1 = s.1+1 := by
  simp [greedyStep, ht]

lemma greedyStep_invariant (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (s : GreedyState E a T) (hs : GreedyInvariant part s)
    (seed : OracleSeed E a T L) : GreedyInvariant part (greedyStep part hp g s seed) := by
  by_cases ht : s.1 < T
  · simp only [greedyStep, dite_eq_left ht, GreedyInvariant, advance]
    constructor
    · intro j ω e he
      by_cases hω : ω = (⟨s.1,ht⟩ : Fin T)
      · subst ω
        simp only [Function.update_self, Option.some.injEq] at he
        rw [← he]
        exact (select_spec part hp _ j).1
      · rw [Function.update_of_ne hω] at he
        exact hs.1 j ω e he
    · intro j ω hω
      have hne : ω ≠ (⟨s.1,ht⟩ : Fin T) := by
        intro he
        have := congrArg Fin.val he
        simp only at this
        omega
      rw [Function.update_of_ne hne]
      exact hs.2 j ω (by omega)
  · simpa only [greedyStep, dite_eq_right ht] using hs

omit [Fintype E] in
lemma draw_feasible (part : E → Fin a) (s : GreedyState E a T)
    (hs : GreedyInvariant part s) (seed : Fin a → Fin T) (j : Fin a) :
    ((draw a s.2 seed ∅).filter (fun e => part e = j)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro e he f hf
  obtain ⟨he,hpe⟩ := Finset.mem_filter.mp he
  obtain ⟨hf,hpf⟩ := Finset.mem_filter.mp hf
  obtain ⟨k,hk⟩ : ∃ k, s.2 k (seed k) = some e := by simpa [mem_draw] using he
  obtain ⟨l,hl⟩ : ∃ l, s.2 l (seed l) = some f := by simpa [mem_draw] using hf
  have hkl : k = l := (hs.1 k (seed k) e hk).symm.trans (hpe.trans (hpf.symm.trans
    (hs.1 l (seed l) f hl)))
  subst l
  exact Option.some.inj (hk.symm.trans hl)

lemma marginalSample_average [NeZero T] (part : E → Fin a) (g : SetFunction E)
    (r : Fin a → Table (Fin T) E) (c : Fin a → E) (e : E) :
    average (marginalSample part g r e) = derivative r c (part e) e g ∅ := by
  exact (partial_sample r c (part e) e g ∅).symm

lemma sampled_select_choice [NeZero T] (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (r : Fin a → Table (Fin T) E) (o : Fin a → E)
    (ho : ∀ j, part (o j) = j) (seed : OracleSeed E a T L) {tol : ℝ}
    (hgood : ∀ e, |scores part g r seed e - average (marginalSample part g r e)| ≤ tol) :
    let c := select part hp (scores part g r seed)
    ∀ j, derivative r c j (o j) g ∅ ≤ derivative r c j (c j) g ∅ + 2 * tol := by
  intro c j
  have hc := (select_spec part hp (scores part g r seed) j)
  have hg1 := hgood (c j)
  have hg2 := hgood (o j)
  rw [marginalSample_average part g r c, hc.1] at hg1
  rw [marginalSample_average part g r c, ho] at hg2
  exact two_estimates_choice hg1 hg2 (hc.2 (o j) (ho j))

end GreedyStep
end MetricKMedianRecovery.Categorical

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

section StepBound
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ} [NeZero T]

lemma tableValue_eq (g : SetFunction E) (r : Fin a → Table (Fin T) E) (c : Fin a → E) :
    tableValue g r = evaluate (batch r c) g ∅ := average_draw a r c g ∅

lemma advance_gain (g : SetFunction E) (r : Fin a → Table (Fin T) E)
    (ω : Fin T) (c o : Fin a → E) (hempty : ∀ j, r j ω = none)
    (hmono : Monotone g) (hsub : Diminishing g) {M tol : ℝ} (hM : 0 ≤ M)
    (hg : BoundedMarginals g M)
    (hchoice : ∀ j, derivative r c j (o j) g ∅ ≤
      derivative r c j (c j) g ∅ + 2 * tol) :
    tableValue g r + (1/(T:ℝ)) * (g (Finset.univ.image o) - tableValue g r - 2*a*tol) -
      (a:ℝ)^2 * (1/(T:ℝ))^2 * M ≤ tableValue g (advance r ω c) := by
  have hu := categorical_update_bound (batch r c) g hM
    (show 0 ≤ 1/(T:ℝ) by positivity)
    (by simpa only [Fintype.card_fin] using batch_room r ω c hempty) hg ∅
  have he : update (1/(T:ℝ)) (batch r c) = batch (advance r ω c) c := by
    simpa only [Fintype.card_fin] using (batch_advance r ω c hempty).symm
  rw [he, batch_length, ← tableValue_eq g r c, ← tableValue_eq] at hu
  have hd := sampled_direction r c o g ∅ hmono hsub hchoice
  rw [← tableValue_eq] at hd
  have hm := mul_le_mul_of_nonneg_left hd (show 0 ≤ 1/(T:ℝ) by positivity)
  linarith

lemma advance_recurrence (g : SetFunction E) (r : Fin a → Table (Fin T) E)
    (ω : Fin T) (c o : Fin a → E) (hempty : ∀ j, r j ω = none)
    (hmono : Monotone g) (hsub : Diminishing g) {M tau : ℝ} (hM : 0 ≤ M)
    (hg : BoundedMarginals g M) (ha : 0 < a) (hscale : (a:ℝ)^2 ≤ tau*T)
    (hchoice : ∀ j, derivative r c j (o j) g ∅ ≤
      derivative r c j (c j) g ∅ + 2 * (tau*M/a)) :
    tableValue g r + (g (Finset.univ.image o) - tableValue g r - 3*tau*M)/T ≤
      tableValue g (advance r ω c) := by
  have haR : (a:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt ha)
  have hTR : (T:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne T)
  have hs := advance_gain g r ω c o hempty hmono hsub hM hg hchoice
  have ht : 2*(a:ℝ)*(tau*M/a) = 2*tau*M := by field_simp
  rw [ht] at hs
  have herr : (a:ℝ)^2 * (1/(T:ℝ))^2 * M ≤ tau*M/T := by
    calc
      _ = ((a:ℝ)^2*M) / (T:ℝ)^2 := by ring
      _ ≤ (tau*T*M) / (T:ℝ)^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hscale hM) (sq_nonneg _)
      _ = _ := by field_simp
  calc
    _ = tableValue g r + (1/(T:ℝ)) *
        (g (Finset.univ.image o) - tableValue g r - 2*tau*M) - tau*M/T := by ring
    _ ≤ tableValue g r + (1/(T:ℝ)) *
        (g (Finset.univ.image o) - tableValue g r - 2*tau*M) -
          (a:ℝ)^2 * (1/(T:ℝ))^2 * M := sub_le_sub_left herr _
    _ ≤ _ := hs

def estimationBad (part : E → Fin a) (g : SetFunction E) (M tau : ℝ)
    (s : GreedyState E a T) (seed : OracleSeed E a T L) : Prop :=
  ∃ e, tau*M/a < |scores part g s.2 seed e - average (marginalSample part g s.2 e)|

lemma greedyStep_recurrence (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (o : Fin a → E) (ho : ∀ j, part (o j) = j)
    (hmono : Monotone g) (hsub : Diminishing g) {M tau : ℝ} (hM : 0 ≤ M)
    (hg : BoundedMarginals g M) (ha : 0 < a) (hscale : (a:ℝ)^2 ≤ tau*T)
    (s : GreedyState E a T) (hs : GreedyInvariant part s) (ht : s.1 < T)
    (seed : OracleSeed E a T L) (hgood : ¬estimationBad part g M tau s seed) :
    tableValue g s.2 + (g (Finset.univ.image o) - tableValue g s.2 - 3*tau*M)/T ≤
      tableValue g (greedyStep part hp g s seed).2 := by
  have hgood' : ∀ e, |scores part g s.2 seed e - average (marginalSample part g s.2 e)|
      ≤ tau*M/a := by
    intro e
    exact not_lt.mp (fun he => hgood ⟨e,he⟩)
  have hc := sampled_select_choice part hp g s.2 o ho seed hgood'
  simpa only [greedyStep, dite_eq_left ht] using
    advance_recurrence g s.2 ⟨s.1,ht⟩ (select part hp (scores part g s.2 seed)) o
      (fun j => hs.2 j ⟨s.1,ht⟩ (le_refl _)) hmono hsub hM hg ha hscale hc

lemma greedy_failure_bound (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) {M tau : ℝ} (hM : 0 < M) (htau : 0 < tau)
    (hg : BoundedMarginals g M) (ha : 0 < a) (hL : 0 < L)
    (hcount : (T:ℝ) * Fintype.card E * a^2 / (4*tau^3) ≤ L)
    (s : GreedyState E a T) :
    probability (adaptiveBad (greedyStep (L := L) part hp g)
      (estimationBad part g M tau) T s) ≤ tau := by
  let X : GreedyState E a T → E → (Fin a → Fin T) → ℝ :=
    fun u e => marginalSample part g u.2 e
  have hX : ∀ u : GreedyState E a T, True → ∀ e seed,
      0 ≤ X u e seed ∧ X u e seed ≤ M := by
    intro u _ e seed
    exact hg e (draw a (Function.update u.2 (part e) (fun _ => none)) seed ∅)
  have hb := adaptive_categorical_error X L T a hL
    (Nat.pos_of_ne_zero (NeZero.ne T)) ha hM htau (greedyStep part hp g)
    (fun _ => True) (fun _ _ _ => trivial) hX hcount s trivial
  exact hb

end StepBound
end MetricKMedianRecovery.Categorical

end OAI
