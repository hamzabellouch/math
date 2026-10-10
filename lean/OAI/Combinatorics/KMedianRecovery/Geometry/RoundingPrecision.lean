import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.EnumeratedBest
import OAI.Combinatorics.KMedianRecovery.Recovery.RawCount

namespace OAI

namespace MetricKMedianRecovery.Guided
variable {S A : Type*} [Fintype A]

omit [Fintype A] in
lemma pathWeight_constant (f : S → A → S) (c : ℝ) (n : ℕ) (s : S) (seed : Fin n → A) :
    pathWeight f (fun _ _ => c) n s seed = c^n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [pathWeight,ih,pow_succ,mul_comm]

lemma eventMass_domination (f : S → A → S) (p q : Kernel S A) (c : ℝ) (hc : 0 ≤ c)
    (hstep : ∀ s a, c * q.weight s a ≤ p.weight s a) (n : ℕ) (s : S)
    (E : (Fin n → A) → Prop) :
    c^n * eventMass f q.weight n s E ≤ eventMass f p.weight n s E := by
  classical
  unfold eventMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro seed _
  by_cases he : E seed
  · rw [ite_eq_left he,ite_eq_left he]
    have hh := pathWeight_domination f p q (fun _ _ => c) (fun _ _ => hc) hstep n s seed
    simpa only [pathWeight_constant] using hh
  · simp only [ite_eq_right he,mul_zero,le_refl]

lemma hitMass_domination (f : S → A → S) (p q : Kernel S A) (c : ℝ) (hc : 0 ≤ c)
    (hstep : ∀ s a, c * q.weight s a ≤ p.weight s a) (stop : S → Prop) (n : ℕ) (s : S) :
    c^n * hitMass f q stop n s ≤ hitMass f p stop n s :=
  eventMass_domination f p q c hc hstep n s (Hits f stop n s)

variable [DecidableEq A]

noncomputable def roundingPrecision (p : Kernel S A) (s : S) : ℕ :=
  Classical.choose (Dyadic.exists_precision (p.weight s))

omit [DecidableEq A] in
lemma roundingPrecision_spec (p : Kernel S A) (s : S) :
    ∀ a, 0 < p.weight s a → 2 ≤ (2:ℝ)^(roundingPrecision p s) * p.weight s a :=
  Classical.choose_spec (Dyadic.exists_precision (p.weight s))

noncomputable def rounded (p : Kernel S A) (default : A) : Kernel S A where
  weight s := Dyadic.weight (p.weight s) (roundingPrecision p s) default
  nonneg _s _a := Dyadic.weight_nonneg _ _ _ _
  total s := Dyadic.weight_total _ (p.nonneg s) (p.total s) _ _

lemma rounded_domination (p : Kernel S A) (default : A) (s : S) (a : A) :
    (1/2:ℝ) * p.weight s a ≤ (rounded p default).weight s a := by
  have hh := Dyadic.weight_lower (p.weight s) (p.nonneg s) (roundingPrecision p s) default a
    (roundingPrecision_spec p s)
  simpa only [rounded,div_eq_mul_inv,one_mul,mul_comm] using hh

lemma rounded_draw (p : Kernel S A) (default : A) (s : S) (a : A) :
    (∑ bits : Fin (roundingPrecision p s) → Bool,
      if Dyadic.draw (p.weight s) (p.nonneg s) (p.total s) (roundingPrecision p s) default bits = a
      then (1:ℝ) else 0) / 2^(roundingPrecision p s) = (rounded p default).weight s a :=
  Dyadic.draw_probability _ _ _ _ _ _

lemma rounded_hitMass (f : S → A → S) (p : Kernel S A) (default : A)
    (stop : S → Prop) (n : ℕ) (s : S) :
    (1/2:ℝ)^n * hitMass f p stop n s ≤ hitMass f (rounded p default) stop n s :=
  hitMass_domination f (rounded p default) p (1/2) (by norm_num)
    (rounded_domination p default) stop n s

end MetricKMedianRecovery.Guided

end OAI
