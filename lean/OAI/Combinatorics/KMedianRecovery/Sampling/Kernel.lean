import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.LengthPolynomial

namespace OAI

namespace MetricKMedianRecovery.Guided

variable {S A : Type*} [Fintype A]

structure Kernel (S A : Type*) [Fintype A] where
  weight : S → A → ℝ
  nonneg : ∀ s a, 0 ≤ weight s a
  total : ∀ s, ∑ a, weight s a = 1

noncomputable def pathWeight (f : S → A → S) (p : S → A → ℝ) :
    (n : ℕ) → S → (Fin n → A) → ℝ
  | 0, _, _ => 1
  | n+1, s, seed => p s (seed 0) * pathWeight f p n (f s (seed 0)) (Fin.tail seed)

omit [Fintype A] in
lemma pathWeight_nonneg (f : S → A → S) (p : S → A → ℝ)
    (hp : ∀ s a, 0 ≤ p s a) (n : ℕ) (s : S) (seed : Fin n → A) :
    0 ≤ pathWeight f p n s seed := by
  induction n generalizing s with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hp s _) (ih _ _)

lemma sum_fin_succ (n : ℕ) (X : (Fin (n+1) → A) → ℝ) :
    (∑ seed, X seed) = ∑ a : A, ∑ seed : Fin n → A, X (Fin.cons a seed) := by
  calc
    _ = ∑ y : A × (Fin n → A), X (Fin.cons y.1 y.2) := by
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => A)).symm
      intro x
      exact congrArg X (Fin.cons_self_tail x).symm
    _ = _ := Fintype.sum_prod_type _

lemma pathWeight_total (f : S → A → S) (p : Kernel S A) (n : ℕ) (s : S) :
    ∑ seed : Fin n → A, pathWeight f p.weight n s seed = 1 := by
  induction n generalizing s with
  | zero => simp [pathWeight]
  | succ n ih =>
    rw [sum_fin_succ]
    simp only [pathWeight, Fin.cons_zero, Fin.tail_cons, ← Finset.mul_sum, ih, mul_one]
    exact p.total s

def Hits (f : S → A → S) (stop : S → Prop) :
    (n : ℕ) → S → (Fin n → A) → Prop
  | 0, s, _ => stop s
  | n+1, s, seed => stop s ∨ Hits f stop n (f s (seed 0)) (Fin.tail seed)

noncomputable def eventMass (f : S → A → S) (p : S → A → ℝ)
    (n : ℕ) (s : S) (E : (Fin n → A) → Prop) : ℝ := by
  classical
  exact ∑ seed, if E seed then pathWeight f p n s seed else 0

lemma eventMass_nonneg (f : S → A → S) (p : Kernel S A)
    (n : ℕ) (s : S) (E : (Fin n → A) → Prop) : 0 ≤ eventMass f p.weight n s E := by
  classical
  exact Finset.sum_nonneg (fun seed _ => by
    split_ifs
    · exact pathWeight_nonneg f p.weight p.nonneg n s seed
    · exact le_rfl)

lemma pathWeight_domination (f : S → A → S) (p q : Kernel S A)
    (loss : S → A → ℝ) (hloss : ∀ s a, 0 ≤ loss s a)
    (hstep : ∀ s a, loss s a * q.weight s a ≤ p.weight s a)
    (n : ℕ) (s : S) (seed : Fin n → A) :
    pathWeight f loss n s seed * pathWeight f q.weight n s seed ≤
      pathWeight f p.weight n s seed := by
  induction n generalizing s with
  | zero => simp [pathWeight]
  | succ n ih =>
    have hh := mul_le_mul (hstep s (seed 0)) (ih (f s (seed 0)) (Fin.tail seed))
      (mul_nonneg (pathWeight_nonneg f loss hloss _ _ _)
        (pathWeight_nonneg f q.weight q.nonneg _ _ _))
      (p.nonneg s (seed 0))
    simpa only [pathWeight, mul_mul_mul_comm] using hh

lemma supported_path_hits (f : S → A → S) (q : Kernel S A) (stop Inv : S → Prop)
    (counter : S → ℕ)
    (hInv : ∀ s, Inv s → ∀ a, 0 < q.weight s a → Inv (f s a))
    (hzero : ∀ s, Inv s → counter s = 0 → stop s)
    (hdesc : ∀ s, Inv s → ¬stop s → ∀ a, 0 < q.weight s a → counter (f s a) < counter s)
    (n : ℕ) (s : S) (hs : Inv s) (hc : counter s ≤ n) (seed : Fin n → A)
    (hseed : 0 < pathWeight f q.weight n s seed) : Hits f stop n s seed := by
  induction n generalizing s with
  | zero => exact hzero s hs (Nat.eq_zero_of_le_zero hc)
  | succ n ih =>
    by_cases ht : stop s
    · exact Or.inl ht
    · change 0 < q.weight s (seed 0) *
        pathWeight f q.weight n (f s (seed 0)) (Fin.tail seed) at hseed
      have hn := pathWeight_nonneg f q.weight q.nonneg n (f s (seed 0)) (Fin.tail seed)
      have hp : 0 < q.weight s (seed 0) := by nlinarith
      have htail : 0 < pathWeight f q.weight n (f s (seed 0)) (Fin.tail seed) := by
        nlinarith [q.nonneg s (seed 0)]
      exact Or.inr (ih _ (hInv s hs _ hp) (by have := hdesc s hs ht _ hp; omega) _ htail)

theorem history_likelihood_bound (f : S → A → S) (p q : Kernel S A)
    (loss : S → A → ℝ) (hloss : ∀ s a, 0 ≤ loss s a)
    (hstep : ∀ s a, loss s a * q.weight s a ≤ p.weight s a)
    (n : ℕ) (s : S) (E : (Fin n → A) → Prop) (B : ℝ) (_hB : 0 ≤ B)
    (hbudget : ∀ seed, 0 < pathWeight f q.weight n s seed → B ≤ pathWeight f loss n s seed)
    (hevent : ∀ seed, 0 < pathWeight f q.weight n s seed → E seed) :
    B ≤ eventMass f p.weight n s E := by
  classical
  have hpoint : ∀ seed : Fin n → A,
      B * pathWeight f q.weight n s seed ≤
        if E seed then pathWeight f p.weight n s seed else 0 := by
    intro seed
    have hq := pathWeight_nonneg f q.weight q.nonneg n s seed
    by_cases hp : 0 < pathWeight f q.weight n s seed
    · rw [ite_eq_left (hevent seed hp)]
      exact (mul_le_mul_of_nonneg_right (hbudget seed hp) hq).trans
        (pathWeight_domination f p q loss hloss hstep n s seed)
    · have hz : pathWeight f q.weight n s seed = 0 := le_antisymm (le_of_not_gt hp) hq
      rw [hz, mul_zero]
      split_ifs
      · exact pathWeight_nonneg f p.weight p.nonneg n s seed
      · exact le_rfl
  have hsum := Finset.sum_le_sum (fun seed (_ : seed ∈ Finset.univ) => hpoint seed)
  rw [← Finset.mul_sum, pathWeight_total, mul_one] at hsum
  exact hsum

noncomputable def eligibleMass (p : Kernel S A) (eligible : S → A → Prop) (s : S) : ℝ := by
  classical
  exact ∑ a : A, if eligible s a then p.weight s a else 0

noncomputable def conditioned (p : Kernel S A) (eligible : S → A → Prop)
    (hpos : ∀ s, 0 < eligibleMass p eligible s) : Kernel S A := by
  classical
  let mass := eligibleMass p eligible
  refine ⟨fun s a => if eligible s a then p.weight s a / mass s else 0, ?_, ?_⟩
  · intro s a
    split_ifs
    · exact div_nonneg (p.nonneg s a) (hpos s).le
    · exact le_rfl
  · intro s
    have he : (∑ a : A, if eligible s a then p.weight s a/mass s else 0) =
        (∑ a : A, if eligible s a then p.weight s a else 0) / mass s := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    rw [he]
    exact div_self (ne_of_gt (hpos s))

lemma conditioned_ratio (p : Kernel S A) (eligible : S → A → Prop)
    (hpos : ∀ s, 0 < eligibleMass p eligible s)
    (s : S) (a : A) :
    eligibleMass p eligible s *
      (conditioned p eligible hpos).weight s a ≤ p.weight s a := by
  classical
  change _ * (if eligible s a then p.weight s a / _ else 0) ≤ _
  split_ifs
  · exact le_of_eq (mul_div_cancel₀ _ (ne_of_gt (hpos s)))
  · simpa only [mul_zero] using p.nonneg s a

end MetricKMedianRecovery.Guided

end OAI
