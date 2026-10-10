import Mathlib

namespace OAI

noncomputable section

open Filter Set

namespace Problem340

theorem clock_readings_separated {t : ℕ → ℝ} (ht : Monotone t)
    {i j : ℕ} (hij : i < j) (hstep : t (i + 1) = t i + 1) :
    t i + 1 ≤ t j := by
  rw [← hstep]
  exact ht (Nat.succ_le_of_lt hij)

theorem clock_readout_unique {t : ℕ → ℝ} {β : ℝ → ℝ} {a b : ℝ}
    (ht : Monotone t) (hwidth : b - a < 1)
    (hsupport : ∀ x, β x ≠ 0 → a < x ∧ x < b)
    (hstep : ∀ n, β (t n) ≠ 0 → t (n + 1) = t n + 1)
    {i j : ℕ} (hi : β (t i) ≠ 0) (hj : β (t j) ≠ 0) : i = j := by
  obtain hij | hij | hij := lt_trichotomy i j
  · have hsep := clock_readings_separated ht hij (hstep i hi)
    have hi' := hsupport (t i) hi
    have hj' := hsupport (t j) hj
    linarith
  · exact hij
  · have hsep := clock_readings_separated ht hij (hstep j hj)
    have hi' := hsupport (t i) hi
    have hj' := hsupport (t j) hj
    linarith

theorem clock_readout_support_subsingleton {t : ℕ → ℝ} {β : ℝ → ℝ} {a b : ℝ}
    (ht : Monotone t) (hwidth : b - a < 1)
    (hsupport : ∀ x, β x ≠ 0 → a < x ∧ x < b)
    (hstep : ∀ n, β (t n) ≠ 0 → t (n + 1) = t n + 1) :
    Set.Subsingleton {n : ℕ | β (t n) ≠ 0} := by
  intro i hi j hj
  exact clock_readout_unique ht hwidth hsupport hstep hi hj

theorem tsum_clock_readout_eq_single {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {t : ℕ → ℝ} {β : ℝ → ℝ} {a b : ℝ}
    (ht : Monotone t) (hwidth : b - a < 1)
    (hsupport : ∀ x, β x ≠ 0 → a < x ∧ x < b)
    (hstep : ∀ n, β (t n) ≠ 0 → t (n + 1) = t n + 1)
    (v : ℕ → E) {j : ℕ} (hj : β (t j) ≠ 0) :
    (∑' n, β (t n) • v n) = β (t j) • v j := by
  apply tsum_eq_single j
  intro n hnj
  have hn : β (t n) = 0 := by
    by_contra hn
    exact hnj (clock_readout_unique ht hwidth hsupport hstep hn hj)
  simp [hn]

theorem tsum_clock_readout_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {t : ℕ → ℝ} {β : ℝ → ℝ}
    (v : ℕ → E) (hzero : ∀ n, β (t n) = 0) :
    (∑' n, β (t n) • v n) = 0 := by
  simp [hzero]

theorem clock_unit_speed_add {t : ℕ → ℝ} {a b : ℝ}
    (ht : Monotone t)
    (hstep : ∀ n, a ≤ t n → t n ≤ b → t (n + 1) = t n + 1)
    (i d : ℕ) (ha : a ≤ t i) (hb : t (i + d) ≤ b) :
    t (i + d) = t i + (d : ℝ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hd : t (i + d) ≤ b := (ht (by omega)).trans hb
    have hlo : a ≤ t (i + d) := ha.trans (ht (by omega))
    have heq := hstep (i + d) hlo hd
    have hprev := ih hd
    simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.cast_add, Nat.cast_one,
      hprev, add_assoc] using heq

theorem clock_preparation_card_le_five {t : ℕ → ℝ}
    (ht : Monotone t)
    (hstep : ∀ n, 8 ≤ t n → t n ≤ 12 → t (n + 1) = t n + 1)
    (I : Finset ℕ) (hI : ∀ i ∈ I, 8 < t i ∧ t i < 12) : I.card ≤ 5 := by
  classical
  by_cases hne : I.Nonempty
  · let i := I.min' hne
    have hi : i ∈ I := Finset.min'_mem I hne
    have hsub : I ⊆ Finset.Icc i (i + 4) := by
      intro j hj
      have hij : i ≤ j := Finset.min'_le I j hj
      have hadd : i + (j - i) = j := Nat.add_sub_of_le hij
      have htime := clock_unit_speed_add ht hstep i (j - i)
        (hI i hi).1.le (by simpa [hadd] using (hI j hj).2.le)
      rw [hadd] at htime
      have hgap : (j - i : ℝ) < 4 := by
        have hi' := (hI i hi).1
        have hj' := (hI j hj).2
        have hcast : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) :=
          Nat.cast_sub hij
        rw [hcast] at htime
        linarith
      have hgap' : j - i < 4 := by
        have : ((j - i : ℕ) : ℝ) < (4 : ℕ) := by
          simpa [Nat.cast_sub hij] using hgap
        exact_mod_cast this
      exact Finset.mem_Icc.mpr ⟨hij, by omega⟩
    have hc := Finset.card_le_card hsub
    simp only [Nat.card_Icc] at hc
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

theorem clock_prediction_agreement {X : Type*} {x y : ℕ → X}
    {clock : X → ℝ} {a b : ℝ} {N : ℕ}
    (hzero : x 0 = y 0)
    (hbefore : ∀ n < N, x n = y n → clock (x n) < a → x (n + 1) = y (n + 1))
    (hxstep : ∀ n < N, a ≤ clock (x n) → clock (x n) ≤ b →
      clock (x (n + 1)) = clock (x n) + 1)
    (hystep : ∀ n < N, a ≤ clock (y n) → clock (y n) ≤ b →
      clock (y (n + 1)) = clock (y n) + 1)
    (hbound : ∀ n < N, clock (x n) ≤ b) :
    ∀ n ≤ N, clock (x n) = clock (y n) := by
  have hfast (n : ℕ) (hn : n < N) (heq : clock (x n) = clock (y n))
      (ha : a ≤ clock (x n)) :
      clock (x (n + 1)) = clock (y (n + 1)) ∧ a ≤ clock (x (n + 1)) := by
    have hx := hxstep n hn ha (hbound n hn)
    have hy := hystep n hn (heq ▸ ha) (heq ▸ hbound n hn)
    constructor
    · rw [hx, hy, heq]
    · linarith
  have hinv : ∀ n ≤ N,
      x n = y n ∨ (clock (x n) = clock (y n) ∧ a ≤ clock (x n)) := by
    intro n
    induction n with
    | zero => intro _; exact Or.inl hzero
    | succ n ih =>
      intro hn
      have hn' : n < N := by omega
      rcases ih (by omega) with heq | ⟨heq, ha⟩
      · by_cases ha : clock (x n) < a
        · exact Or.inl (hbefore n hn' heq ha)
        · exact Or.inr (hfast n hn' (congrArg clock heq) (le_of_not_gt ha))
      · exact Or.inr (hfast n hn' heq ha)
  intro n hn
  rcases hinv n hn with heq | ⟨heq, _⟩
  · exact congrArg clock heq
  · exact heq

theorem clock_readout_values_agree {s t : ℕ → ℝ} {β : ℝ → ℝ} {b : ℝ}
    (hs : Monotone s) (ht : Monotone t)
    (hsupport : ∀ r, b ≤ r → β r = 0)
    (N : ℕ) (hN : b ≤ s N) (hagree : ∀ n ≤ N, s n = t n) :
    ∀ n, β (s n) = β (t n) := by
  intro n
  by_cases hn : n ≤ N
  · rw [hagree n hn]
  · have hNn : N ≤ n := by omega
    have hsN : b ≤ s n := hN.trans (hs hNn)
    have htN : b ≤ t n := (hagree N le_rfl ▸ hN).trans (ht hNn)
    rw [hsupport _ hsN, hsupport _ htN]

theorem clock_prediction_single_hit {s t : ℕ → ℝ} {β : ℝ → ℝ} {a b : ℝ}
    (hs : Monotone s) (hwidth : b - a < 1)
    (hsupport : ∀ r, β r ≠ 0 → a < r ∧ r < b)
    (hstep : ∀ n, β (s n) ≠ 0 → s (n + 1) = s n + 1)
    (hagree : ∀ n, β (s n) = β (t n))
    {j : ℕ} (hj : β (s j) ≠ 0) (n : ℕ) :
    β (t n) = if n = j then β (s j) else 0 := by
  rw [← hagree n]
  split_ifs with hnj
  · subst n; rfl
  · by_contra hn
    exact hnj (clock_readout_unique hs hwidth hsupport hstep hn hj)

end Problem340

end

end OAI
