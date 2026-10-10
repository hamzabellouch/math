import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.SparseBadDivisorTail

/-- Dyadic decomposition starting at an arbitrary dyadic threshold. -/
lemma sum_dyadic_from {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (J K : ℕ) :
    (∑ n ∈ Finset.Ico (2 ^ J) (2 ^ (J + K)), f n) =
      ∑ k ∈ Finset.range K,
        ∑ n ∈ Finset.Ico (2 ^ (J + k)) (2 ^ (J + k + 1)), f n := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact (Finset.sum_Ico_consecutive f
      (Nat.pow_le_pow_right (by decide) (by omega : J ≤ J + K))
      (Nat.pow_le_pow_right (by decide) (by omega : J + K ≤ J + K + 1))).symm

/-- A dyadic shell has reciprocal mass at most its cardinality over its base. -/
lemma reciprocal_shell_le (A : Finset ℕ) (j : ℕ) :
    (∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ A, (1 : ℝ) / n) ≤
      ((Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ A).card : ℝ) / (2 : ℝ) ^ j := by
  calc
    _ ≤ ∑ _n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ A,
        (1 : ℝ) / (2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro n hn
      have hbase : (2 : ℝ) ^ j ≤ (n : ℝ) := by
        exact_mod_cast (Finset.mem_Ico.mp (Finset.mem_inter.mp hn).1).1
      exact one_div_le_one_div_of_le (by positivity) hbase
    _ = _ := by simp [div_eq_mul_inv]

/-- Finite reciprocal-tail estimate from dyadic cardinality bounds. The
geometric ratio `r` is the shell-growth ratio divided by two. Only shells
at or above `J` need satisfy the estimate. -/
theorem reciprocal_tail_le (A : Finset ℕ) (J : ℕ) {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hA : ∀ n ∈ A, 2 ^ J ≤ n)
    (hcount : ∀ j : ℕ, J ≤ j →
      ((Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ A).card : ℝ) ≤ C * (2 * r) ^ j) :
    (∑ n ∈ A, (1 : ℝ) / n) ≤ C * r ^ J / (1 - r) := by
  let K := Nat.log 2 (A.sup id) + 1
  let f : ℕ → ℝ := fun n => if n ∈ A then 1 / (n : ℝ) else 0
  have htop : A.sup id < 2 ^ (J + K) := by
    have ht : A.sup id < 2 ^ K := Nat.lt_pow_succ_log_self (by decide) _
    exact ht.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hsub : A ⊆ Finset.Ico (2 ^ J) (2 ^ (J + K)) := by
    intro n hn
    exact Finset.mem_Ico.mpr ⟨hA n hn, (Finset.le_sup (f := id) hn).trans_lt htop⟩
  have hsum : (∑ n ∈ A, (1 : ℝ) / n) =
      ∑ n ∈ Finset.Ico (2 ^ J) (2 ^ (J + K)), f n := by
    calc
      _ = ∑ n ∈ A, f n := Finset.sum_congr rfl (by intro n hn; simp [f, hn])
      _ = _ := Finset.sum_subset hsub (by intro n _ hn; simp [f, hn])
  have hblock (j : ℕ) (hj : J ≤ j) :
      (∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), f n) ≤ C * r ^ j := by
    have heq : (∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), f n) =
        ∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ A, (1 : ℝ) / n := by
      simp only [f, ← Finset.sum_filter]
      congr 1
    rw [heq]
    calc
      _ ≤ ((Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ A).card : ℝ) / (2 : ℝ) ^ j :=
        reciprocal_shell_le A j
      _ ≤ (C * (2 * r) ^ j) / (2 : ℝ) ^ j :=
        div_le_div_of_nonneg_right (hcount j hj) (by positivity)
      _ = C * r ^ j := by rw [mul_pow]; field_simp
  rw [hsum, sum_dyadic_from]
  calc
    _ ≤ ∑ k ∈ Finset.range K, C * r ^ (J + k) :=
      Finset.sum_le_sum (fun k _ => hblock (J + k) (by omega))
    _ = C * r ^ J * ∑ k ∈ Finset.range K, r ^ k := by
      simp_rw [pow_add]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      ring
    _ ≤ C * r ^ J * ∑' k : ℕ, r ^ k :=
      mul_le_mul_of_nonneg_left
        ((summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (by intros; positivity))
        (by positivity)
    _ = C * r ^ J / (1 - r) := by
      rw [tsum_geometric_of_lt_one hr0 hr1]
      rfl


/-- Positive integers up to `Y` divisible by at least one member of `A`. -/
def divisorMultiples (A : Finset ℕ) (Y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Y).filter (fun n => ∃ d ∈ A, d ∣ n)

lemma card_positive_multiples (Y d : ℕ) :
    ((Finset.Icc 1 Y).filter (fun n => d ∣ n)).card = Y / d := by
  have heq : (Finset.Icc 1 Y).filter (fun n => d ∣ n) =
      (Finset.range (Y + 1)).filter (fun n => n ≠ 0 ∧ d ∣ n) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    omega
  rw [heq, Nat.card_multiples']

/-- The union bound for exceptional divisors has no additive endpoint error. -/
theorem divisorMultiples_card_le (A : Finset ℕ) (Y : ℕ) :
    ((divisorMultiples A Y).card : ℝ) ≤
      (Y : ℝ) * ∑ d ∈ A, (1 : ℝ) / d := by
  have heq : divisorMultiples A Y =
      A.biUnion (fun d => (Finset.Icc 1 Y).filter (fun n => d ∣ n)) := by
    ext n
    simp only [divisorMultiples, Finset.mem_filter, Finset.mem_biUnion]
    aesop
  rw [heq]
  calc
    _ ≤ ∑ d ∈ A, (((Finset.Icc 1 Y).filter (fun n => d ∣ n)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ = ∑ d ∈ A, ((Y / d : ℕ) : ℝ) := by simp_rw [card_positive_multiples]
    _ ≤ ∑ d ∈ A, (Y : ℝ) / d :=
      Finset.sum_le_sum (fun d _ => Nat.cast_div_le)
    _ = (Y : ℝ) * ∑ d ∈ A, (1 : ℝ) / d := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      simp [div_eq_mul_inv]

/-- A finite piece of a global exceptional-modulus predicate above `2^J`. -/
def badTail (B : ℕ → Prop) [DecidablePred B] (J Y : ℕ) : Finset ℕ :=
  (Finset.Icc (2 ^ J) Y).filter B

/-- Global dyadic counts control every finite truncation of the reciprocal tail. -/
theorem badTail_reciprocal_le (B : ℕ → Prop) [DecidablePred B]
    (J Y : ℕ) {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hcount : ∀ j : ℕ, J ≤ j →
      (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter B).card : ℝ) ≤ C * (2 * r) ^ j) :
    (∑ d ∈ badTail B J Y, (1 : ℝ) / d) ≤ C * r ^ J / (1 - r) := by
  apply reciprocal_tail_le (badTail B J Y) J hC hr0 hr1
  · intro n hn
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  · intro j hj
    have hsub : Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ badTail B J Y ⊆
        (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter B := by
      intro n hn
      obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hn
      exact Finset.mem_filter.mpr ⟨h1, (Finset.mem_filter.mp h2).2⟩
    have hcard : ((Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ badTail B J Y).card : ℝ) ≤
        (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter B).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hcard.trans (hcount j hj)

/-- Uniform exceptional-multiple density, with the explicit geometric tail. -/
theorem badTail_multiples_card_le (B : ℕ → Prop) [DecidablePred B]
    (J Y : ℕ) {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hcount : ∀ j : ℕ, J ≤ j →
      (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter B).card : ℝ) ≤ C * (2 * r) ^ j) :
    ((divisorMultiples (badTail B J Y) Y).card : ℝ) ≤
      (Y : ℝ) * (C * r ^ J / (1 - r)) := by
  exact (divisorMultiples_card_le _ _).trans
    (mul_le_mul_of_nonneg_left (badTail_reciprocal_le B J Y hC hr0 hr1 hcount)
      (Nat.cast_nonneg Y))

/-- Dyadic sublinear exceptional counts give a density tending uniformly to
zero as the excluded divisor threshold grows. The onset of the shell estimate
may be arbitrary but fixed. -/
theorem eventually_badTail_multiples_small (B : ℕ → Prop) [DecidablePred B]
    (J₀ : ℕ) {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hcount : ∀ j : ℕ, J₀ ≤ j →
      (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter B).card : ℝ) ≤ C * (2 * r) ^ j) :
    ∀ ε : ℝ, 0 < ε → ∃ J₁ : ℕ, J₀ ≤ J₁ ∧ ∀ J : ℕ, J₁ ≤ J → ∀ Y : ℕ,
      ((divisorMultiples (badTail B J Y) Y).card : ℝ) ≤ ε * Y := by
  intro ε hε
  have hlim : Filter.Tendsto (fun J : ℕ => C * r ^ J / (1 - r))
      Filter.atTop (nhds 0) := by
    have hc : Filter.Tendsto (fun _ : ℕ => C) Filter.atTop (nhds C) := tendsto_const_nhds
    have h := (hc.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)).div_const (1 - r)
    simpa using h
  obtain ⟨J₂, hJ₂⟩ := Filter.eventually_atTop.mp (hlim.eventually_lt_const hε)
  refine ⟨max J₀ J₂, le_max_left _ _, ?_⟩
  intro J hJ Y
  have hJ0 : J₀ ≤ J := (le_max_left _ _).trans hJ
  have hJ2 : J₂ ≤ J := (le_max_right _ _).trans hJ
  have hbound := badTail_multiples_card_le B J Y hC hr0 hr1
    (fun j hj => hcount j (hJ0.trans hj))
  calc
    _ ≤ (Y : ℝ) * (C * r ^ J / (1 - r)) := hbound
    _ ≤ (Y : ℝ) * ε := mul_le_mul_of_nonneg_left (hJ₂ J hJ2).le (Nat.cast_nonneg Y)
    _ = ε * Y := mul_comm _ _


/-- The usual sublinear-power form of the uniform density statement. -/
theorem eventually_badTail_multiples_small_of_power (B : ℕ → Prop) [DecidablePred B]
    (J₀ : ℕ) {C β : ℝ} (hC : 0 ≤ C) (hβ : β < 1)
    (hcount : ∀ j : ℕ, J₀ ≤ j →
      (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter B).card : ℝ) ≤
        C * ((2 : ℝ) ^ j) ^ β) :
    ∀ ε : ℝ, 0 < ε → ∃ J₁ : ℕ, J₀ ≤ J₁ ∧ ∀ J : ℕ, J₁ ≤ J → ∀ Y : ℕ,
      ((divisorMultiples (badTail B J Y) Y).card : ℝ) ≤ ε * Y := by
  let r : ℝ := (2 : ℝ) ^ β / 2
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    dsimp [r]
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hβ
  apply eventually_badTail_multiples_small B J₀ hC hr0 hr1
  intro j hj
  have heq : (2 * r) ^ j = ((2 : ℝ) ^ j) ^ β := by
    have hr : 2 * r = (2 : ℝ) ^ β := by dsimp [r]; ring
    rw [hr]
    exact Real.rpow_pow_comm (by norm_num) β j
  rw [heq]
  exact hcount j hj


lemma divisorMultiples_mono {A A' : Finset ℕ} (Y : ℕ) (hA : A ⊆ A') :
    divisorMultiples A Y ⊆ divisorMultiples A' Y := by
  intro n hn
  obtain ⟨hn, d, hd, hdn⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨hn, d, hA hd, hdn⟩

/-- The finite divisor cutoff is semantically redundant for positive multiples. -/
lemma mem_divisorMultiples_badAbove (B : ℕ → Prop) [DecidablePred B]
    (R Y n : ℕ) :
    n ∈ divisorMultiples ((Finset.Icc R Y).filter B) Y ↔
      1 ≤ n ∧ n ≤ Y ∧ ∃ d : ℕ, R ≤ d ∧ B d ∧ d ∣ n := by
  simp only [divisorMultiples, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hn1, hnY⟩, d, ⟨⟨hRd, _⟩, hBd⟩, hdn⟩
    exact ⟨hn1, hnY, d, hRd, hBd, hdn⟩
  · rintro ⟨hn1, hnY, d, hRd, hBd, hdn⟩
    have hdY : d ≤ Y := (Nat.le_of_dvd (by omega : 0 < n) hdn).trans hnY
    exact ⟨⟨hn1, hnY⟩, d, ⟨⟨hRd, hdY⟩, hBd⟩, hdn⟩

/-- An arbitrary growing lower cutoff can be used, not just a dyadic one.
The conclusion is uniform in the ambient integer interval. -/
theorem eventually_large_bad_divisor_multiples_small (B : ℕ → Prop) [DecidablePred B]
    (J₀ : ℕ) {C β : ℝ} (hC : 0 ≤ C) (hβ : β < 1)
    (hcount : ∀ j : ℕ, J₀ ≤ j →
      (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter B).card : ℝ) ≤
        C * ((2 : ℝ) ^ j) ^ β) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, 1 ≤ R₀ ∧ ∀ R : ℕ, R₀ ≤ R → ∀ Y : ℕ,
      ((divisorMultiples ((Finset.Icc R Y).filter B) Y).card : ℝ) ≤ ε * Y := by
  intro ε hε
  obtain ⟨J, _, hJ⟩ := eventually_badTail_multiples_small_of_power
    B J₀ hC hβ hcount ε hε
  refine ⟨2 ^ J, Nat.succ_le_iff.mpr (by positivity), ?_⟩
  intro R hR Y
  have hsub : (Finset.Icc R Y).filter B ⊆ badTail B J Y := by
    intro d hd
    obtain ⟨hdI, hBd⟩ := Finset.mem_filter.mp hd
    obtain ⟨hRd, hdY⟩ := Finset.mem_Icc.mp hdI
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hR.trans hRd, hdY⟩, hBd⟩
  have hcard : ((divisorMultiples ((Finset.Icc R Y).filter B) Y).card : ℝ) ≤
      ((divisorMultiples (badTail B J Y) Y).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (divisorMultiples_mono Y hsub)
  exact hcard.trans (hJ J le_rfl Y)

end Problem337.SparseBadDivisorTail

end

end OAI
