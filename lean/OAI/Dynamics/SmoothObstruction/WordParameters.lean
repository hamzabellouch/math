import Mathlib

namespace OAI

section

open Filter Topology

namespace SmoothObstruction.WordParameters

/-- The source logarithm is binary. Levels here are numbered i+1. -/
noncomputable def ell (s : ℕ) : ℝ := Real.logb 2 ((2 : ℝ) ^ (2 * s) - 1)
noncomputable def K (s : ℕ) : ℕ := ⌊Real.sqrt (ell s)⌋₊
noncomputable def epsilon (i : ℕ) : ℝ := 1 / (2 : ℝ) ^ (i + 3)
noncomputable def X (i s : ℕ) : ℝ := epsilon i / 100 * 2 ^ K s * ell s
noncomputable def nextS (i s : ℕ) : ℕ := ⌊X i s / 2⌋₊
noncomputable def sequence (s₀ : ℕ) : ℕ → ℕ
  | 0 => s₀
  | i + 1 => nextS i (sequence s₀ i)

lemma epsilon_pos (i : ℕ) : 0 < epsilon i := by unfold epsilon; positivity
lemma epsilon_succ (i : ℕ) : epsilon (i + 1) = epsilon i / 2 := by
  unfold epsilon
  rw [show i + 1 + 3 = i + 3 + 1 by omega, pow_succ]
  ring

lemma ell_zero : ell 0 = 0 := by simp [ell]
lemma ell_bounds {s : ℕ} (hs : 1 ≤ s) : (2 * s : ℝ) - 1 < ell s ∧ ell s < 2 * s := by
  have hd : 2 ≤ 2 * s := by omega
  have hpow : 2 ≤ (2 : ℝ) ^ (2 * s - 1) := by
    calc
      _ = (2 : ℝ) ^ 1 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have hrew : (2 : ℝ) ^ (2 * s) = 2 ^ (2 * s - 1) * 2 := by
    conv_lhs => rw [show 2 * s = (2 * s - 1) + 1 by omega]
    rw [pow_succ]
  have hpos : 0 < (2 : ℝ) ^ (2 * s) - 1 := by rw [hrew]; linarith
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 < (2 : ℝ) ^ (2 * s - 1))
    (show (2 : ℝ) ^ (2 * s - 1) < 2 ^ (2 * s) - 1 by rw [hrew]; linarith)
  have hu := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) hpos
    (show (2 : ℝ) ^ (2 * s) - 1 < 2 ^ (2 * s) by linarith)
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl hu
  have hsreal : ((2 * s - 1 : ℕ) : ℝ) = 2 * s - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; rfl
  exact ⟨by simpa [ell, hsreal] using hl, by simpa [ell] using hu⟩

lemma ell_nonneg (s : ℕ) : 0 ≤ ell s := by
  rcases s with _ | s
  · rw [ell_zero]
  · have h := (ell_bounds (by omega : 1 ≤ s + 1)).1
    have hs : (0 : ℝ) ≤ s := by positivity
    push_cast at h
    linarith

lemma K_bounds (s : ℕ) : (K s : ℝ) ^ 2 ≤ ell s ∧ ell s < (K s + 1 : ℝ) ^ 2 := by
  have h0 := Real.sqrt_nonneg (ell s)
  have h1 := Nat.floor_le h0
  have h2 := Nat.lt_floor_add_one (Real.sqrt (ell s))
  have he := Real.sq_sqrt (ell_nonneg s)
  change (K s : ℝ) ≤ Real.sqrt (ell s) at h1
  change Real.sqrt (ell s) < (K s : ℝ) + 1 at h2
  constructor <;> nlinarith [sq_nonneg ((K s : ℝ) - Real.sqrt (ell s)),
    show 0 ≤ (K s : ℝ) from Nat.cast_nonneg _]

/-- A single integer estimate proves all the logarithmic polynomial budgets
at the fixed initial threshold. No floating-point certificate is used. -/
lemma polynomial_budget : ∀ k : ℕ, 256 ≤ k → ((k : ℝ) + 14) ^ 16 ≤ (2 : ℝ) ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hnreal : (256 : ℝ) ≤ n := by exact_mod_cast hn
    have hstep : (n : ℝ) + 1 + 14 ≤ (257 / 256 : ℝ) * (n + 14) := by linarith
    have hp := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ n + 1 + 14) hstep 16
    have hc : (257 / 256 : ℝ) ^ 16 ≤ 2 := by norm_num
    calc
      (((n + 1 : ℕ) : ℝ) + 14) ^ 16 ≤ (257 / 256 : ℝ) ^ 16 * ((n : ℝ) + 14) ^ 16 := by
        simpa only [Nat.cast_add, Nat.cast_one, mul_pow] using hp
      _ ≤ 2 * ((n : ℝ) + 14) ^ 16 := mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ 2 * 2 ^ n := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

lemma polynomial_root_budget {k : ℕ} (hk : 256 ≤ k) :
    (14 + k : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) / 8) ∧
      ((k : ℝ) + 1) ^ 2 ≤ (2 : ℝ) ^ ((k : ℝ) / 8) ∧
      (k : ℝ) ^ 2 ≤ (2 : ℝ) ^ ((k : ℝ) / 3) := by
  have hbase := polynomial_budget k hk
  have hkn : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have h8 : (14 + k : ℝ) ^ 8 ≤ 2 ^ k := by
    calc
      _ ≤ ((k : ℝ) + 14) ^ 16 := by
        rw [add_comm 14]
        exact pow_le_pow_right₀ (by linarith) (by decide)
      _ ≤ _ := hbase
  have h16 : (((k : ℝ) + 1) ^ 2) ^ 8 ≤ 2 ^ k := by
    rw [← pow_mul]
    exact (pow_le_pow_left₀ (by positivity) (by linarith : (k : ℝ) + 1 ≤ k + 14) 16).trans hbase
  have h6 : ((k : ℝ) ^ 2) ^ 3 ≤ 2 ^ k := by
    rw [← pow_mul]
    exact ((pow_le_pow_left₀ (by positivity) (by linarith : (k : ℝ) ≤ k + 14) 6).trans
      (pow_le_pow_right₀ (by linarith) (by decide))).trans hbase
  have hr8 : ((2 : ℝ) ^ ((k : ℝ) / 8)) ^ 8 = (2 : ℝ) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  have hr3 : ((2 : ℝ) ^ ((k : ℝ) / 3)) ^ 3 = (2 : ℝ) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  refine ⟨?_, ?_, ?_⟩
  · exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 8 ≠ 0)).mp (hr8 ▸ h8)
  · exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 8 ≠ 0)).mp (hr8 ▸ h16)
  · exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 3 ≠ 0)).mp (hr3 ▸ h6)


lemma rounding {i s : ℕ} (hX : 6 ≤ X i s) :
    X i s - 3 < ell (nextS i s) ∧ ell (nextS i s) ≤ X i s ∧
      X i s / 2 ≤ ell (nextS i s) := by
  have hpos : 0 ≤ X i s / 2 := by linarith
  have hlo := Nat.lt_floor_add_one (X i s / 2)
  have hup := Nat.floor_le hpos
  change X i s / 2 < (nextS i s : ℝ) + 1 at hlo
  change (nextS i s : ℝ) ≤ X i s / 2 at hup
  have hs : 1 ≤ nextS i s := by
    by_contra h
    have hz : nextS i s = 0 := by omega
    simp only [hz, Nat.cast_zero, zero_add] at hlo
    linarith
  obtain ⟨he1, he2⟩ := ell_bounds hs
  refine ⟨by linarith, by linarith, by linarith⟩

lemma exp_half_sub_one {k : ℕ} (hk : 6 ≤ k) :
    (2 : ℝ) ^ ((k : ℝ) / 3) ≤ 2 ^ ((k : ℝ) / 2) - 1 := by
  have hkr : (6 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : 1 ≤ (2 : ℝ) ^ ((k : ℝ) / 3) := Real.one_le_rpow (by norm_num) (by positivity)
  have hh : (2 : ℝ) ^ ((k : ℝ) / 3 + 1) ≤ 2 ^ ((k : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one] at hh
  linarith

lemma X_lower {i s : ℕ} (hε : 32 ≤ epsilon i * K s) :
    (8 / 25 : ℝ) * K s * 2 ^ K s ≤ X i s := by
  have hk : 0 ≤ (K s : ℝ) := Nat.cast_nonneg _
  have hep : 0 ≤ epsilon i := (epsilon_pos i).le
  have he1 := mul_le_mul_of_nonneg_left (K_bounds s).1 hep
  have he2 := mul_le_mul_of_nonneg_right hε hk
  have ht : 32 * K s ≤ epsilon i * ell s := by nlinarith
  have ht' := mul_le_mul_of_nonneg_right ht
    (show 0 ≤ (2 : ℝ) ^ K s / 100 by positivity)
  unfold X
  nlinarith

/-- Growth from exactly the source recursion, including the floor to the
largest even dimension. No later enlargement of the initial alphabet occurs. -/
theorem one_step_growth {i s : ℕ} (hk : 256 ≤ K s) (hε : 32 ≤ epsilon i * K s) :
    6 ≤ X i s ∧ (2 : ℝ) ^ K s ≤ ell (nextS i s) ∧
      (2 : ℝ) ^ ((K s : ℝ) / 3) ≤ K (nextS i s) ∧
      K s ^ 2 ≤ K (nextS i s) ∧ 4 * K s ≤ K (nextS i s) := by
  have hkr : (256 : ℝ) ≤ K s := by exact_mod_cast hk
  have hn : 1 ≤ (2 : ℝ) ^ K s := one_le_pow₀ (by norm_num)
  have hxlo := X_lower hε
  have hx : 6 ≤ X i s := by nlinarith
  have hround := rounding hx
  have hnext : (2 : ℝ) ^ K s ≤ ell (nextS i s) := by nlinarith
  have hsq : ((2 : ℝ) ^ ((K s : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ K s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  have hhalf : (2 : ℝ) ^ ((K s : ℝ) / 2) ≤ (K (nextS i s) : ℝ) + 1 := by
    have hbound := (K_bounds (nextS i s)).2
    nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ((K s : ℝ) / 2),
      show 0 ≤ (K (nextS i s) : ℝ) from Nat.cast_nonneg _]
  have hthird := exp_half_sub_one (by omega : 6 ≤ K s)
  have hg : (2 : ℝ) ^ ((K s : ℝ) / 3) ≤ K (nextS i s) := by linarith
  have hsqr : K s ^ 2 ≤ K (nextS i s) := by
    have h := (polynomial_root_budget hk).2.2.trans hg
    exact_mod_cast h
  have hfour : 4 * K s ≤ K (nextS i s) := by
    have hkn : 4 ≤ K s := by omega
    have := Nat.mul_le_mul_right (K s) hkn
    rw [← sq] at this
    exact this.trans hsqr
  exact ⟨hx, hnext, hg, hsqr, hfour⟩

/-- All levels obey the fixed initial threshold and the exact epsilon growth
bound in source (word-growth). Level zero means manuscript level one. -/
theorem sequence_growth {s₀ : ℕ} (h₀ : 256 ≤ K s₀) :
    ∀ i, 256 ≤ K (sequence s₀ i) ∧
      32 * (2 : ℝ) ^ i ≤ epsilon i * K (sequence s₀ i) := by
  intro i
  induction i with
  | zero =>
    simp only [sequence, pow_zero, mul_one]
    refine ⟨h₀, ?_⟩
    have h : (256 : ℝ) ≤ K s₀ := by exact_mod_cast h₀
    norm_num [epsilon]
    linarith
  | succ i ih =>
    have hε : 32 ≤ epsilon i * K (sequence s₀ i) := by
      have hh : 1 ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
      nlinarith [ih.2]
    have hstep := one_step_growth ih.1 hε
    have hfour := hstep.2.2.2.2
    change 256 ≤ K (nextS i (sequence s₀ i)) ∧ _
    refine ⟨by omega, ?_⟩
    change 32 * 2 ^ (i + 1) ≤ epsilon (i + 1) * K (nextS i (sequence s₀ i))
    rw [epsilon_succ, pow_succ]
    have hfourr : (4 : ℝ) * K (sequence s₀ i) ≤ K (nextS i (sequence s₀ i)) := by
      exact_mod_cast hfour
    have he := mul_le_mul_of_nonneg_left hfourr (epsilon_pos i).le
    nlinarith [ih.2]


noncomputable def commonBound (k : ℕ) : ℝ :=
  14 + k + 1 / 2 * (2 : ℝ) ^ ((k : ℝ) / 8) * ((k : ℝ) + 1) ^ 2

lemma common_bound {k : ℕ} (hk : 256 ≤ k) :
    commonBound k ≤ (2 : ℝ) ^ ((k : ℝ) / 4) ∧
      (2 : ℝ) ^ ((k : ℝ) / 4) ≤ (1 / 8 : ℝ) * 2 ^ ((k : ℝ) / 3) := by
  obtain ⟨ha, hb, _⟩ := polynomial_root_budget hk
  have hkr : (256 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : 0 < (2 : ℝ) ^ ((k : ℝ) / 8) := by positivity
  have htwo : 2 ≤ (2 : ℝ) ^ ((k : ℝ) / 8) := by
    calc
      _ = (2 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hs : ((2 : ℝ) ^ ((k : ℝ) / 8)) ^ 2 = (2 : ℝ) ^ ((k : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1; push_cast; ring
  constructor
  · unfold commonBound
    nlinarith [mul_le_mul_of_nonneg_left hb hp.le]
  · have h : (2 : ℝ) ^ ((k : ℝ) / 4 + 3) ≤ (2 : ℝ) ^ ((k : ℝ) / 3) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at h
    norm_num at h
    linarith

lemma log_tolerance : Real.logb 2 (10000 : ℝ) < 14 := by
  have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 10000)
    (by norm_num : (10000 : ℝ) < 2 ^ 14)
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h
  simpa only [Nat.cast_ofNat, mul_one] using h

/-- The logarithmic filter budget at consecutive source levels. -/
lemma filter_exponent {i s : ℕ} (hk : 256 ≤ K s) (hε : 32 ≤ epsilon i * K s) :
    Real.logb 2 (10000 : ℝ) + K s +
      (2 : ℝ) ^ (K s / 8) * ell s / 2 -
      ((K (nextS i s) - K (nextS i s) / 2 : ℕ) : ℝ) / 2 ≤
      -(1 / 8 : ℝ) * (2 : ℝ) ^ ((K s : ℝ) / 3) := by
  have hg := (one_step_growth hk hε).2.2.1
  have hc := (common_bound hk).1.trans (common_bound hk).2
  have hd : (2 : ℝ) ^ (K s / 8) ≤ (2 : ℝ) ^ ((K s : ℝ) / 8) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h := Nat.div_mul_le_self (K s) 8
    have hr : ((K s / 8 : ℕ) : ℝ) * 8 ≤ K s := by exact_mod_cast h
    linarith
  have hdiv : (K (nextS i s) : ℝ) / 2 ≤
      ((K (nextS i s) - K (nextS i s) / 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (Nat.div_le_self _ _)]
    have h := Nat.div_mul_le_self (K (nextS i s)) 2
    have hr : ((K (nextS i s) / 2 : ℕ) : ℝ) * 2 ≤ K (nextS i s) := by exact_mod_cast h
    linarith
  have hp := mul_le_mul hd (K_bounds s).2.le (ell_nonneg s)
    (show 0 ≤ (2 : ℝ) ^ ((K s : ℝ) / 8) by positivity)
  unfold commonBound at hc
  nlinarith [log_tolerance]

/-- The logarithmic window budget, with exactly the source cardinalities. -/
lemma window_exponent {i s : ℕ} (hk : 256 ≤ K s) (hε : 32 ≤ epsilon i * K s) :
    Real.logb 2 (10000 : ℝ) + K s +
      (2 : ℝ) ^ (K s / 8) * ell s / 2 - ell (nextS i s) / 2 ≤
      -(2 : ℝ) ^ K s / 4 := by
  have hg := (one_step_growth hk hε).2.1
  have hc := (common_bound hk).1
  have hd : (2 : ℝ) ^ (K s / 8) ≤ (2 : ℝ) ^ ((K s : ℝ) / 8) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h := Nat.div_mul_le_self (K s) 8
    have hr : ((K s / 8 : ℕ) : ℝ) * 8 ≤ K s := by exact_mod_cast h
    linarith
  have hp := mul_le_mul hd (K_bounds s).2.le (ell_nonneg s)
    (show 0 ≤ (2 : ℝ) ^ ((K s : ℝ) / 8) by positivity)
  have hkr : (256 : ℝ) ≤ K s := by exact_mod_cast hk
  have hsmall : (2 : ℝ) ^ ((K s : ℝ) / 4) ≤ (2 : ℝ) ^ K s / 4 := by
    have h : (2 : ℝ) ^ ((K s : ℝ) / 4 + 2) ≤ (2 : ℝ) ^ (K s : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at h
    norm_num at h
    linarith
  unfold commonBound at hc
  nlinarith [log_tolerance]

lemma distance_exponent {i s : ℕ} (hk : 256 ≤ K s) (hε : 32 ≤ epsilon i * K s) :
    5 + K s + 3 * ell (nextS i s) +
      (6 * K s + 1) * (2 : ℝ) ^ K s - epsilon i * (2 : ℝ) ^ K s * ell s / 2 ≤
      -(K s : ℝ) * (2 : ℝ) ^ K s := by
  have hround := (rounding (one_step_growth hk hε).1).2.1
  have hel : 32 * K s ≤ epsilon i * ell s := by
    have h1 := mul_le_mul_of_nonneg_left (K_bounds s).1 (epsilon_pos i).le
    have h2 := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg (K s) : (0 : ℝ) ≤ K s)
    nlinarith
  have hel' := mul_le_mul_of_nonneg_right hel
    (show 0 ≤ (2 : ℝ) ^ K s by positivity)
  have hkr : (256 : ℝ) ≤ K s := by exact_mod_cast hk
  have hp : 1 ≤ (2 : ℝ) ^ K s := one_le_pow₀ (by norm_num)
  unfold X at hround
  nlinarith


noncomputable def alphabetSize (s : ℕ) : ℝ := (2 : ℝ) ^ (2 * s) - 1
noncomputable def filterBudget (s t : ℕ) : ℝ :=
  10000 * (2 : ℝ) ^ K s * Real.sqrt
    (alphabetSize s ^ (2 ^ (K s / 8)) / (2 : ℝ) ^ (K t - K t / 2))
noncomputable def windowBudget (s t : ℕ) : ℝ :=
  10000 * (2 : ℝ) ^ K s * Real.sqrt
    (alphabetSize s ^ (2 ^ (K s / 8)) / alphabetSize t)
noncomputable def distanceBudget (i s t : ℕ) : ℝ :=
  32 * (2 : ℝ) ^ K s * alphabetSize t ^ 3 *
    (2 : ℝ) ^ ((6 * K s + 1) * 2 ^ K s) *
      alphabetSize s ^ (-epsilon i * (2 : ℝ) ^ K s / 2)

lemma s_pos_of_Kpos {s : ℕ} (hk : 0 < K s) : 1 ≤ s := by
  by_contra h
  have hz : s = 0 := by omega
  subst s
  simp [K, ell_zero] at hk

lemma alphabetSize_pos {s : ℕ} (hs : 1 ≤ s) : 0 < alphabetSize s := by
  have h : (1 : ℝ) < 2 ^ (2 * s) := one_lt_pow₀ (by norm_num) (by omega)
  unfold alphabetSize
  linarith

lemma log_sqrt {x : ℝ} (hx : 0 < x) : Real.logb 2 (Real.sqrt x) = Real.logb 2 x / 2 := by
  rw [Real.sqrt_eq_rpow, Real.logb_rpow_eq_mul_logb_of_pos hx]
  ring

lemma filterBudget_pos {s : ℕ} (hs : 1 ≤ s) (t : ℕ) : 0 < filterBudget s t := by
  unfold filterBudget
  have := alphabetSize_pos hs
  positivity

lemma windowBudget_pos {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) : 0 < windowBudget s t := by
  unfold windowBudget
  have := alphabetSize_pos hs
  have := alphabetSize_pos ht
  positivity

lemma distanceBudget_pos {i s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) : 0 < distanceBudget i s t := by
  unfold distanceBudget
  have := alphabetSize_pos hs
  have := alphabetSize_pos ht
  positivity

lemma log_filterBudget {s : ℕ} (hs : 1 ≤ s) (t : ℕ) :
    Real.logb 2 (filterBudget s t) = Real.logb 2 (10000 : ℝ) + K s +
      (2 : ℝ) ^ (K s / 8) * ell s / 2 -
      ((K t - K t / 2 : ℕ) : ℝ) / 2 := by
  have hL := alphabetSize_pos hs
  unfold filterBudget
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by norm_num) (by positivity),
    log_sqrt (by positivity), Real.logb_div (by positivity) (by positivity)]
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one,
    Nat.cast_pow, Nat.cast_ofNat]
  change Real.logb 2 (10000 : ℝ) + K s +
    ((2 : ℝ) ^ (K s / 8) * ell s - ((K t - K t / 2 : ℕ) : ℝ)) / 2 = _
  ring

lemma log_windowBudget {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    Real.logb 2 (windowBudget s t) = Real.logb 2 (10000 : ℝ) + K s +
      (2 : ℝ) ^ (K s / 8) * ell s / 2 - ell t / 2 := by
  have hL := alphabetSize_pos hs
  have hM := alphabetSize_pos ht
  unfold windowBudget
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by norm_num) (by positivity),
    log_sqrt (by positivity), Real.logb_div (by positivity) (by positivity)]
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one,
    Nat.cast_pow, Nat.cast_ofNat]
  change Real.logb 2 (10000 : ℝ) + K s +
    ((2 : ℝ) ^ (K s / 8) * ell s - ell t) / 2 = _
  ring

lemma log_distanceBudget {i s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    Real.logb 2 (distanceBudget i s t) =
      5 + K s + 3 * ell t + (6 * K s + 1) * (2 : ℝ) ^ K s -
        epsilon i * (2 : ℝ) ^ K s * ell s / 2 := by
  have hL := alphabetSize_pos hs
  have hM := alphabetSize_pos ht
  have h32 : Real.logb 2 (32 : ℝ) = 5 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num]
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  unfold distanceBudget
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by norm_num) (by positivity),
    Real.logb_rpow_eq_mul_logb_of_pos hL]
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one,
    Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add, Nat.cast_one, h32]
  change 5 + K s + 3 * ell t + (6 * K s + 1) * (2 : ℝ) ^ K s +
    (-epsilon i * (2 : ℝ) ^ K s / 2) * ell s = _
  ring

/-- All actual probability budgets, not just formal logarithmic surrogates,
are controlled at the single fixed initial threshold. -/
theorem actual_budgets {i s : ℕ} (hk : 256 ≤ K s) (hε : 32 ≤ epsilon i * K s) :
    filterBudget s (nextS i s) < 1 / 2 ∧
      windowBudget s (nextS i s) < 1 / 4 ∧
      distanceBudget i s (nextS i s) < 1 / 4 := by
  have hs : 1 ≤ s := s_pos_of_Kpos (by omega)
  have hstep := one_step_growth hk hε
  have ht : 1 ≤ nextS i s := s_pos_of_Kpos (by omega)
  have hkr : (256 : ℝ) ≤ K s := by exact_mod_cast hk
  have hthird : 16 ≤ (2 : ℝ) ^ ((K s : ℝ) / 3) := by
    calc
      _ = (2 : ℝ) ^ (4 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hpow : 16 ≤ (2 : ℝ) ^ K s := by
    calc
      _ = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have hlog2 : Real.logb 2 (1 / 2 : ℝ) = -1 := by
    rw [Real.logb_div (by norm_num) (by norm_num)]
    simp
  have hlog4 : Real.logb 2 (1 / 4 : ℝ) = -2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    rw [Real.logb_div (by norm_num) (by norm_num), Real.logb_pow]
    simp
  refine ⟨?_, ?_, ?_⟩
  · apply (Real.logb_lt_logb_iff (by norm_num : (1 : ℝ) < 2) (filterBudget_pos hs _) (by norm_num)).mp
    rw [log_filterBudget hs, hlog2]
    linarith [filter_exponent hk hε]
  · apply (Real.logb_lt_logb_iff (by norm_num : (1 : ℝ) < 2) (windowBudget_pos hs ht) (by norm_num)).mp
    rw [log_windowBudget hs ht, hlog4]
    linarith [window_exponent hk hε]
  · apply (Real.logb_lt_logb_iff (by norm_num : (1 : ℝ) < 2) (distanceBudget_pos (i := i) hs ht) (by norm_num)).mp
    rw [log_distanceBudget hs ht, hlog4]
    nlinarith [distance_exponent hk hε]

end SmoothObstruction.WordParameters

namespace SmoothObstruction.WordParameters

noncomputable def length (s₀ : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => length s₀ i * 2 ^ K (sequence s₀ i)

noncomputable def rate (s₀ i : ℕ) : ℝ := ell (sequence s₀ i) / length s₀ i

lemma length_pos (s₀ i : ℕ) : 0 < length s₀ i := by
  induction i with
  | zero => simp [length]
  | succ i ih => exact Nat.mul_pos ih (by positivity)

lemma length_dvd (s₀ i : ℕ) : length s₀ i ∣ length s₀ (i + 1) :=
  ⟨2 ^ K (sequence s₀ i), rfl⟩

lemma length_eq_pow (s₀ i : ℕ) :
    length s₀ i = 2 ^ (∑ j ∈ Finset.range i, K (sequence s₀ j)) := by
  induction i with
  | zero => simp [length]
  | succ i ih => rw [length, ih, Finset.sum_range_succ, pow_add]

lemma log_length (s₀ i : ℕ) : Real.logb 2 (length s₀ i) =
    ∑ j ∈ Finset.range i, (K (sequence s₀ j) : ℝ) := by
  rw [length_eq_pow]
  push_cast
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  push_cast
  rfl

lemma step_conditions {s₀ : ℕ} (h₀ : 256 ≤ K s₀) (i : ℕ) :
    256 ≤ K (sequence s₀ i) ∧ 32 ≤ epsilon i * K (sequence s₀ i) := by
  have h := sequence_growth h₀ i
  refine ⟨h.1, ?_⟩
  have hp : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  nlinarith [h.2]

lemma length_ge_two_pow {s₀ : ℕ} (h₀ : 256 ≤ K s₀) (i : ℕ) :
    2 ^ i ≤ length s₀ i := by
  induction i with
  | zero => simp [length]
  | succ i ih =>
    have hk := (sequence_growth h₀ i).1
    rw [length, pow_succ]
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2)
      (show 1 ≤ K (sequence s₀ i) by omega)
    exact Nat.mul_le_mul ih (by simpa using hpow)

lemma length_unbounded {s₀ : ℕ} (h₀ : 256 ≤ K s₀) (n : ℕ) :
    ∃ i, n < length s₀ i := by
  refine ⟨n, (Nat.lt_two_pow_self (n := n)).trans_le (length_ge_two_pow h₀ n)⟩

lemma rate_pos {s₀ : ℕ} (h₀ : 256 ≤ K s₀) (i : ℕ) : 0 < rate s₀ i := by
  have hk := (sequence_growth h₀ i).1
  have hkr : (256 : ℝ) ≤ K (sequence s₀ i) := by exact_mod_cast hk
  apply div_pos _ (by exact_mod_cast length_pos s₀ i)
  have hb := (K_bounds (sequence s₀ i)).1
  nlinarith

lemma rate_step {s₀ : ℕ} (h₀ : 256 ≤ K s₀) (i : ℕ) :
    epsilon i / 200 * rate s₀ i ≤ rate s₀ (i + 1) := by
  obtain ⟨hk, he⟩ := step_conditions h₀ i
  have hx := (one_step_growth hk he).1
  have hr := (rounding hx).2.2
  unfold rate
  rw [sequence, length, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  apply (le_div_iff₀ (mul_pos (by exact_mod_cast length_pos s₀ i) (by positivity))).mpr
  have hm : (length s₀ i : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast length_pos s₀ i)
  calc
    _ = X i (sequence s₀ i) / 2 := by unfold X; field_simp; ring
    _ ≤ _ := hr

lemma rate_step_dyadic {s₀ : ℕ} (h₀ : 256 ≤ K s₀) (i : ℕ) :
    rate s₀ i / (2 : ℝ) ^ (i + 11) ≤ rate s₀ (i + 1) := by
  have hp : 0 < rate s₀ i := rate_pos h₀ i
  calc
    _ ≤ epsilon i / 200 * rate s₀ i := by
      unfold epsilon
      rw [show i + 11 = (i + 3) + 8 by omega, pow_add]
      norm_num
      field_simp
      nlinarith
    _ ≤ _ := rate_step h₀ i

/-- The exact dyadic rate lower bound, with the finite arithmetic sum left
unrounded (its value is i(i+21)/2). Level zero is source level one. -/
theorem rate_lower {s₀ : ℕ} (h₀ : 256 ≤ K s₀) (i : ℕ) :
    rate s₀ 0 / (2 : ℝ) ^ (∑ j ∈ Finset.range i, (j + 11)) ≤ rate s₀ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ, pow_add, ← div_div]
    exact (div_le_div_of_nonneg_right ih (by positivity)).trans (rate_step_dyadic h₀ i)

lemma exponent_sum (i : ℕ) :
    (2 : ℕ) * (∑ j ∈ Finset.range i, (j + 11)) = i * (i + 21) := by
  induction i with
  | zero => simp
  | succ i ih => rw [Finset.sum_range_succ]; nlinarith

lemma K_double_exponential {s₀ : ℕ} (h₀ : 256 ≤ K s₀) (i : ℕ) :
    2 ^ (8 * 2 ^ i) ≤ K (sequence s₀ i) := by
  induction i with
  | zero => simpa [sequence] using h₀
  | succ i ih =>
    obtain ⟨hk, he⟩ := step_conditions h₀ i
    have hs := (one_step_growth hk he).2.2.2.1
    change _ ≤ K (nextS i (sequence s₀ i))
    calc
      _ = (2 ^ (8 * 2 ^ i)) ^ 2 := by rw [← pow_mul, pow_succ]; congr 1; omega
      _ ≤ K (sequence s₀ i) ^ 2 := Nat.pow_le_pow_left ih 2
      _ ≤ _ := hs

lemma double_exp_budget (i : ℕ) (hi : 16 ≤ i) :
    16 * (∑ j ∈ Finset.range i, (j + 11)) ≤ 8 * 2 ^ i := by
  have hpoly : i * (i + 21) ≤ 2 ^ i := by
    induction i, hi using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [pow_succ]
      have hmul : (n + 1) * (n + 1 + 21) ≤ 2 * (n * (n + 21)) := by nlinarith
      nlinarith
  have hs := exponent_sum i
  nlinarith

/-- Source divergence: the available-scale information cannot be summable.
The proof gives an explicit positive lower bound after level16, not merely
an informal comparison of logarithmic growth rates. -/
theorem rates_not_summable {s₀ : ℕ} (h₀ : 256 ≤ K s₀) :
    ¬ Summable (fun i => (K (sequence s₀ i) : ℝ) * rate s₀ i ^ 16) := by
  have hlower (i : ℕ) (hi : 16 ≤ i) : rate s₀ 0 ^ 16 ≤
      (K (sequence s₀ i) : ℝ) * rate s₀ i ^ 16 := by
    let t := ∑ j ∈ Finset.range i, (j + 11)
    have hg : (2 : ℝ) ^ (16 * t) ≤ K (sequence s₀ i) := by
      have h1 := Nat.pow_le_pow_right (by decide : 0 < 2) (double_exp_budget i hi)
      exact_mod_cast h1.trans (K_double_exponential h₀ i)
    have hr := pow_le_pow_left₀ (div_nonneg (rate_pos h₀ 0).le (by positivity) :
        0 ≤ rate s₀ 0 / (2 : ℝ) ^ t)
      (rate_lower h₀ i) 16
    have hp : 0 < (2 : ℝ) ^ t := by positivity
    have heq : rate s₀ 0 ^ 16 = (2 : ℝ) ^ (16 * t) *
        (rate s₀ 0 / (2 : ℝ) ^ t) ^ 16 := by
      rw [div_pow, ← pow_mul]
      rw [Nat.mul_comm t 16]
      field_simp
    rw [heq]
    exact mul_le_mul hg hr (by positivity) (by positivity)
  intro hs
  have hlim := hs.tendsto_atTop_zero
  have hle : rate s₀ 0 ^ 16 ≤ 0 := ge_of_tendsto hlim (eventually_atTop.2 ⟨16, hlower⟩)
  exact (not_le_of_gt (pow_pos (rate_pos h₀ 0) 16)) hle

end SmoothObstruction.WordParameters

namespace SmoothObstruction.WordParameters

/-- A concrete admissible first vector dimension. It makes the main
construction's initial-size condition nonvacuous. -/
lemma initial_threshold : 256 ≤ K 40000 := by
  unfold K
  apply Nat.le_floor
  apply (Real.le_sqrt (by norm_num) (ell_nonneg 40000)).mpr
  have h := (ell_bounds (by norm_num : 1 ≤ (40000 : ℕ))).1
  norm_num at h ⊢
  linarith

/-- The actual nonzero symplectic sampler always has a nonzero choice. -/
lemma dimension_budget {s : ℕ} (hK : 256 ≤ K s) : K s + 1 ≤ 2 * s := by
  have hs : 1 ≤ s := by
    by_contra hn
    have hz : s = 0 := by omega
    simp [hz, K, ell_zero] at hK
  have hl := (ell_bounds hs).2
  have hk := (K_bounds s).1
  have hkreal : (256 : ℝ) ≤ K s := by exact_mod_cast hK
  have h : (K s : ℝ) + 1 < 2 * s := by nlinarith
  have hn : K s + 1 < 2 * s := by exact_mod_cast h
  exact hn.le

end SmoothObstruction.WordParameters

end

section

open Finset

namespace SmoothObstruction.WordAlphabet

/-- The two coordinate halves of the source's F₂^(2s); this product is the
canonical coordinate bijection, not a different graph or bilinear form. -/
abbrev Space (s : ℕ) := (Fin s → ZMod 2) × (Fin s → ZMod 2)
abbrev Alphabet (s : ℕ) := {v : Space s // v ≠ 0}

def form (s : ℕ) : LinearMap.BilinForm (ZMod 2) (Space s) :=
  LinearMap.mk₂ (ZMod 2) (fun u v => ∑ a, (u.1 a * v.2 a + u.2 a * v.1 a))
    (by intro u v w; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply];
        simp only [add_mul, sum_add_distrib]; ring)
    (by intro c u v; simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul];
        simp only [mul_assoc, ← mul_add, ← mul_sum])
    (by intro u v w; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply];
        simp only [mul_add, sum_add_distrib]; ring)
    (by intro c u v; simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul];
        simp only [mul_left_comm _ c, ← mul_add, ← mul_sum])

lemma form_apply (s : ℕ) (u v : Space s) :
    form s u v = ∑ a, (u.1 a * v.2 a + u.2 a * v.1 a) := rfl

lemma form_alt (s : ℕ) : (form s).IsAlt := by
  intro u
  rw [form_apply]
  apply sum_eq_zero
  intro a _
  rw [mul_comm (u.2 a) (u.1 a), ← two_mul]
  rw [show (2 : ZMod 2) = 0 by decide, zero_mul]

lemma form_symm (s : ℕ) (u v : Space s) : form s u v = form s v u := by
  rw [form_apply, form_apply]
  apply sum_congr rfl
  intro a _
  ring

lemma form_nondegenerate (s : ℕ) : (form s).Nondegenerate := by
  have hleft (u : Space s) (hu : ∀ v, form s u v = 0) : u = 0 := by
    apply Prod.ext <;> apply funext
    · intro a
      have h := hu (0, Pi.single a 1)
      simpa [form_apply, Pi.single_apply, mul_ite] using h
    · intro a
      have h := hu (Pi.single a 1, 0)
      simpa [form_apply, Pi.single_apply, mul_ite] using h
  exact ⟨hleft, fun v hv => hleft v (fun u => (form_symm s v u).trans (hv u))⟩

lemma finrank (s : ℕ) : Module.finrank (ZMod 2) (Space s) = 2 * s := by
  rw [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin]
  omega

lemma card_space (s : ℕ) : Fintype.card (Space s) = 2 ^ (2 * s) := by
  simp only [Space, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [← pow_add]
  congr 1
  omega

lemma card_alphabet (s : ℕ) : Fintype.card (Alphabet s) = 2 ^ (2 * s) - 1 := by
  have h := Fintype.card_congr (Equiv.optionSubtypeNe (0 : Space s))
  rw [Fintype.card_option, card_space] at h
  change Fintype.card {v : Space s // v ≠ 0} = _
  omega

end SmoothObstruction.WordAlphabet

end

section

open Filter Topology

namespace SmoothObstruction.CheapScales
open Filter Finset

/-- A summable nonnegative expense cannot dominate a nonsummable information
budget on pairwise disjoint finite test sets. -/
theorem arbitrarily_late_cheap {J : ℕ → Finset ℕ}
    (hJ : ∀ i i', i ≠ i' → Disjoint (J i) (J i'))
    {B R : ℕ → ℝ} (hR : ∀ i,0≤R i)
    (hBs : Summable (fun j => (B j)^16))
    (hRs : ¬Summable (fun i => (J i).card*(R i)^16))
    {ε : ℝ} (hε : 0<ε) (N : ℕ) :
    ∃ i≥N, ∃ j∈J i,B j<ε*R i := by
  classical
  let idx : (Σ i,{j // j∈J i}) → ℕ := fun p => p.2.val
  have hinj : Function.Injective idx := by
    intro ⟨i,j,hj⟩ ⟨i',j',hj'⟩ h
    change j=j' at h
    subst j'
    have hi : i=i' := by
      by_contra hn
      exact (Finset.disjoint_left.mp (hJ i i' hn) hj hj')
    subst i'
    rfl
  have hsum := (hBs.comp_injective hinj).sigma
  have hsum' : Summable (fun i => ∑ j∈J i,(B j)^16) := by
    apply hsum.congr
    intro i
    change (∑' j : {j // j∈J i}, (B j.val)^16)=_
    rw [tsum_fintype]
    exact Finset.sum_finset_coe (fun j => (B j)^16) (J i)
  by_contra hc
  push Not at hc
  have hbound (i : ℕ) : (ε^16)*((J (i+N)).card*(R (i+N))^16) ≤
      ∑ j∈J (i+N),(B j)^16 := by
    calc
      _ = ∑ j∈J (i+N),(ε*R (i+N))^16 := by simp [mul_pow]; ring
      _ ≤ _ := Finset.sum_le_sum (fun j hj =>
        pow_le_pow_left₀ (mul_nonneg hε.le (hR _)) (hc (i+N) (by omega) j hj) 16)
  have hs := ((summable_nat_add_iff N).mpr hsum').of_nonneg_of_le
    (fun i => mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) (by positivity))) hbound
  have ht := hs.mul_left (ε^16)⁻¹
  have ht' : Summable (fun i => (J (i+N)).card*(R (i+N))^16) := by
    simpa only [←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hε.ne'),one_mul] using ht
  exact hRs ((summable_nat_add_iff N).mp ht')

/-- Successively late tests with ratios tending to zero; positivity is retained
for the source information rate, so the ratio is not a totalized-division trick. -/
theorem cheap_sequence {J : ℕ → Finset ℕ}
    (hJ : ∀ i i', i ≠ i' → Disjoint (J i) (J i'))
    {B R : ℕ → ℝ} (hB : ∀ j,0≤B j) (hR : ∀ i,0<R i)
    (hBs : Summable (fun j => (B j)^16))
    (hRs : ¬Summable (fun i => (J i).card*(R i)^16)) :
    ∃ (i j : ℕ → ℕ), (∀ a : ℕ, a ≤ i a) ∧ (∀ a : ℕ, j a ∈ J (i a)) ∧
      Tendsto i atTop atTop ∧ Tendsto (fun a => B (j a)/R (i a)) atTop (nhds 0) := by
  have hex (a : ℕ) := arbitrarily_late_cheap hJ (fun i => (hR i).le) hBs hRs
    (show 0<(1:ℝ)/(a+1) by positivity) a
  choose i hi j hj hcheap using hex
  refine ⟨i,j,hi,hj,tendsto_atTop_mono hi tendsto_id,?_⟩
  apply squeeze_zero (fun a => div_nonneg (hB _) (hR _).le)
      (fun a => (div_le_iff₀ (hR _)).mpr (hcheap a).le)
  simpa only [Nat.cast_add,Nat.cast_one] using
    (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun a : ℕ => (1:ℝ)/(a+1)) atTop (nhds 0))

end SmoothObstruction.CheapScales

namespace SmoothObstruction.WordParameters
open Filter Finset

noncomputable def logLevel (s₀ i : ℕ) : ℕ := ∑ j∈Finset.range i, K (sequence s₀ j)
noncomputable def testScales (s₀ i : ℕ) : Finset ℕ :=
  Finset.Icc (logLevel s₀ i+(K (sequence s₀ i)+15)/16)
    (logLevel s₀ i+K (sequence s₀ i)/8)

lemma logLevel_succ (s₀ i : ℕ) :
    logLevel s₀ (i+1)=logLevel s₀ i+K (sequence s₀ i) := by
  simp only [logLevel,Finset.sum_range_succ]

lemma logLevel_strictMono {s₀ : ℕ} (h₀ : 256≤K s₀) : StrictMono (logLevel s₀) := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [logLevel_succ]
  have := (step_conditions h₀ i).1
  omega

lemma testScales_disjoint {s₀ : ℕ} (h₀ : 256≤K s₀) :
    ∀ i i', i≠i' → Disjoint (testScales s₀ i) (testScales s₀ i') := by
  have hd (i i' : ℕ) (hi : i< i') : Disjoint (testScales s₀ i) (testScales s₀ i') := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    simp only [testScales,Finset.mem_Icc] at hj hj'
    have hm := (logLevel_strictMono h₀).monotone (show i+1≤ i' by omega)
    rw [logLevel_succ] at hm
    have hk := (step_conditions h₀ i).1
    omega
  intro i i' hi
  rcases lt_or_gt_of_ne hi with h|h
  · exact hd i i' h
  · exact (hd i' i h).symm

lemma testScales_card {s₀ : ℕ} (h₀ : 256≤K s₀) (i : ℕ) :
    K (sequence s₀ i) ≤ 32*(testScales s₀ i).card := by
  rw [testScales,Nat.card_Icc]
  have hk := (step_conditions h₀ i).1
  omega

lemma testScales_not_summable {s₀ : ℕ} (h₀ : 256≤K s₀) :
    ¬ Summable (fun i => (testScales s₀ i).card*(rate s₀ i)^16) := by
  intro hs
  apply rates_not_summable h₀
  apply (hs.mul_left 32).of_nonneg_of_le
  · intro i; positivity
  · intro i
    have hh : (K (sequence s₀ i) : ℝ)≤32*(testScales s₀ i).card := by
      exact_mod_cast testScales_card h₀ i
    nlinarith [mul_le_mul_of_nonneg_right hh (show 0≤(rate s₀ i)^16 by positivity)]

/-- The source's actual disjoint tests, with their full stated range and
no enlargement or alteration of the word recursion. -/
theorem actual_cheap_scales {s₀ : ℕ} (h₀ : 256≤K s₀)
    {B : ℕ → ℝ} (hB : ∀ j,0<B j) (hBs : Summable (fun j => (B j)^16)) :
    ∃ (i j : ℕ → ℕ), (∀ a : ℕ,a≤ i a) ∧ (∀ a,j a∈testScales s₀ (i a)) ∧
      Tendsto i atTop atTop ∧
      Tendsto (fun a => B (j a)/rate s₀ (i a)) atTop (nhds 0) ∧
      ∀ a, ∃ t : ℕ, (K (sequence s₀ (i a))+15)/16≤t ∧
        t≤K (sequence s₀ (i a))/8 ∧
        length s₀ (i a)*2^t=2^(j a) ∧ 2≤2^t := by
  obtain ⟨i,j,hi,hj,hit,hcheap⟩ := CheapScales.cheap_sequence (testScales_disjoint h₀)
    (fun j => (hB j).le) (rate_pos h₀) hBs (testScales_not_summable h₀)
  refine ⟨i,j,hi,hj,hit,hcheap,fun a => ?_⟩
  have hh := hj a
  simp only [testScales,Finset.mem_Icc] at hh
  let t := j a-logLevel s₀ (i a)
  have ht : j a=logLevel s₀ (i a)+t := by omega
  have htrange : (K (sequence s₀ (i a))+15)/16≤t ∧ t≤K (sequence s₀ (i a))/8 := by omega
  refine ⟨t,htrange.1,htrange.2,?_,?_⟩
  · rw [length_eq_pow,←pow_add,ht]
    rfl
  · have hk := (step_conditions h₀ (i a)).1
    have hp : 1≤t := by omega
    exact (by decide : 2≤2^1).trans (Nat.pow_le_pow_right (by decide) hp)

end SmoothObstruction.WordParameters

end

end OAI
