import OAI.Probability.RandomSAT.Clauses

namespace OAI

/-!
Quantitative comparison of a shorter clause with a block of independent proper
clauses, uniformly over the background solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

def killFraction (b n r : ℕ) : ℝ := (b.choose r : ℝ) / ((n.choose r : ℝ) * 2 ^ r)

theorem killFraction_nonneg (b n r : ℕ) : 0 ≤ killFraction b n r := by
  unfold killFraction
  positivity

@[simp] theorem killFraction_zero (b n : ℕ) : killFraction b n 0 = 1 := by
  simp [killFraction]

theorem killFraction_succ {b n r : ℕ} (hrn : r + 1 ≤ n) :
    killFraction b n (r + 1) =
      killFraction b n r * ((b - r : ℕ) : ℝ) / (2 * ((n - r : ℕ) : ℝ)) := by
  have hnc : (n.choose r : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (by omega : r ≤ n))
  have hncs : (n.choose (r + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hrn)
  have hnr : ((n - r : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : n - r ≠ 0)
  have hb : (b.choose (r + 1) : ℝ) * (r + 1) =
      (b.choose r : ℝ) * ((b - r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq b r
  have hn : (n.choose (r + 1) : ℝ) * (r + 1) =
      (n.choose r : ℝ) * ((n - r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n r
  unfold killFraction
  rw [pow_succ]
  field_simp
  nlinarith [congrArg (fun a : ℝ => a * (n.choose (r + 1) : ℝ)) hb,
    congrArg (fun a : ℝ => a * (b.choose (r + 1) : ℝ)) hn]

theorem sub_ratio_le {b n r : ℕ} (hbn : b ≤ n) (hrb : r ≤ b) (hrn : r < n) :
    ((b - r : ℕ) : ℝ) / ((n - r : ℕ) : ℝ) ≤ (b : ℝ) / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnr : (0 : ℝ) < (n - r : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hrn
  rw [div_le_div_iff₀ hnr hn, Nat.cast_sub hrb, Nat.cast_sub (Nat.le_of_lt hrn)]
  have hbn' : (b : ℝ) ≤ n := by exact_mod_cast hbn
  nlinarith [mul_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r) (sub_nonneg.mpr hbn')]

theorem killFraction_le_pow {b n r : ℕ} (hbn : b ≤ n) (hrn : r ≤ n)
    (hn : 0 < n) : killFraction b n r ≤ ((b : ℝ) / (2 * n)) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    by_cases hbr : b < r + 1
    · simp only [killFraction, Nat.choose_eq_zero_of_lt hbr, Nat.cast_zero, zero_div]
      positivity
    · have hrb : r ≤ b := by omega
      have ih' := ih (by omega)
      rw [killFraction_succ hrn, pow_succ]
      have hratio := sub_ratio_le hbn hrb (by omega : r < n)
      have hhalf : ((b - r : ℕ) : ℝ) / (2 * ((n - r : ℕ) : ℝ)) ≤
          (b : ℝ) / (2 * n) := by
        simpa only [div_mul_eq_div_div_swap] using div_le_div_of_nonneg_right hratio
          (by norm_num : (0 : ℝ) ≤ 2)
      calc
        killFraction b n r * ((b - r : ℕ) : ℝ) / (2 * ((n - r : ℕ) : ℝ)) =
            killFraction b n r * (((b - r : ℕ) : ℝ) / (2 * ((n - r : ℕ) : ℝ))) := by ring
        _ ≤ ((b : ℝ) / (2 * n)) ^ r * ((b : ℝ) / (2 * n)) :=
          mul_le_mul ih' hhalf (by positivity) (by positivity)

theorem killFraction_le_half_pow {b n r : ℕ} (hbn : b ≤ n) (hrn : r ≤ n)
    (hn : 0 < n) : killFraction b n r ≤ (1 / 2 : ℝ) ^ r := by
  apply (killFraction_le_pow hbn hrn hn).trans
  apply pow_le_pow_left₀ (by positivity)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
  have hbn' : (b : ℝ) ≤ n := by exact_mod_cast hbn
  linarith

theorem nat_le_internal_choose {n r : ℕ} (hr : 1 ≤ r) (hrn : r < n) :
    n ≤ n.choose r := by
  induction n generalizing r with
  | zero => omega
  | succ n ih =>
    cases r with
    | zero => omega
    | succ r =>
      by_cases h : r = 0
      · subst r
        simp
      · rw [Nat.choose_succ_succ]
        have hlow := ih (by omega : 1 ≤ r) (by omega : r < n)
        have hpos := Nat.choose_pos (by omega : r.succ ≤ n)
        omega

theorem killFraction_small_forcing {b n r : ℕ} (hr : 1 ≤ r) (hrn : r < n)
    (hbr : b ≤ r) : killFraction b n r ≤ 1 / (n + 1 : ℝ) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnc : (n : ℝ) ≤ n.choose r := by exact_mod_cast nat_le_internal_choose hr hrn
  have hb : (b.choose r : ℝ) ≤ 1 := by
    exact_mod_cast (Nat.choose_le_choose r hbr).trans_eq (Nat.choose_self r)
  have hp : (2 : ℝ) ≤ 2 ^ r := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr
  have hncpos : (0 : ℝ) < n.choose r := by linarith
  have hden : (0 : ℝ) < (n.choose r : ℝ) * 2 ^ r := by positivity
  unfold killFraction
  apply (div_le_div_iff₀ hden (by positivity : (0 : ℝ) < n + 1)).mpr
  nlinarith [mul_le_mul hnc hp (by positivity : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ n.choose r)]

theorem succ_ratio_lower {b n r : ℕ} (hrb : r + 1 ≤ b) (hrn : r < n) :
    (b : ℝ) / (2 * n * (r + 1)) ≤
      ((b - r : ℕ) : ℝ) / (2 * ((n - r : ℕ) : ℝ)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnr : (0 : ℝ) < (n - r : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hrn
  have hrb' : (r + 1 : ℝ) ≤ b := by exact_mod_cast hrb
  have hr : (0 : ℝ) ≤ r := by positivity
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n * (r + 1))
    (by positivity : (0 : ℝ) < 2 * (n - r : ℕ))]
  rw [Nat.cast_sub (by omega : r ≤ b), Nat.cast_sub (Nat.le_of_lt hrn)]
  have haux : (b : ℝ) ≤ (b - r) * (r + 1) := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hrb')]
  nlinarith [mul_le_mul_of_nonneg_right haux hn.le,
    mul_nonneg (Nat.cast_nonneg b : (0 : ℝ) ≤ b) hr]

theorem killFraction_succ_lower {b n r : ℕ} (hrb : r + 1 ≤ b) (hrn : r < n) :
    killFraction b n r * ((b : ℝ) / (2 * n)) / (r + 1) ≤
      killFraction b n (r + 1) := by
  rw [killFraction_succ (by omega : r + 1 ≤ n)]
  have h := mul_le_mul_of_nonneg_left (succ_ratio_lower hrb hrn)
    (killFraction_nonneg b n r)
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using h

theorem power_survival_bound {q : ℝ} (_hq0 : 0 ≤ q) (hq1 : q ≤ 1) (g : ℕ) :
    (1 - q) ^ g * (1 + (g : ℝ) * q) ≤ 1 := by
  induction g with
  | zero => simp
  | succ g ih =>
    have hstep : (1 - q) * (1 + ((g : ℝ) + 1) * q) ≤ 1 + (g : ℝ) * q := by
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ g + 1) (sq_nonneg q)]
    calc
      (1 - q) ^ (g + 1) * (1 + ((g + 1 : ℕ) : ℝ) * q) =
          (1 - q) ^ g * ((1 - q) * (1 + ((g : ℝ) + 1) * q)) := by
            push_cast
            ring
      _ ≤ (1 - q) ^ g * (1 + (g : ℝ) * q) :=
        mul_le_mul_of_nonneg_left hstep (pow_nonneg (sub_nonneg.mpr hq1) _)
      _ ≤ 1 := ih

theorem block_ge_of_double {x q : ℝ} {g : ℕ}
    (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hg : 2 * x ≤ (g : ℝ) * q) : x ≤ 1 - (1 - q) ^ g := by
  have h := power_survival_bound hq0 hq1 g
  have hx1 : 0 ≤ 1 - x := by linarith
  have hg0 : 0 ≤ (g : ℝ) * q := by positivity
  have hh : 1 ≤ (1 - x) * (1 + (g : ℝ) * q) := by
    nlinarith [mul_le_mul_of_nonneg_right hg hx1, mul_nonneg hx0 (by linarith : 0 ≤ 1 - 2 * x)]
  have hb : (1 - q) ^ g ≤ 1 - x := by
    exact (mul_le_mul_iff_left₀ (by positivity : 0 < 1 + (g : ℝ) * q)).mp
      (by nlinarith)
  linarith

theorem uniformProbability_true {α : Type*} [Fintype α] [Nonempty α] :
    uniformProbability (fun _ : α => True) = 1 := by
  classical
  unfold uniformProbability
  simp only [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial))]
  rw [Nat.card_eq_fintype_card]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

theorem uniformProbability_false {α : Type*} [Fintype α] :
    uniformProbability (fun _ : α => False) = 0 := by
  simp [uniformProbability]

theorem uniformProbability_congr {α : Type*} [Fintype α] {p q : α → Prop}
    (h : ∀ a, p a ↔ q a) : uniformProbability p = uniformProbability q := by
  unfold uniformProbability
  rw [Fintype.card_congr (Equiv.subtypeEquivRight h)]

theorem uniformProbability_not {α : Type*} [Fintype α] [Nonempty α] (p : α → Prop) :
    uniformProbability (fun a => ¬ p a) = 1 - uniformProbability p := by
  unfold uniformProbability
  rw [Fintype.card_subtype_compl, Nat.cast_sub (Fintype.card_subtype_le p), sub_div,
    div_self (by exact_mod_cast Fintype.card_ne_zero)]

theorem uniformProbability_forall {α : Type*} [Fintype α] (p : α → Prop) (m : ℕ) :
    uniformProbability (fun f : Fin m → α => ∀ i, p (f i)) = uniformProbability p ^ m := by
  unfold uniformProbability
  have hc : Fintype.card {f : Fin m → α // ∀ i, p (f i)} =
      Fintype.card (Fin m → {a : α // p a}) :=
    Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun _ : Fin m => p))
  simp only [← Nat.card_eq_fintype_card] at hc ⊢
  rw [hc]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    div_pow]

theorem uniformProbability_exists {α : Type*} [Fintype α] [Nonempty α]
    (p : α → Prop) (m : ℕ) :
    uniformProbability (fun f : Fin m → α => ∃ i, p (f i)) =
      1 - (1 - uniformProbability p) ^ m := by
  calc
    _ = uniformProbability (fun f : Fin m → α => ¬ ∀ i, ¬ p (f i)) :=
      uniformProbability_congr (fun _ => by simp)
    _ = 1 - uniformProbability (fun f : Fin m → α => ∀ i, ¬ p (f i)) :=
      uniformProbability_not _
    _ = _ := by rw [uniformProbability_forall (fun a => ¬ p a) m, uniformProbability_not]

def blockUNSATProbability {n : ℕ} (k g : ℕ) (S : Finset (Assignment n)) : ℝ :=
  uniformProbability (fun F : Formula n k g =>
    ¬ ∃ σ ∈ S, Satisfies σ F)

theorem blockUNSAT_lower {n k g : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    1 - (1 - uniformProbability (fun C : ProperClause n k => KillsSolutions S C)) ^ g ≤
      blockUNSATProbability k g S := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  rw [← uniformProbability_exists]
  apply uniformProbability_mono
  rintro F ⟨i, hi⟩ ⟨σ, hσ, hs⟩
  exact hi σ hσ (hs i)

theorem replacement_numeric {b v r g : ℕ} {a : ℝ}
    (hr : 1 ≤ r) (hrv : r < v) (hbv : b ≤ v) (ha : 0 < a)
    (hsmall : 1 / (v + 1 : ℝ) ≤ a⁻¹ ^ r)
    (hg : 2 * (r + 1 : ℝ) * a ≤ (g : ℝ)) :
    killFraction b v r - a⁻¹ ^ r ≤ 1 - (1 - killFraction b v (r + 1)) ^ g := by
  let x := killFraction b v r
  let q := killFraction b v (r + 1)
  have hv : 0 < v := by omega
  have hx0 : 0 ≤ x := killFraction_nonneg _ _ _
  have hq0 : 0 ≤ q := killFraction_nonneg _ _ _
  have hxhalf : x ≤ 1 / 2 := by
    apply (killFraction_le_half_pow hbv (Nat.le_of_lt hrv) hv).trans
    calc
      (1 / 2 : ℝ) ^ r ≤ (1 / 2 : ℝ) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hr
      _ = 1 / 2 := by simp
  have hq1 : q ≤ 1 := by
    apply (killFraction_le_half_pow hbv (by omega) hv).trans
    exact pow_le_one₀ (by norm_num) (by norm_num)
  by_cases hx : x ≤ a⁻¹ ^ r
  · have hpow : (1 - q) ^ g ≤ 1 :=
      pow_le_one₀ (sub_nonneg.mpr hq1) (by linarith)
    change x - a⁻¹ ^ r ≤ 1 - (1 - q) ^ g
    linarith
  · have hrb : r + 1 ≤ b := by
      by_contra h
      have hb : b ≤ r := by omega
      have hbound := killFraction_small_forcing hr hrv hb
      exact hx (hbound.trans hsmall)
    have ht : a⁻¹ ≤ (b : ℝ) / (2 * v) := by
      by_contra h
      have hle : (b : ℝ) / (2 * v) ≤ a⁻¹ := (lt_of_not_ge h).le
      have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (b : ℝ) / (2 * v)) hle r
      have hbound := killFraction_le_pow hbv (Nat.le_of_lt hrv) hv
      exact hx (hbound.trans hpow)
    have hat : 1 ≤ a * ((b : ℝ) / (2 * v)) := by
      simpa [ne_of_gt ha] using mul_le_mul_of_nonneg_left ht ha.le
    have hqlo := killFraction_succ_lower hrb hrv
    have hprod : (2 * (r + 1 : ℝ) * a) *
        (x * ((b : ℝ) / (2 * v)) / (r + 1)) ≤ (g : ℝ) * q :=
      mul_le_mul hg hqlo (by positivity) (by positivity)
    have hrpos : (r + 1 : ℝ) ≠ 0 := by positivity
    have heq : (2 * (r + 1 : ℝ) * a) *
        (x * ((b : ℝ) / (2 * v)) / (r + 1)) =
        2 * x * (a * ((b : ℝ) / (2 * v))) := by
      field_simp
    rw [heq] at hprod
    have hdbl : 2 * x ≤ (g : ℝ) * q := by
      nlinarith [mul_le_mul_of_nonneg_left hat (by positivity : 0 ≤ 2 * x)]
    have hb := block_ge_of_double hx0 hxhalf hq0 hq1 hdbl
    have heps : 0 ≤ a⁻¹ ^ r := by positivity
    change x - a⁻¹ ^ r ≤ 1 - (1 - q) ^ g
    linarith

def replacementScale (n k : ℕ) : ℝ := (n : ℝ) ^ (1 / (k : ℝ))

def replacementError (n k : ℕ) : ℝ := (replacementScale n k)⁻¹ ^ (k - 1)

def replacementBlock (n k : ℕ) : ℕ := ⌈2 * (k : ℝ) * replacementScale n k⌉₊

theorem replacementScale_pos {n k : ℕ} (hn : 0 < n) :
    0 < replacementScale n k := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

theorem replacementScale_pow {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    replacementScale n k ^ k = (n : ℝ) := by
  unfold replacementScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  rw [one_div_mul_cancel hk', Real.rpow_one]

theorem replacementScale_one_le {n k : ℕ} (hn : 1 ≤ n) :
    1 ≤ replacementScale n k := by
  unfold replacementScale
  exact Real.one_le_rpow (by exact_mod_cast hn) (by positivity)

theorem replacementError_eq {n k : ℕ} (hn : 0 < n) :
    replacementError n k = (n : ℝ) ^ (-((k - 1 : ℕ) : ℝ) / k) := by
  unfold replacementError replacementScale
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n),
    ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ n)]
  congr 1
  ring

theorem replacementError_small {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    1 / (n : ℝ) ≤ replacementError n k := by
  have ha := replacementScale_pos (k := k) hn
  have hpow : replacementScale n k ^ (k - 1) ≤ (n : ℝ) := by
    calc
      replacementScale n k ^ (k - 1) ≤ replacementScale n k ^ k :=
        pow_le_pow_right₀ (replacementScale_one_le (Nat.succ_le_of_lt hn)) (Nat.sub_le _ _)
      _ = _ := replacementScale_pow hn hk
  unfold replacementError
  rw [inv_pow, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) hpow

theorem shorter_clause_replacement {n k : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (S : Finset (Assignment (n - 1))) :
    uniformProbability (fun Q : ProperClause (n - 1) (k - 1) => KillsSolutions S Q) -
      replacementError n k ≤ blockUNSATProbability k (replacementBlock n k) S := by
  have hkn : k ≤ n - 1 := by omega
  let : Nonempty (ProperClause (n - 1) k) := nonempty_properClause hkn
  have heps : 0 ≤ replacementError n k :=
    pow_nonneg (inv_nonneg.mpr (replacementScale_pos (k := k) (by omega)).le) _
  by_cases hS : S.Nonempty
  · have hkill (r : ℕ) :
        uniformProbability (fun Q : ProperClause (n - 1) r => KillsSolutions S Q) =
          killFraction (forcedVariables S).card (n - 1) r := by
      unfold killFraction
      rw [← killingProbability_of_nonempty S hS]
      exact (uniformProbability_congr (fun _ => by simp [hS])).symm
    rw [hkill]
    apply le_trans _ (blockUNSAT_lower hkn S)
    rw [hkill]
    have hb : (forcedVariables S).card ≤ n - 1 := by
      simpa using Finset.card_le_univ (forcedVariables S)
    have hg : 2 * ((k - 1 : ℕ) + 1 : ℝ) * replacementScale n k ≤
        (replacementBlock n k : ℝ) := by
      have he : ((k - 1 : ℕ) : ℝ) + 1 = k := by
        exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ k))
      rw [he]
      exact Nat.le_ceil _
    have hsmall : 1 / ((n - 1 : ℕ) + 1 : ℝ) ≤ (replacementScale n k)⁻¹ ^ (k - 1) := by
      have he : ((n - 1 : ℕ) : ℝ) + 1 = n := by
        exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ n))
      rw [he]
      exact replacementError_small (by omega) (by omega)
    have hrep := replacement_numeric (r := k - 1) (b := (forcedVariables S).card)
      (v := n - 1) (g := replacementBlock n k) (a := replacementScale n k)
      (by omega) (by omega) hb (replacementScale_pos (by omega)) hsmall hg
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k), replacementError] using hrep
  · have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    have hb : blockUNSATProbability k (replacementBlock n k)
        (∅ : Finset (Assignment (n - 1))) = 1 := by
      unfold blockUNSATProbability
      have hf : (fun F : Formula (n - 1) k (replacementBlock n k) =>
          ¬ ∃ σ ∈ (∅ : Finset (Assignment (n - 1))), Satisfies σ F) =
          (fun _ => True) := by
        funext F
        simp
      rw [hf]
      exact uniformProbability_true
    rw [hb]
    have hu := uniformProbability_le_one
      (fun Q : ProperClause (n - 1) (k - 1) => KillsSolutions ∅ Q)
    linarith

end


end FixedClauseThreshold

end OAI
