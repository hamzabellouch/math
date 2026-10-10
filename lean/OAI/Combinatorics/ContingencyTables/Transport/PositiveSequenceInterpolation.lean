import OAI.Combinatorics.ContingencyTables.Transport.IntegerChildLogConcavity

namespace OAI

/-! # Finite log-concave interpolation for the terminal tree marginal

The scalar statement used in the contamination estimate follows from
the actual adjacent two-removal inequality. No continuous extension of
the integer marginal is assumed.
-/

namespace ContingencyTables

open scoped BigOperators

private lemma decreasing_increments_average (g : ℕ → ℝ) (N : ℕ)
    (hc : ∀ k, k+2 ≤ N → g k+g (k+2) ≤ 2*g (k+1))
    (n : ℕ) (hn : n+1 ≤ N) :
    (n:ℝ)*(g (n+1)-g n) ≤ g n-g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ha := ih (by omega)
    have hd : g (n+2)-g (n+1) ≤ g (n+1)-g n := by
      linarith [hc n (by omega)]
    have hm := mul_le_mul_of_nonneg_left hd
      (show (0:ℝ) ≤ (n:ℝ)+1 by positivity)
    push_cast at hm ⊢
    nlinarith

/-- A finite sequence with decreasing adjacent increments lies above
each secant joining its first point to a later point. -/
theorem discrete_secant (g : ℕ → ℝ) (N : ℕ)
    (hc : ∀ k, k+2 ≤ N → g k+g (k+2) ≤ 2*g (k+1))
    (n : ℕ) (hn : n ≤ N) (k : ℕ) (hk : k ≤ n) :
    (k:ℝ)*(g n-g 0) ≤ (n:ℝ)*(g k-g 0) := by
  induction n with
  | zero =>
    have hk0 : k=0 := by omega
    simp [hk0]
  | succ n ih =>
    by_cases hkn : k ≤ n
    · by_cases hn0 : n=0
      · have hk0 : k=0 := by omega
        simp [hk0]
      · have hi := ih (by omega) hkn
        have ha := decreasing_increments_average g N hc n (by omega)
        have hi' := mul_le_mul_of_nonneg_left hi
          (show (0:ℝ) ≤ (n:ℝ)+1 by positivity)
        have ha' := mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg k : (0:ℝ) ≤ k)
        have hnR : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
        push_cast at hi' ⊢
        nlinarith
    · have hke : k=n+1 := by omega
      simp only [hke]
      exact le_rfl

/-- Adjacent log-concavity gives the exact finite logarithmic secant
inequality used for each positive tree-coordinate marginal. -/
theorem positive_sequence_log_secant (a : ℕ → ℝ) (N : ℕ)
    (hp : ∀ k, k ≤ N → 0 < a k)
    (hc : ∀ k, k+2 ≤ N → a k*a (k+2) ≤ (a (k+1))^2)
    (k : ℕ) (hk : k ≤ N) :
    (k:ℝ)*(Real.log (a N)-Real.log (a 0)) ≤
      (N:ℝ)*(Real.log (a k)-Real.log (a 0)) := by
  apply discrete_secant (fun j => Real.log (a j)) N _ N le_rfl k hk
  intro j hj
  have h0 := hp j (by omega)
  have h1 := hp (j+1) (by omega)
  have h2 := hp (j+2) hj
  have hh := Real.log_le_log (mul_pos h0 h2) (hc j hj)
  rw [Real.log_mul h0.ne' h2.ne',Real.log_pow] at hh
  simpa only [Nat.cast_ofNat] using hh

/-- A positive log-concave sequence whose far endpoint has mass at
least one and whose first mass is at most 2^K loses at most a factor
two over the first N/K integer positions. -/
theorem positive_sequence_half_window (a : ℕ → ℝ) (N K : ℕ)
    (hK : 1 ≤ K) (hN : 0 < N)
    (hp : ∀ k, k ≤ N → 0 < a k)
    (hc : ∀ k, k+2 ≤ N → a k*a (k+2) ≤ (a (k+1))^2)
    (hend : 1 ≤ a N) (hfirst : a 0 ≤ (2:ℝ)^K)
    (r : ℕ) (hr : r*K ≤ N) : a 0/2 ≤ a r := by
  have hrN : r ≤ N := by nlinarith
  have h0 := hp 0 (Nat.zero_le N)
  have hr0 := hp r hrN
  have hlog := positive_sequence_log_secant a N hp hc r hrN
  have hlogend : 0 ≤ Real.log (a N) := Real.log_nonneg hend
  have hlogfirst : Real.log (a 0) ≤ (K:ℝ)*Real.log 2 := by
    have hh := Real.log_le_log h0 hfirst
    simpa only [Real.log_pow] using hh
  have htwo : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hrK : (r:ℝ)*K ≤ N := by exact_mod_cast hr
  have hrR : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hm := mul_le_mul_of_nonneg_left hlogfirst hrR
  have hsum := mul_le_mul_of_nonneg_right hrK htwo
  have hloghalf : Real.log (a 0)-Real.log 2 ≤ Real.log (a r) := by
    nlinarith [mul_nonneg hrR hlogend]
  rw [← Real.log_div h0.ne' (by norm_num : (2:ℝ) ≠ 0)] at hloghalf
  exact (Real.log_le_log_iff (div_pos h0 (by norm_num)) hr0).mp hloghalf

/-- A half-height interpolation window contains enough distinct integer
positions to give the source's normalized exterior point-mass bound. -/
theorem half_window_mass_bound (a : ℕ → ℝ) (U k N K b : ℕ)
    (hK : 0 < K) (hb : 0 < b) (hbN : b ≤ N) (hkN : k+N ≤ U)
    (ha : ∀ j,j ≤ U → 0 ≤ a j)
    (hC : 0 < ∑ j ∈ Finset.range (U+1),a j)
    (hwindow : ∀ r,r*K ≤ N → a k/2 ≤ a (k+r)) :
    a k/(∑ j ∈ Finset.range (U+1),a j) ≤ (2*K:ℝ)/b := by
  let q := N/K+1
  have hkU : k ≤ U := by omega
  have hak : 0 ≤ a k := ha k hkU
  have hsubset : (Finset.range q).image (fun r => k+r) ⊆ Finset.range (U+1) := by
    intro j hj
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hj
    have hrq : r ≤ N/K := by have := Finset.mem_range.mp hr; dsimp only [q] at this; omega
    have hrN : r ≤ N := hrq.trans (Nat.div_le_self _ _)
    exact Finset.mem_range.mpr (by omega)
  have hsum : (∑ r ∈ Finset.range q,a (k+r)) ≤ ∑ j ∈ Finset.range (U+1),a j := by
    rw [← Finset.sum_image (fun r _ s _ hrs => Nat.add_left_cancel hrs)]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun j hj _ => ha j (by have := Finset.mem_range.mp hj; omega))
  have hheight : (q:ℝ)*(a k/2) ≤ ∑ r ∈ Finset.range q,a (k+r) := by
    calc
      _ = ∑ _r ∈ Finset.range q,a k/2 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro r hr
        apply hwindow
        have hrq : r ≤ N/K := by have := Finset.mem_range.mp hr; dsimp only [q] at this; omega
        exact (Nat.mul_le_mul_right K hrq).trans (Nat.div_mul_le_self _ _)
  have hcountNat : b ≤ K*q := hbN.trans (Nat.lt_mul_div_succ N hK).le
  have hcount : (b:ℝ) ≤ (K:ℝ)*(q:ℝ) := by exact_mod_cast hcountNat
  have hmass := hheight.trans hsum
  have hm1 := mul_le_mul_of_nonneg_right hcount (div_nonneg hak (by norm_num : (0:ℝ) ≤ 2))
  have hm2 := mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg K : (0:ℝ) ≤ K)
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  rw [div_le_div_iff₀ hC hbR]
  nlinarith

end ContingencyTables

end OAI
