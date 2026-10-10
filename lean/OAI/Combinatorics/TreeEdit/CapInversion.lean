import OAI.Combinatorics.TreeEdit.Model

namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

lemma sqrt_log_cap {A k d : ℝ} (hA : 1 ≤ A) (hk : 8 * A ≤ k) (hd : 1 < d)
    (hcap : Real.log d ≤ A * (k + 1) ^ 2 * Real.log (k + 1)) :
    Real.sqrt (Real.log d * Real.log (Real.log d)) ≤ 8 * A * (k * Real.log k) := by
  have hk2 : 2 ≤ k := by linarith
  have hkp : 0 < k := by linarith
  have hAp : 0 < A := by linarith
  have hlogk : 0 < Real.log k := Real.log_pos (by linarith)
  have hlogd : 0 < Real.log d := Real.log_pos hd
  have hlk : Real.log (k + 1) ≤ 2 * Real.log k := by
    calc
      _ ≤ Real.log (2 * k) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + Real.log k := Real.log_mul (by norm_num) (by positivity)
      _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hk2]
  have hlk0 : 0 ≤ Real.log (k + 1) := Real.log_nonneg (by linarith)
  have hL : Real.log d ≤ 8 * A * k ^ 2 * Real.log k := by
    calc
      _ ≤ A * (k + 1) ^ 2 * Real.log (k + 1) := hcap
      _ ≤ A * (2 * k) ^ 2 * (2 * Real.log k) := by gcongr; linarith
      _ = _ := by ring
  have hll : Real.log (Real.log d) ≤ 4 * Real.log k := by
    calc
      _ ≤ Real.log (8 * A * k ^ 2 * Real.log k) := Real.log_le_log hlogd hL
      _ = Real.log (8 * A) + 2 * Real.log k + Real.log (Real.log k) := by
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity), Real.log_pow]
        ring
      _ ≤ Real.log k + 2 * Real.log k + Real.log k := by
        have ha := Real.log_le_log (by positivity : (0 : ℝ) < 8 * A) hk
        have hb := Real.log_le_log hlogk (show Real.log k ≤ k from by linarith [Real.log_le_sub_one_of_pos hkp])
        linarith
      _ = _ := by ring
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hh : Real.log d * Real.log (Real.log d) ≤
        (8 * A * k ^ 2 * Real.log k) * (4 * Real.log k) := by
      exact (mul_le_mul_of_nonneg_left hll hlogd.le).trans
        (mul_le_mul_of_nonneg_right hL (by positivity))
    have hAA : 32 * A ≤ (8 * A) ^ 2 := by nlinarith
    calc
      _ ≤ _ := hh
      _ = (32 * A) * (k * Real.log k) ^ 2 := by ring
      _ ≤ (8 * A) ^ 2 * (k * Real.log k) ^ 2 := mul_le_mul_of_nonneg_right hAA (sq_nonneg _)
      _ = _ := by ring

lemma near_cap {N : ℕ → ℕ} {k₀ d : ℕ} (hN : ∀ k, k₀ ≤ k → k ≤ N k)
    (hd : N k₀ ≤ d) : ∃ k, k₀ ≤ k ∧ N k ≤ d ∧ d < N (k + 1) := by
  classical
  have hex : ∃ t : ℕ, d < N (k₀ + t) := by
    refine ⟨d + 1, ?_⟩
    exact (by omega : d < k₀ + (d + 1)).trans_le (hN _ (by omega))
  let t := Nat.find hex
  have ht : d < N (k₀ + t) := Nat.find_spec hex
  have ht0 : 0 < t := by
    by_contra hn
    have he : t = 0 := by omega
    simp only [he, add_zero] at ht
    omega
  refine ⟨k₀ + (t - 1), by omega, ?_, ?_⟩
  · have hh := Nat.find_min hex (show t - 1 < Nat.find hex by dsimp [t] at ht0 ⊢; omega)
    exact Nat.le_of_not_gt hh
  · convert ht using 1
    congr 1
    omega

theorem all_caps_of_witnesses {N : ℕ → ℕ} {A : ℝ} (hA : 1 ≤ A)
    (h : ∀ᶠ k : ℕ in Filter.atTop,
      k ≤ N k ∧ Real.log (N k : ℝ) ≤ A * (k : ℝ) ^ 2 * Real.log k ∧
      ∃ W : Finset (List Bool), 2 ≤ W.card ∧ (∀ w ∈ W, w.length = N k) ∧
        Real.exp ((k : ℝ) * Real.log k / 2) ≤ c1 W) : BinaryLowerBound := by
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp h
  let K := max k₀ ⌈8 * A⌉₊ + 2
  have hK0 : k₀ ≤ K := by dsimp [K]; omega
  have hK2 : 2 ≤ K := by dsimp [K]; omega
  have hKA : 8 * A ≤ (K : ℝ) := by
    exact (Nat.le_ceil (8 * A)).trans (by exact_mod_cast (show ⌈8 * A⌉₊ ≤ K by dsimp [K]; omega))
  refine ⟨1 / (16 * A), by positivity, N K, ?_⟩
  intro d hd
  have hdr : 1 < (d : ℝ) := by
    have hKd : K ≤ d := (hk₀ K hK0).1.trans hd
    exact_mod_cast (by omega : 1 < d)
  obtain ⟨k, hkK, hkd, hdk⟩ := near_cap (k₀ := K)
    (fun j hj => (hk₀ j (hK0.trans hj)).1) hd
  obtain ⟨hNk, hlogk, W, hW, hlen, hdist⟩ := hk₀ k (hK0.trans hkK)
  have hlog : Real.log (d : ℝ) ≤ A * ((k : ℝ) + 1) ^ 2 * Real.log ((k : ℝ) + 1) := by
    calc
      _ ≤ Real.log (N (k + 1) : ℝ) := Real.log_le_log (by positivity) (by exact_mod_cast hdk.le)
      _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_one] using (hk₀ (k + 1) (by omega)).2.1
  have hb := sqrt_log_cap hA (hKA.trans (by exact_mod_cast hkK)) hdr hlog
  have hexp : Real.exp ((1 / (16 * A)) * Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ)))) ≤
      Real.exp ((k : ℝ) * Real.log k / 2) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ (1 / (16 * A)) * (8 * A * ((k : ℝ) * Real.log k)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by field_simp; ring
  exact ⟨N k, hkd, W, hW, hlen, hexp.trans hdist⟩

lemma eventually_exponential_lower {b C : ℝ} (hb : 1 ≤ b) (hC : 1 ≤ C) (r : ℕ) :
    ∀ᶠ k : ℕ in Filter.atTop,
      Real.exp ((k : ℝ) * Real.log k / 2) ≤ ((k : ℝ) / b) ^ k / (C * (k : ℝ) ^ r) := by
  have ht : Filter.Tendsto (fun k : ℕ => Real.log (k : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop (4 * (Real.log b + Real.log C)),
    Filter.eventually_ge_atTop (max 2 (4 * r))] with k hl hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hkr : 4 * (r : ℝ) ≤ k := by exact_mod_cast (by omega : 4 * r ≤ k)
  have hl0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
  have hbpos : 0 < b := by linarith
  have hCpos : 0 < C := by linarith
  have hlC : 0 ≤ Real.log C := Real.log_nonneg hC
  rw [← Real.exp_log (by positivity : 0 < ((k : ℝ) / b) ^ k / (C * (k : ℝ) ^ r))]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow,
    Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hh1 := mul_le_mul_of_nonneg_left hl hkpos.le
  have hh2 := mul_le_mul_of_nonneg_right hkr hl0
  have hh3 := mul_le_mul_of_nonneg_right hk1 hlC
  nlinarith

end TreeEdit

end OAI
