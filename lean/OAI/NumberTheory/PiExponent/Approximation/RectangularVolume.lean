import Mathlib

namespace OAI

open scoped BigOperators

namespace PiExponent

noncomputable def rectangularCutoff {k : ℕ} (κ : Fin k → ℝ) (T : ℝ) (i : Fin k) : ℕ :=
  ⌈T / ((k : ℝ) * κ i)⌉₊

theorem rectangularCutoff_pos {k : ℕ} (hk : 0 < k) (κ : Fin k → ℝ)
    (hκ : ∀ i, 0 < κ i) {T : ℝ} (hT : 0 < T) (i : Fin k) :
    0 < rectangularCutoff κ T i := by
  apply Nat.lt_ceil.mpr
  simpa only [Nat.cast_zero] using
    div_pos hT (mul_pos (by exact_mod_cast hk) (hκ i))

theorem two_le_rectangularCutoff {k : ℕ} (hk : 0 < k) (κ : Fin k → ℝ)
    (hκ : ∀ i, 0 < κ i) {T : ℝ} (i : Fin k)
    (hT : (k : ℝ) * κ i < T) :
    2 ≤ rectangularCutoff κ T i := by
  have hd : 0 < (k : ℝ) * κ i :=
    mul_pos (by exact_mod_cast hk) (hκ i)
  have h : (1 : ℝ) < T / ((k : ℝ) * κ i) :=
    (lt_div_iff₀ hd).mpr (by simpa using hT)
  exact Nat.lt_ceil.mpr (by simpa using h)

theorem eventually_two_le_rectangularCutoff {k : ℕ} (hk : 0 < k)
    (κ : Fin k → ℝ) (hκ : ∀ i, 0 < κ i) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℝ in Filter.atTop, ∀ i, 2 ≤ rectangularCutoff κ (ε * N) i := by
  have ht : Filter.Tendsto (fun N : ℝ => ε * N) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop hε
  apply Filter.eventually_all.mpr
  intro i
  filter_upwards [ht.eventually (Filter.eventually_gt_atTop ((k : ℝ) * κ i))] with N hN
  exact two_le_rectangularCutoff hk κ hκ i hN

theorem rectangularCutoff_coordinate_weight_lt {k : ℕ} (hk : 0 < k)
    (κ : Fin k → ℝ) (hκ : ∀ i, 0 < κ i) {T : ℝ}
    (β : Fin k → ℕ) (hβ : ∀ i, β i < rectangularCutoff κ T i) (i : Fin k) :
    κ i * (β i : ℝ) < T / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hb : (β i : ℝ) < T / ((k : ℝ) * κ i) := Nat.lt_ceil.mp (hβ i)
  have h := mul_lt_mul_of_pos_left hb (hκ i)
  have he : κ i * (T / ((k : ℝ) * κ i)) = T / (k : ℝ) := by
    field_simp [(hκ i).ne']
  simpa only [he] using h

theorem rectangularCutoff_weight_lt {k : ℕ} (hk : 0 < k)
    (κ : Fin k → ℝ) (hκ : ∀ i, 0 < κ i) {T : ℝ}
    (β : Fin k → ℕ) (hβ : ∀ i, β i < rectangularCutoff κ T i) :
    (∑ i, κ i * (β i : ℝ)) < T := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsum : (∑ i, κ i * (β i : ℝ)) < ∑ _i : Fin k, T / (k : ℝ) := by
    apply Finset.sum_lt_sum
    · intro i hi
      exact (rectangularCutoff_coordinate_weight_lt hk κ hκ β hβ i).le
    · exact ⟨⟨0, hk⟩, Finset.mem_univ _,
        rectangularCutoff_coordinate_weight_lt hk κ hκ β hβ ⟨0, hk⟩⟩
  have he : (∑ _i : Fin k, T / (k : ℝ)) = T := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hkR.ne']
  simpa only [he] using hsum

theorem rectangularCutoff_product_lower {k : ℕ} (hk : 0 < k)
    (κ : Fin k → ℝ) (hκ : ∀ i, 0 < κ i) {T : ℝ} (hT : 0 < T) :
    T ^ k / ((k : ℝ) ^ k * ∏ i, κ i) ≤
      ∏ i, (rectangularCutoff κ T i : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hp : (∏ i, T / ((k : ℝ) * κ i)) ≤
      ∏ i, (rectangularCutoff κ T i : ℝ) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact (div_pos hT (mul_pos hkR (hκ i))).le
    · intro i hi
      exact Nat.le_ceil _
  simpa only [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] using hp

end PiExponent

end OAI
