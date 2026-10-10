import OAI.NumberTheory.TotientAsymptotic.PublishedConcentration

namespace OAI

/-! Comparing the truncated simplex centers with the retained coarse bands. -/

noncomputable section

namespace TotientAsymptotic

lemma truncated_center_ratio {m q i ε : ℝ} (hmq : q < m) (hq : 0 ≤ q)
    (hi : 0 ≤ i) (him : i ≤ m-q) (hε : 0 ≤ ε) (hsmall : q ≤ ε*(m-i)) :
    (1-ε)*(m-i)/m ≤ (m-q-i)/(m-q) ∧ (m-q-i)/(m-q) ≤ (m-i)/m := by
  have hm : 0 < m := lt_of_le_of_lt hq hmq
  have hmq' : 0 < m-q := sub_pos.mpr hmq
  have hmi : 0 ≤ m-i := by linarith
  have h1 := mul_le_mul_of_nonneg_right hsmall hi
  have h2 := mul_le_mul_of_nonneg_left him (mul_nonneg hε hmi)
  constructor
  · apply (div_le_div_iff₀ hm hmq').mpr
    nlinarith
  · apply (div_le_div_iff₀ hmq' hm).mpr
    nlinarith [mul_nonneg hq hi]

lemma truncated_center_close {m q i : ℕ} {S : ℝ} (hS : 0 ≤ S)
    (hqm : q < m) (hi : i ≤ m-q) (hq : 100*q ≤ m-i) :
    (99/100 : ℝ)*(S*((m-i : ℕ) : ℝ)/m) ≤ S*((m-q-i : ℕ) : ℝ)/(m-q : ℕ) ∧
      S*((m-q-i : ℕ) : ℝ)/(m-q : ℕ) ≤ S*((m-i : ℕ) : ℝ)/m := by
  have hqR : (q : ℝ) < m := by exact_mod_cast hqm
  have hiR : (i : ℝ) ≤ (m : ℝ)-q := by
    have hh : (i : ℝ)+(q : ℝ) ≤ m := by exact_mod_cast (show i+q ≤ m by omega)
    linarith
  have hsmall : (q : ℝ) ≤ (1/100 : ℝ)*((m : ℝ)-i) := by
    have hh : (100 : ℝ)*q ≤ (m : ℝ)-i := by
      have hn : 100*q+i ≤ m := by omega
      have hh : (100 : ℝ)*q+i ≤ m := by exact_mod_cast hn
      linarith
    linarith
  have hh := truncated_center_ratio hqR (Nat.cast_nonneg q) (Nat.cast_nonneg i) hiR
    (by norm_num : (0 : ℝ)≤1/100) hsmall
  have hmi : i ≤ m := by omega
  have hmqi : i ≤ m-q := hi
  rw [← Nat.cast_sub hmi, ← Nat.cast_sub (Nat.le_of_lt hqm),
    ← Nat.cast_sub hmqi] at hh
  constructor
  · have h := mul_le_mul_of_nonneg_left hh.1 hS
    convert h using 1 <;> ring
  · have h := mul_le_mul_of_nonneg_left hh.2 hS
    convert h using 1 <;> ring

lemma outside_band_implies_deviation {b c u : ℝ} (hb : 0 < b)
    (hlo : (98/100 : ℝ)*b ≤ c) (hhi : c ≤ (102/100 : ℝ)*b)
    (hu : u < (95/100 : ℝ)*b ∨ (105/100 : ℝ)*b < u) :
    (1/40 : ℝ) < |u/c-1| := by
  have hc : 0 < c := lt_of_lt_of_le (by positivity) hlo
  by_contra! hh
  have hh' := abs_le.mp hh
  have hl : (39/40 : ℝ)*c ≤ u := (le_div_iff₀ hc).mp (by linarith [hh'.1])
  have hr : u ≤ (41/40 : ℝ)*c := (div_le_iff₀ hc).mp (by linarith [hh'.2])
  rcases hu with hu | hu <;> nlinarith

end TotientAsymptotic

end

end OAI
