import OAI.Combinatorics.BalancedRyser.Probability.RescaledDrift
import OAI.Combinatorics.BalancedRyser.Selection.SelectionProcess
import OAI.Combinatorics.BalancedRyser.Selection.SelectionScales

namespace OAI

namespace Balanced.Selection.Process.Parameters

noncomputable section

variable {p : Parameters}

theorem Pstar_pos (hp : p.Admissible) : 0 < p.Pstar := by
  have hc := hp.1
  have hC := hp.2.1
  unfold Pstar
  positivity

theorem a_bounds (hp : p.Admissible) : 0 < p.a ∧ p.a < 1 := by
  exact ⟨hp.2.2.2.2.1, lt_of_lt_of_le hp.2.2.2.2.2 (min_le_left _ _)⟩

theorem tailSlots_le_order (hp : p.Admissible) (q : ℕ) : p.tailSlots q ≤ q := by
  unfold tailSlots
  apply Nat.ceil_le.mpr
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  nlinarith [(a_bounds hp).2]

theorem remaining_ge (hp : p.Admissible) {q n t : ℕ} (hqn : q ≤ n)
    (ht : t ≤ p.lastMainTime q n) : p.a * q ≤ ((n - t : ℕ) : ℝ) := by
  have htail : p.tailSlots q ≤ n := (tailSlots_le_order hp q).trans hqn
  have hrem : p.tailSlots q ≤ n - t := by
    unfold lastMainTime at ht
    omega
  exact (Nat.le_ceil (p.a * q)).trans (by exact_mod_cast hrem)

theorem source_scale_bounds (hp : p.Admissible) {q n t : ℕ}
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q) (hn : n = 2 * (q + 1))
    (ht : t ≤ p.lastMainTime q n) :
    p.smin ≤ p.sizeScale q t ∧ p.sizeScale q t ≤ 1 ∧
      p.smin * p.a / 3 ≤ p.degreeScale q n t ∧ p.degreeScale q n t ≤ 1 := by
  have hqpos : 0 < q := by omega
  have hnpos : 0 < n := by omega
  have hnq : n ≤ 3 * q := by omega
  have hqn : q ≤ n := by omega
  have htn : t ≤ n := ht.trans (Nat.sub_le _ _)
  obtain ⟨hslo, hshi⟩ := SelectionScales.domain_bounds (Pstar_pos hp).le hqpos hPq
    (htn.trans hnq)
  obtain ⟨hblo, hbhi⟩ := SelectionScales.degree_bounds (Pstar_pos hp).le
    (a_bounds hp).1.le hqpos hnpos hPq hnq htn (remaining_ge hp hqn ht)
  exact ⟨hslo, hshi, hblo, hbhi⟩

theorem source_relative_changes (hp : p.Admissible) {q n t : ℕ}
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q) (hn : n = 2 * (q + 1))
    (ht : t + 1 ≤ p.lastMainTime q n) :
    |1 - p.sizeScale q (t + 1) / p.sizeScale q t| = p.Pstar / q ∧
    |1 - p.degreeScale q n (t + 1) / p.degreeScale q n t| ≤
      (p.Pstar + 1 / p.a) / q := by
  have hqpos : 0 < q := by omega
  have hqn : q ≤ n := by omega
  have htn : t < n := (Nat.lt_of_succ_le ht).trans_le (Nat.sub_le _ _)
  constructor
  · exact SelectionScales.domain_relative_change (Pstar_pos hp).le hqpos hPq
  · exact SelectionScales.degree_relative_change_le (Pstar_pos hp).le
      (a_bounds hp).1 hqpos hPq htn (remaining_ge hp hqn (by omega))

theorem source_size_increment_le (hp : p.Admissible) {q n t : ℕ}
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q) (hn : n = 2 * (q + 1))
    (ht : t + 1 ≤ p.lastMainTime q n) {x y L Q : ℝ}
    (hjump : |y - x| ≤ L) (hsize : |x| ≤ Q * q) :
    |y / p.sizeScale q (t + 1) - x / p.sizeScale q t| ≤
      (L + Q * p.Pstar) / p.smin := by
  have hs := (source_scale_bounds hp hq hPq hn ht).1
  have hrel := (source_relative_changes hp hq hPq hn ht).1.le
  have hbound := Balanced.abs_rescaled_increment_le hjump hsize hrel
    (Real.exp_pos (-6 * p.Pstar)) hs
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hnum : Q * (q : ℝ) * (p.Pstar / q) = Q * p.Pstar := by field_simp
  simpa only [hnum, smin] using hbound

theorem source_degree_increment_le (hp : p.Admissible) {q n t : ℕ}
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q) (hn : n = 2 * (q + 1))
    (ht : t + 1 ≤ p.lastMainTime q n) {x y L Q : ℝ}
    (hjump : |y - x| ≤ L) (hsize : |x| ≤ Q * q) :
    |y / p.degreeScale q n (t + 1) - x / p.degreeScale q n t| ≤
      (L + Q * (p.Pstar + 1 / p.a)) / (p.smin * p.a / 3) := by
  have hs := (source_scale_bounds hp hq hPq hn ht).2.2.1
  have hrel := (source_relative_changes hp hq hPq hn ht).2
  have hlo : 0 < p.smin * p.a / 3 := by
    have hsmin : 0 < p.smin := Real.exp_pos _
    have ha := (a_bounds hp).1
    positivity
  have hbound := Balanced.abs_rescaled_increment_le hjump hsize hrel hlo hs
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hnum : Q * (q : ℝ) * ((p.Pstar + 1 / p.a) / q) =
      Q * (p.Pstar + 1 / p.a) := by field_simp
  simpa only [hnum, SelectionScales.domain] using hbound

theorem exists_admissible (c C c₀ : ℝ)
    (hc : 0 < c) (hC : 0 < C) (hc₀ : 0 < c₀) (hc₀le : c₀ ≤ 1) :
    ∃ p : Parameters, p.c = c ∧ p.C = C ∧ p.c₀ = c₀ ∧ p.Admissible := by
  let p₀ : Parameters := ⟨c, C, c₀, 0⟩
  let m : ℝ := min 1 (min (p₀.rho / 2) (c / (100 * (C + 1))))
  have hrho : 0 < p₀.rho := by
    change 0 < c₀ * Real.exp (-6 * p₀.Bstar) / 4
    positivity
  have hm : 0 < m := by
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  refine ⟨⟨c, C, c₀, m / 2⟩, rfl, rfl, rfl, ?_⟩
  change 0 < c ∧ 0 < C ∧ 0 < c₀ ∧ c₀ ≤ 1 ∧ 0 < m / 2 ∧ m / 2 < m
  exact ⟨hc, hC, hc₀, hc₀le, by linarith, by linarith⟩

theorem eventually_scale_regime (p : Parameters) :
    ∀ᶠ q : ℕ in Filter.atTop, 2 ≤ q ∧ 2 * p.Pstar ≤ q := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * p.Pstar)
  apply Filter.eventually_atTop.mpr
  refine ⟨max 2 N, fun q hq => ?_⟩
  constructor
  · exact (le_max_left _ _).trans hq
  · have hNq : N ≤ q := (le_max_right _ _).trans hq
    exact hN.trans (by exact_mod_cast hNq)

theorem Bstar_pos (hp : p.Admissible) : 0 < p.Bstar := by
  exact div_pos (by norm_num) (mul_pos (Real.exp_pos _) hp.1)

theorem rho_pos (hp : p.Admissible) : 0 < p.rho := by
  exact div_pos (mul_pos hp.2.2.1 (Real.exp_pos _)) (by norm_num)

theorem occupancy_scale_bounds (hp : p.Admissible) {q t : ℕ}
    (hq : 0 < q) (hBq : 2 * p.Bstar ≤ q) (ht : t ≤ 3 * q) :
    Real.exp (-6 * p.Bstar) ≤ (1 - p.Bstar / q) ^ t ∧
      (1 - p.Bstar / q) ^ t ≤ 1 :=
  SelectionScales.domain_bounds (Bstar_pos hp).le hq hBq ht

theorem occupancy_rescaled_increment_le (hp : p.Admissible) {q t : ℕ}
    (hq : 0 < q) (hBq : 2 * p.Bstar ≤ q) (ht : t + 1 ≤ 3 * q)
    {x y : ℝ} (hjump : |y - x| ≤ 1) (hsize : |x| ≤ q) :
    |y / ((1 - p.Bstar / q) ^ (t + 1)) - x / ((1 - p.Bstar / q) ^ t)| ≤
      (1 + p.Bstar) / Real.exp (-6 * p.Bstar) := by
  have hs := (occupancy_scale_bounds hp hq hBq ht).1
  have hrel := (SelectionScales.domain_relative_change (t := t)
    (Bstar_pos hp).le hq hBq).le
  have hbound := Balanced.abs_rescaled_increment_le hjump hsize hrel (Real.exp_pos _) hs
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have hnum : (q : ℝ) * (p.Bstar / q) = p.Bstar := by field_simp
  simpa only [hnum, SelectionScales.domain] using hbound

theorem tailSlots_le_rho_mul (hp : p.Admissible) {q : ℕ}
    (hq : 2 ≤ p.rho * q) : ((p.tailSlots q : ℕ) : ℝ) ≤ p.rho * q := by
  have ha : 0 < p.a := (a_bounds hp).1
  have harho : p.a < p.rho / 2 := (lt_min_iff.mp (lt_min_iff.mp hp.2.2.2.2.2).2).1
  have hceil := Nat.ceil_lt_add_one (mul_nonneg ha.le (Nat.cast_nonneg q))
  have hmul := mul_le_mul_of_nonneg_right harho.le (Nat.cast_nonneg q)
  change (Nat.ceil (p.a * q) : ℝ) ≤ p.rho * q
  nlinarith

theorem occupancy_after_tail (hp : p.Admissible) {q : ℕ} {x y : ℝ}
    (hq : 2 ≤ p.rho * q) (hmain : 2 * p.rho * q ≤ x)
    (hloss : x - p.tailSlots q ≤ y) : p.rho * q ≤ y := by
  have htail := tailSlots_le_rho_mul hp hq
  linarith

theorem eventually_occupancy_regime (hp : p.Admissible) :
    ∀ᶠ q : ℕ in Filter.atTop, 0 < q ∧ 2 * p.Bstar ≤ q ∧ 2 ≤ p.rho * q := by
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge (2 * p.Bstar)
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (2 / p.rho)
  apply Filter.eventually_atTop.mpr
  refine ⟨max 1 (max N₁ N₂), fun q hq => ?_⟩
  have hqone : 1 ≤ q := (le_max_left _ _).trans hq
  have h₁ : N₁ ≤ q := (le_max_left N₁ N₂).trans ((le_max_right _ _).trans hq)
  have h₂ : N₂ ≤ q := (le_max_right N₁ N₂).trans ((le_max_right _ _).trans hq)
  refine ⟨hqone, hN₁.trans (by exact_mod_cast h₁), ?_⟩
  have hdiv : 2 / p.rho ≤ (q : ℝ) := hN₂.trans (by exact_mod_cast h₂)
  have hmul := (div_le_iff₀ (rho_pos hp)).1 hdiv
  simpa only [mul_comm] using hmul

end
end Balanced.Selection.Process.Parameters

end OAI
