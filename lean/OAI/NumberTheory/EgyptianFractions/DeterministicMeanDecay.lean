import OAI.NumberTheory.EgyptianFractions.ResidueLevels

namespace OAI
noncomputable section
open Filter

namespace Problem337.ResidueLevels

/-- The exponential absorption used in the deterministic second moment is
uniform in every real prime-product scale in the standard interval. -/
theorem eventually_exp_absorb_real_scale {a b c C : ℝ}
    (hab : a < b) (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠ S : ℝ in atTop, ∀ m : ℝ,
      S / (2 * Real.log S) ≤ m → m ≤ S / Real.log S →
      Real.exp (-b * m) + C * Real.exp (-c * S) ≤ Real.exp (-a * m) := by
  have ht : Tendsto (fun S : ℝ => S / (2 * Real.log S)) atTop atTop := by
    convert tendsto_div_log.atTop_div_const (by norm_num : (0 : ℝ) < 2) using 1
    funext S
    ring
  have ht₁ : Tendsto
      (fun S : ℝ => Real.exp (-((b - a) * (S / (2 * Real.log S)))))
      atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (ht.const_mul_atTop (sub_pos.mpr hab))
  have ht₂ : Tendsto
      (fun S : ℝ => C * Real.exp (-(S / (2 * Real.log S))))
      atTop (nhds 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul C
  have hsmall : ∀ᶠ S : ℝ in atTop,
      Real.exp (-((b - a) * (S / (2 * Real.log S)))) +
        C * Real.exp (-(S / (2 * Real.log S))) ≤ 1 := by
    apply Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1)
    simpa using ht₁.add ht₂
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop ((a + 1) / c))] with S hs hS hlog
  intro m hmlo hmhi
  have hSp : 0 < S := by linarith
  have hlogp : 0 < Real.log S := Real.log_pos hS
  have hmp : 0 < m := (div_pos hSp (by positivity)).trans_le hmlo
  have hlogm : Real.log S * m ≤ S := by
    have hh := (le_div_iff₀ hlogp).1 hmhi
    nlinarith
  have hcm : (a + 1) * m ≤ c * S := by
    have hh := (div_le_iff₀ hc).1 hlog
    nlinarith [mul_le_mul_of_nonneg_right hh hmp.le,
      mul_le_mul_of_nonneg_left hlogm hc.le]
  have hsmallm : Real.exp (-((b - a) * m)) + C * Real.exp (-m) ≤ 1 := by
    apply le_trans _ hs
    apply add_le_add
    · apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hmlo (sub_pos.mpr hab).le]
    · apply mul_le_mul_of_nonneg_left _ hC
      exact Real.exp_le_exp.mpr (neg_le_neg hmlo)
  have hexp : Real.exp (-c * S) ≤ Real.exp (-(a + 1) * m) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc
    Real.exp (-b * m) + C * Real.exp (-c * S) ≤
        Real.exp (-b * m) + C * Real.exp (-(a + 1) * m) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hexp hC)
    _ = Real.exp (-a * m) *
        (Real.exp (-((b - a) * m)) + C * Real.exp (-m)) := by
      rw [mul_add, ← Real.exp_add]
      have heq : -a * m + -((b - a) * m) = -b * m := by ring
      rw [heq]
      congr 1
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-a * m) := by
      simpa using mul_le_mul_of_nonneg_left hsmallm (Real.exp_pos _).le

/-- A diagonal term controlled by an exponential list cardinality and a
uniform off-diagonal power saving give the precise deterministic mean rate.
The threshold is independent of the list, cutoff, and real scale `m`. -/
theorem eventually_deterministic_mean_real_scale {A δ : ℝ}
    (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∀ᶠ S : ℝ in atTop, ∀ m N X : ℝ,
      S / (2 * Real.log S) ≤ m → m ≤ S / Real.log S →
      Real.exp (m * Real.log 2) ≤ N → 0 ≤ X →
      X / N + 2 * A * X * Real.exp (-(4 * δ * S / 5)) ≤
        X * Real.exp (-m / 100) := by
  have hlog : (1 / 100 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  filter_upwards [eventually_exp_absorb_real_scale
    (a := 1 / 100) (b := Real.log 2) (c := 4 * δ / 5) (C := 2 * A)
    hlog (by positivity) (by positivity)] with S hS
  intro m N X hmlo hmhi hN hX
  have hdiag : X / N ≤ X * Real.exp (-Real.log 2 * m) := by
    calc
      X / N ≤ X / Real.exp (m * Real.log 2) :=
        div_le_div_of_nonneg_left hX (Real.exp_pos _) hN
      _ = X * Real.exp (-Real.log 2 * m) := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
        congr 2
        ring
  have hbound := mul_le_mul_of_nonneg_left (hS m hmlo hmhi) hX
  calc
    X / N + 2 * A * X * Real.exp (-(4 * δ * S / 5)) ≤
        X * Real.exp (-Real.log 2 * m) +
          2 * A * X * Real.exp (-(4 * δ * S / 5)) :=
      add_le_add hdiag (le_refl _)
    _ ≤ X * Real.exp (-m / 100) := by
      have he : -(4 * δ * S / 5) = -(4 * δ / 5) * S := by ring
      have hf : -m / 100 = -(1 / 100 : ℝ) * m := by ring
      rw [he, hf]
      nlinarith

end Problem337.ResidueLevels

end

end OAI
