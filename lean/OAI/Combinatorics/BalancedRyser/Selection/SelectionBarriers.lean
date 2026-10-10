import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace OAI

open Filter Real
open scoped BigOperators Topology

namespace Balanced.SelectionBarriers

theorem finite_hazard_le {I : Type*} (R : Finset I) (L d : I → ℝ)
    {h m D : ℝ} (hh : 0 < h) (hm : 0 < m)
    (hL : ∀ i ∈ R, m ≤ L i) (hd : ∀ i ∈ R, 0 ≤ d i)
    (hD : ∑ i ∈ R, d i ≤ D) :
    (∑ i ∈ R, d i / L i) / h ≤ D / (h * m) := by
  have hsum : (∑ i ∈ R, d i / L i) ≤ (∑ i ∈ R, d i) / m := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun i hi ↦ div_le_div_of_nonneg_left (hd i hi) hm (hL i hi)
  calc
    _ ≤ ((∑ i ∈ R, d i) / m) / h := div_le_div_of_nonneg_right hsum hh.le
    _ ≤ (D / m) / h := div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right hD hm.le) hh.le
    _ = D / (h * m) := by ring

theorem domain_barrier {s smin c q e L L₀ : ℝ}
    (hs : smin ≤ s) (hc : 0 < c) (hq : 0 < q)
    (he : e ≤ smin * c * q / 2) (hL₀ : c * q ≤ L₀)
    (hL : |L - s * L₀| ≤ e) (hsmin : 0 < smin) :
    s * c * q / 2 ≤ L := by
  have hs0 : 0 ≤ s := hsmin.le.trans hs
  have hsc : s * (c * q) ≤ s * L₀ := mul_le_mul_of_nonneg_left hL₀ hs0
  have hscale : smin * c * q ≤ s * c * q :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hc.le) hq.le
  have hlow := (abs_le.mp hL).1
  nlinarith

theorem hazard_barrier_arithmetic {q n h s smin c C a e : ℝ}
    (hq : 0 < q) (hqn : q ≤ n) (ha : 0 < a) (hh : a * q ≤ h)
    (hsmin : 0 < smin) (hs : smin ≤ s) (hc : 0 < c) (hC : 0 ≤ C)
    (he₁ : e ≤ smin * c * q / 2) (he₂ : e ≤ a * smin * c * q) :
    (s * (h / n) * C * q + e) / (h * (s * c * q - e)) ≤
      (2 * C / c + 2) / q := by
  have hn : 0 < n := hq.trans_le hqn
  have hh0 : 0 < h := (mul_pos ha hq).trans_le hh
  have hs0 : 0 < s := hsmin.trans_le hs
  have hscq : 0 < s * c * q := mul_pos (mul_pos hs0 hc) hq
  have hscale : smin * c * q ≤ s * c * q :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hc.le) hq.le
  have hem : e ≤ s * c * q / 2 := he₁.trans (by linarith)
  have hm : 0 < s * c * q - e := by linarith
  have heh : e ≤ h * s * c := by
    calc
      e ≤ a * smin * c * q := he₂
      _ = (a * q) * smin * c := by ring
      _ ≤ h * smin * c := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hh hsmin.le) hc.le
      _ ≤ h * s * c := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs hh0.le) hc.le
  have hfrac : h / n * q ≤ h := by
    calc
      h / n * q = h * q / n := by ring
      _ ≤ h := (div_le_iff₀ hn).2 (mul_le_mul_of_nonneg_left hqn hh0.le)
  have hdeg : s * (h / n) * C * q ≤ s * h * C := by
    calc
      s * (h / n) * C * q = (s * C) * (h / n * q) := by ring
      _ ≤ (s * C) * h := mul_le_mul_of_nonneg_left hfrac (mul_nonneg hs0.le hC)
      _ = s * h * C := by ring
  have hcoef : 0 ≤ 2 * C / c + 2 := by positivity
  apply (div_le_iff₀ (mul_pos hh0 hm)).2
  have hbase : s * h * C + h * s * c ≤
      ((2 * C / c + 2) / q) * (h * (s * c * q - e)) := by
    have hlower : h * (s * c * q / 2) ≤ h * (s * c * q - e) :=
      mul_le_mul_of_nonneg_left (by linarith) hh0.le
    have hmul := mul_le_mul_of_nonneg_left hlower (div_nonneg hcoef hq.le)
    have hid : ((2 * C / c + 2) / q) * (h * (s * c * q / 2)) =
        s * h * C + h * s * c := by field_simp
    rw [hid] at hmul
    exact hmul
  nlinarith

theorem eventually_selection_error_le {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop, (q : ℝ) ^ ((4 : ℝ) / 5) ≤ δ * q := by
  have ht := (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 : ℝ) / 5)).comp
    tendsto_natCast_atTop_atTop
  have hb : ∀ᶠ q : ℕ in atTop, (q : ℝ) ^ (-((1 : ℝ) / 5)) < δ :=
    ht.eventually (gt_mem_nhds hδ)
  filter_upwards [hb, eventually_ge_atTop 1] with q hb hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hid : (q : ℝ) ^ ((4 : ℝ) / 5) =
      (q : ℝ) ^ (-((1 : ℝ) / 5)) * q := by
    calc
      _ = (q : ℝ) ^ (-((1 : ℝ) / 5) + 1) := by norm_num
      _ = _ := by rw [Real.rpow_add hq0, Real.rpow_one]
  rw [hid]
  exact mul_le_mul_of_nonneg_right hb.le hq0.le

theorem eventually_selection_error_budgets {a smin c : ℝ}
    (ha : 0 < a) (hsmin : 0 < smin) (hc : 0 < c) :
    ∀ᶠ q : ℕ in atTop,
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ smin * c * q / 2 ∧
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ a * smin * c * q := by
  have h₁ := eventually_selection_error_le (δ := smin * c / 2) (by positivity)
  have h₂ := eventually_selection_error_le (δ := a * smin * c) (by positivity)
  filter_upwards [h₁, h₂] with q h₁ h₂
  constructor
  · convert h₁ using 1; ring
  · exact h₂

end Balanced.SelectionBarriers

end OAI
