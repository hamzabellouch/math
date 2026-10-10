import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

noncomputable section
open Filter Finset
open scoped Topology BigOperators

namespace Percolation.BenjaminiSchramm

lemma geometric_continuation_cost_bound (g : ℕ → ℝ) (C q : ℝ)
    (hg : ∀ l, 0 ≤ g l) (_hC : 0 ≤ C) (hb : ∀ l, g l ≤ C)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    Summable (fun l => g l*q^(l-n)) ∧
      0 ≤ (∑' l, g l*q^(l-n)) ∧
      (∑' l, g l*q^(l-n)) ≤ (∑ l ∈ range n, g l)+C*(1-q)⁻¹ := by
  have hsgeom := summable_geometric_of_lt_one hq0 hq1
  have htail : Summable (fun k => g (k+n)*q^k) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (hg _) (pow_nonneg hq0 _))
      (fun k => mul_le_mul_of_nonneg_right (hb _) (pow_nonneg hq0 _)) (hsgeom.mul_left C)
  have hs : Summable (fun l => g l*q^(l-n)) := by
    apply (summable_nat_add_iff n).mp
    simpa only [Nat.add_sub_cancel] using htail
  refine ⟨hs,tsum_nonneg (fun l => mul_nonneg (hg _) (pow_nonneg hq0 _)),?_⟩
  have hhead : (∑ l ∈ range n, g l*q^(l-n)) = ∑ l ∈ range n, g l := by
    apply sum_congr rfl
    intro l hl
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt (mem_range.mp hl)),pow_zero,mul_one]
  calc
    _ = (∑ l ∈ range n, g l*q^(l-n))+(∑' k, g (k+n)*q^k) := by
      simpa only [Nat.add_sub_cancel] using (hs.sum_add_tsum_nat_add n).symm
    _ ≤ (∑ l ∈ range n, g l)+∑' k, C*q^k := by
      rw [hhead]
      exact add_le_add le_rfl (htail.tsum_le_tsum
        (fun k => mul_le_mul_of_nonneg_right (hb _) (pow_nonneg hq0 _))
        (hsgeom.mul_left C))
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq1]

theorem geometric_continuation_cost_sublinear (g : ℕ → ℝ) (C q : ℝ)
    (hg : ∀ l, 0 ≤ g l) (hC : 0 ≤ C) (hb : ∀ l, g l ≤ C)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hlim : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (∑' l, g l*q^(l-n))/(n : ℝ)) atTop (𝓝 0) := by
  have hces : Tendsto (fun n : ℕ => (∑ l ∈ range n, g l)/(n : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_comm] using hlim.cesaro
  have hconst : Tendsto (fun n : ℕ => (C*(1-q)⁻¹)/(n : ℝ)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun n : ℕ =>
      ((∑ l ∈ range n, g l)+C*(1-q)⁻¹)/(n : ℝ)) atTop (𝓝 0) := by
    simpa only [add_div,zero_add] using hces.add hconst
  apply squeeze_zero (fun n => div_nonneg
    (geometric_continuation_cost_bound g C q hg hC hb hq0 hq1 n).2.1 (Nat.cast_nonneg n))
    (fun n => div_le_div_of_nonneg_right
      (geometric_continuation_cost_bound g C q hg hC hb hq0 hq1 n).2.2 (Nat.cast_nonneg n)) hupper

lemma exponential_continuation_weight (a : ℝ) (l n : ℕ) :
    Real.exp (-a*max ((l : ℝ)-n) 0) = Real.exp (-a)^(l-n) := by
  by_cases hn : n ≤ l
  · rw [max_eq_left (sub_nonneg.mpr (Nat.cast_le.mpr hn)),←Real.exp_nat_mul,
      Nat.cast_sub hn]
    congr 1
    ring
  · have hln : l ≤ n := Nat.le_of_lt (Nat.lt_of_not_ge hn)
    rw [max_eq_right (sub_nonpos.mpr (Nat.cast_le.mpr hln)),mul_zero,Real.exp_zero,
      Nat.sub_eq_zero_of_le hln,pow_zero]

theorem exponential_continuation_cost_sublinear (g : ℕ → ℝ) (C a : ℝ)
    (hg : ∀ l, 0 ≤ g l) (hC : 0 ≤ C) (hb : ∀ l, g l ≤ C)
    (ha : 0 < a) (hlim : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      (∑' l, g l*Real.exp (-a*max ((l : ℝ)-n) 0))/(n : ℝ)) atTop (𝓝 0) := by
  simp_rw [exponential_continuation_weight]
  exact geometric_continuation_cost_sublinear g C (Real.exp (-a)) hg hC hb
    (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)) hlim

end Percolation.BenjaminiSchramm

end

end OAI
