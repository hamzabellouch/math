import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Positivity

namespace OAI

namespace SharpPlanar
open Finset

noncomputable def bernsteinWeight (d k : ℕ) (v : ℝ) : ℝ :=
  (d.choose k : ℝ) * v^k * (1-v)^(d-k)
noncomputable def powerToBernstein (d : ℕ) (T : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ r ∈ range (k+1), (k.choose r : ℝ) / (d.choose r : ℝ) * T r

lemma choose_ratio_identity {d k r : ℕ} (hr : r ≤ d) (hk : r ≤ k) :
    (k.choose r : ℝ) / (d.choose r : ℝ) * (d.choose k : ℝ) =
      ((d-r).choose (k-r) : ℝ) := by
  have hden : (d.choose r : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hr
  have he : (d.choose k : ℝ) * (k.choose r : ℝ) =
      (d.choose r : ℝ) * ((d-r).choose (k-r) : ℝ) := by
    exact_mod_cast Nat.choose_mul hk
  rw [div_mul_eq_mul_div,div_eq_iff hden]
  simpa [mul_comm] using he

lemma monomial_bernstein {d r : ℕ} (hr : r ≤ d) (v : ℝ) :
    (∑ k ∈ Ico r (d+1), (k.choose r : ℝ) / (d.choose r : ℝ) *
      bernsteinWeight d k v) = v^r := by
  rw [sum_Ico_eq_sum_range]
  have hs : d+1-r = d-r+1 := by omega
  rw [hs]
  trans v^r * (∑ k ∈ range (d-r+1), v^k * (1-v)^(d-r-k) * ((d-r).choose k : ℝ))
  · rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    have hrk : r+k-r = k := by omega
    have hsub : d-(r+k) = d-r-k := by omega
    unfold bernsteinWeight
    rw [← mul_assoc,← mul_assoc,choose_ratio_identity hr (Nat.le_add_right r k),hrk,hsub,pow_add]
    ring
  · rw [← add_pow]
    simp

lemma bernstein_identity (d : ℕ) (T : ℕ → ℝ) (v : ℝ) :
    (∑ r ∈ range (d+1), T r * v^r) =
      ∑ k ∈ range (d+1), powerToBernstein d T k * bernsteinWeight d k v := by
  unfold powerToBernstein
  simp_rw [sum_mul]
  have hswap := sum_Ico_Ico_comm 0 (d+1)
    (fun r k => (k.choose r : ℝ) / (d.choose r : ℝ) * T r * bernsteinWeight d k v)
  simp only [Nat.Ico_zero_eq_range] at hswap
  rw [← hswap]
  apply sum_congr rfl
  intro r hr
  have hrd : r ≤ d := by simpa only [mem_range,Nat.lt_succ_iff] using hr
  rw [← monomial_bernstein hrd v,mul_sum]
  apply sum_congr rfl
  intro k hk
  ring

lemma bernsteinWeight_nonneg {v : ℝ} (hv : v ∈ Set.Icc 0 1) (d k : ℕ) :
    0 ≤ bernsteinWeight d k v := by
  unfold bernsteinWeight
  have : 0 ≤ 1-v := sub_nonneg.mpr hv.2
  have hv0 : 0 ≤ v := hv.1
  positivity
lemma sum_bernsteinWeight (d : ℕ) (v : ℝ) :
    (∑ k ∈ range (d+1), bernsteinWeight d k v) = 1 := by
  have h := add_pow v (1-v) d
  simp only [add_sub_cancel,one_pow] at h
  rw [h]
  apply sum_congr rfl
  intro k hk
  unfold bernsteinWeight
  ring


lemma bernstein_lower {d : ℕ} {T : ℕ → ℝ} {a v : ℝ}
    (hv : v ∈ Set.Icc 0 1)
    (hB : ∀ k ∈ range (d+1), a ≤ powerToBernstein d T k) :
    a ≤ ∑ r ∈ range (d+1), T r * v^r := by
  rw [bernstein_identity]
  calc
    a = ∑ k ∈ range (d+1), a * bernsteinWeight d k v := by rw [← mul_sum,sum_bernsteinWeight,mul_one]
    _ ≤ _ := sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hB k hk) (bernsteinWeight_nonneg hv d k)

end SharpPlanar

end OAI
