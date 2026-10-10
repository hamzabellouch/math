import Mathlib

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma three_choose_bound (h a b : ℕ) :
    (h+a+b).choose h * (a+b).choose a ≤ 3^(h+a+b) := by
  have hb := Nat.choose_le_two_pow (a+b) a
  have hh := Nat.mul_le_mul_left ((h+a+b).choose h) hb
  have ht := Finset.single_le_sum (s := Finset.range (h+a+b+1))
    (f := fun j => (1 : ℕ)^j*2^(h+a+b-j)*(h+a+b).choose j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (show h < h+a+b+1 by omega))
  have he : h+a+b-h = a+b := by omega
  have hsum : (∑ j ∈ Finset.range (h+a+b+1),
      (1 : ℕ)^j*2^(h+a+b-j)*(h+a+b).choose j) = 3^(h+a+b) := by
    simpa only [Nat.cast_id] using (add_pow (1 : ℕ) 2 (h+a+b)).symm
  rw [hsum,he] at ht
  exact hh.trans (by simpa only [one_pow,one_mul,Nat.mul_comm] using ht)

lemma three_factorial_bound (h a b : ℕ) :
    (h+a+b).factorial ≤ 3^(h+a+b) * (h.factorial*a.factorial*b.factorial) := by
  have hbc := Nat.choose_mul_factorial_mul_factorial (show a ≤ a+b by omega)
  have hha := Nat.choose_mul_factorial_mul_factorial (show h ≤ h+a+b by omega)
  have hsub1 : a+b-a = b := by omega
  have hsub2 : h+a+b-h = a+b := by omega
  rw [hsub1] at hbc
  rw [hsub2] at hha
  have hi : (h+a+b).choose h * (a+b).choose a *
      (h.factorial*a.factorial*b.factorial) = (h+a+b).factorial := by
    calc
      _ = (h+a+b).choose h * h.factorial *
          ((a+b).choose a * a.factorial * b.factorial) := by ring
      _ = _ := by rw [hbc,hha]
  rw [← hi]
  exact Nat.mul_le_mul_right _ (three_choose_bound h a b)

theorem total_three_segment_weight_le {x : ℝ} (hx : 0 ≤ x) (h a b : ℕ) :
    x^(h+a+b) / ((h.factorial : ℝ)*(a.factorial : ℝ)*(b.factorial : ℝ)) ≤
      (3*x)^(h+a+b) / ((h+a+b).factorial : ℝ) := by
  have hf : ((h+a+b).factorial : ℝ) ≤
      (3 : ℝ)^(h+a+b)*((h.factorial : ℝ)*(a.factorial : ℝ)*(b.factorial : ℝ)) := by
    exact_mod_cast three_factorial_bound h a b
  have hh := mul_le_mul_of_nonneg_left hf (pow_nonneg hx (h+a+b))
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [mul_pow]
  nlinarith only [hh]

end SharpTerminalLeave

end

end OAI
