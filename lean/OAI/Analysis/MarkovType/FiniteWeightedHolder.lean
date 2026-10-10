import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Ring

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {ι : Type*}

theorem holder_weight_split {p q w : ℝ} (hpq : p.HolderConjugate q) (hw : 0 ≤ w) :
    w ^ (1 / p) * w ^ (1 / q) = w := by
  have hs : 1 / p + 1 / q = (1 : ℝ) := by simpa using hpq.one_div_add_one_div
  rw [← Real.rpow_add' hw (by rw [hs]; exact one_ne_zero), hs, Real.rpow_one]

theorem weighted_power_root_mul {r w a : ℝ} (hr : r ≠ 0)
    (hw : 0 ≤ w) (ha : 0 ≤ a) :
    (w ^ (1 / r) * a) ^ r = w * a ^ r := by
  rw [Real.mul_rpow (Real.rpow_nonneg hw _) ha, ← Real.rpow_mul hw,
    one_div, inv_mul_cancel₀ hr, Real.rpow_one]

theorem finite_weighted_holder (s : Finset ι) {w a b : ι → ℝ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hw : ∀ i ∈ s, 0 ≤ w i)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    (∑ i ∈ s, w i * a i * b i) ≤
      (∑ i ∈ s, w i * a i ^ p) ^ (1 / p) *
        (∑ i ∈ s, w i * b i ^ q) ^ (1 / q) := by
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg
    (f := fun i => w i ^ (1 / p) * a i)
    (g := fun i => w i ^ (1 / q) * b i) s hpq
    (fun i hi => mul_nonneg (Real.rpow_nonneg (hw i hi) _) (ha i hi))
    (fun i hi => mul_nonneg (Real.rpow_nonneg (hw i hi) _) (hb i hi))
  have hleft : (∑ i ∈ s, (w i ^ (1 / p) * a i) * (w i ^ (1 / q) * b i)) =
      ∑ i ∈ s, w i * a i * b i := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      (w i ^ (1 / p) * a i) * (w i ^ (1 / q) * b i) =
          (w i ^ (1 / p) * w i ^ (1 / q)) * a i * b i := by ring
      _ = w i * a i * b i := by rw [holder_weight_split hpq (hw i hi)]
  have hrightp : (∑ i ∈ s, (w i ^ (1 / p) * a i) ^ p) =
      ∑ i ∈ s, w i * a i ^ p := by
    apply Finset.sum_congr rfl
    intro i hi
    exact weighted_power_root_mul hpq.ne_zero (hw i hi) (ha i hi)
  have hrightq : (∑ i ∈ s, (w i ^ (1 / q) * b i) ^ q) =
      ∑ i ∈ s, w i * b i ^ q := by
    apply Finset.sum_congr rfl
    intro i hi
    exact weighted_power_root_mul hpq.symm.ne_zero (hw i hi) (hb i hi)
  rwa [hleft, hrightp, hrightq] at h

theorem finite_weighted_holder_univ [Fintype ι] {w a b : ι → ℝ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (∑ i, w i * a i * b i) ≤
      (∑ i, w i * a i ^ p) ^ (1 / p) *
        (∑ i, w i * b i ^ q) ^ (1 / q) :=
  finite_weighted_holder Finset.univ hpq
    (fun i _ => hw i) (fun i _ => ha i) (fun i _ => hb i)

theorem abs_sum_weighted_le_holder (s : Finset ι) {w a b c : ι → ℝ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hw : ∀ i ∈ s, 0 ≤ w i)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hc : ∀ i ∈ s, |c i| ≤ a i * b i) :
    |∑ i ∈ s, w i * c i| ≤
      (∑ i ∈ s, w i * a i ^ p) ^ (1 / p) *
        (∑ i ∈ s, w i * b i ^ q) ^ (1 / q) := by
  calc
    |∑ i ∈ s, w i * c i| ≤ ∑ i ∈ s, |w i * c i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, w i * a i * b i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (hw i hi)]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hc i hi) (hw i hi)
    _ ≤ _ := finite_weighted_holder s hpq hw ha hb

end MarkovSuperreflexivity

end OAI
