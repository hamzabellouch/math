import Mathlib

namespace OAI

/-! Exponential generating functions and differentiation of Poisson averages. -/

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical

noncomputable def expGenerating (f : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, t^n/(n.factorial:ℝ)*f n
noncomputable def poissonAverage (f : ℕ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-t)*expGenerating f t

lemma summable_expGenerating_linear (R : ℝ) :
    Summable (fun n : ℕ => R^n/(n.factorial:ℝ)*((n:ℝ)+2)) := by
  have h0 := (NormedSpace.expSeries_div_hasSum_exp R).summable
  have h1 : Summable (fun n : ℕ => R^n/(n.factorial:ℝ)*(n:ℝ)) := by
    apply (summable_nat_add_iff 1).mp
    convert! h0.mul_left R using 1
    funext n
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul]
    have hn : ((n+1:ℕ):ℝ) ≠ 0 := by positivity
    have hf : (n.factorial:ℝ) ≠ 0 := by positivity
    field_simp
  convert h1.add (h0.mul_right 2) using 1
  funext n
  ring

lemma summable_expGenerating_deriv_bound (R C : ℝ) :
    Summable (fun n : ℕ => (n:ℝ)*R^(n-1)/(n.factorial:ℝ)*(C*((n:ℝ)+1))) := by
  apply (summable_nat_add_iff 1).mp
  convert! (summable_expGenerating_linear R).mul_left C using 1
  funext n
  rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

lemma expGenerating_hasDerivAt (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n, |f n| ≤ C*((n:ℝ)+1)) (t : ℝ) :
    HasDerivAt (expGenerating f) (expGenerating (fun n => f (n+1)) t) t := by
  let R := |t|+1
  have hR : 0 < R := by dsimp [R]; positivity
  have ht : t ∈ Set.Ioo (-R) R := by dsimp [R]; constructor <;> linarith [neg_abs_le t, le_abs_self t]
  have hzero : (0:ℝ) ∈ Set.Ioo (-R) R := by constructor <;> linarith
  have hsum0 : Summable (fun n : ℕ => (0:ℝ)^n/(n.factorial:ℝ)*f n) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    have hn0 : n ≠ 0 := by simpa using hn
    simp [hn0]
  have hb (n : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (-R) R) :
      ‖(n:ℝ)*y^(n-1)/(n.factorial:ℝ)*f n‖ ≤
        (n:ℝ)*R^(n-1)/(n.factorial:ℝ)*(C*((n:ℝ)+1)) := by
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_mul, abs_of_nonneg (by positivity : (0:ℝ)≤n),
      abs_pow, abs_of_nonneg (by positivity : (0:ℝ)≤n.factorial)]
    calc
      _ ≤ (n:ℝ)*|y|^(n-1)/(n.factorial:ℝ)*(C*((n:ℝ)+1)) :=
        mul_le_mul_of_nonneg_left (hf n) (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC (by positivity))
        gcongr
        exact le_of_lt (abs_lt.mpr hy)
  have hh := hasDerivAt_tsum_of_isPreconnected (summable_expGenerating_deriv_bound R C)
    isOpen_Ioo (convex_Ioo (-R) R).isPreconnected
    (g := fun n y => y^n/(n.factorial:ℝ)*f n)
    (g' := fun n y => (n:ℝ)*y^(n-1)/(n.factorial:ℝ)*f n)
    (fun n y _ => ((hasDerivAt_pow n y).div_const (n.factorial:ℝ)).mul_const (f n))
    hb hzero hsum0 ht
  have hs : Summable (fun n : ℕ => (n:ℝ)*t^(n-1)/(n.factorial:ℝ)*f n) :=
    Summable.of_norm_bounded (summable_expGenerating_deriv_bound R C) (fun n => hb n t ht)
  have hid : (∑' n : ℕ, (n:ℝ)*t^(n-1)/(n.factorial:ℝ)*f n) = expGenerating (fun n => f (n+1)) t := by
    rw [← hs.sum_add_tsum_nat_add 1]
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, zero_div, zero_add]
    apply tsum_congr
    intro n
    rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
    have hn : ((n+1:ℕ):ℝ) ≠ 0 := by positivity
    have hc : (n.factorial:ℝ) ≠ 0 := by positivity
    field_simp
  rwa [hid] at hh

lemma expGenerating_summable (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n, |f n| ≤ C*((n:ℝ)+1)) (t : ℝ) :
    Summable (fun n : ℕ => t^n/(n.factorial:ℝ)*f n) := by
  apply Summable.of_norm_bounded ((summable_expGenerating_linear |t|).mul_left C)
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_of_nonneg (by positivity : (0:ℝ)≤n.factorial)]
  calc
    _ ≤ |t|^n/(n.factorial:ℝ)*(C*((n:ℝ)+1)) := mul_le_mul_of_nonneg_left (hf n) (by positivity)
    _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ |t|^n/(n.factorial:ℝ) by positivity) hC]

lemma poissonAverage_hasDerivAt (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n, |f n| ≤ C*((n:ℝ)+1)) (t : ℝ) :
    HasDerivAt (poissonAverage f) (poissonAverage (fun n => f (n+1)-f n) t) t := by
  have hf' (n : ℕ) : |f (n+1)| ≤ (2*C)*((n:ℝ)+1) := by
    have hh := hf (n+1)
    push_cast at hh
    nlinarith [mul_nonneg hC (show (0:ℝ)≤n by positivity)]
  have hs := expGenerating_summable f C hC hf t
  have hs' := expGenerating_summable (fun n => f (n+1)) (2*C) (by positivity) hf' t
  have hdiff : expGenerating (fun n => f (n+1)-f n) t =
      expGenerating (fun n => f (n+1)) t-expGenerating f t := by
    unfold expGenerating
    simp only [mul_sub, hs'.tsum_sub hs]
  have hh := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).mul (expGenerating_hasDerivAt f C hC hf t)
  change HasDerivAt (poissonAverage f) _ t at hh
  convert hh using 1
  dsimp only [poissonAverage]
  rw [hdiff]
  simp only [Function.comp_apply]
  ring

end ThreeState

end OAI
