import OAI.MeasureTheory.Falconer.Graphs.GraphNormalization
import OAI.MeasureTheory.Falconer.Estimates.InversePowerSum

namespace OAI

/-!
# Critical-dimensional cancellation in the parallel-test average

Here `s` will be d/2. The interval minimum is over the original integer
depths, and the retained profile is evaluated at those exact depths.
-/

namespace Falconer

theorem dyadic_power_rpow_as_R {N : ℕ} (hN : 0 < N) (n : ℕ) (s : ℝ) :
    ((2:ℝ)^n)^s = ((2:ℝ)^N)^(s*(n:ℝ)/N) := by
  rw [dyadic_rpow_change_base hN,← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

theorem angular_profile_power_weight (m : ℝ → ℝ) {N : ℕ} (hN : 0 < N)
    (s E : ℝ) {g h p : ℕ} (hgh : g ≤ h) (hhp : h ≤ p) :
    (((2:ℝ)^N)^(m p-m h+E)*((2:ℝ)^h)^s)/((2:ℝ)^p)^s ≤
      ((2:ℝ)^N)^(PlanarFalconer.height (fun n : ℕ => m n-s*(n:ℝ)/N) g p+E) := by
  have hp : 0 < (2:ℝ)^N := by positivity
  rw [dyadic_power_rpow_as_R hN h,dyadic_power_rpow_as_R hN p,
    ← Real.rpow_add hp,← Real.rpow_sub hp]
  apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
  have hh := PlanarFalconer.intervalMin_le (fun n : ℕ => m n-s*(n:ℝ)/N) hgh hhp
  dsimp only [PlanarFalconer.height]
  linarith

theorem angular_profile_power_sum (m : ℝ → ℝ) {N : ℕ} (hN : 0 < N)
    (s E : ℝ) {g p : ℕ} (hgp : g ≤ p) :
    ((((2:ℝ)^N)^(m p-m g+E)*((2:ℝ)^g)^s +
      ∑ j ∈ Finset.range (p-g),
        ((2:ℝ)^N)^(m p-m (g+j)+E)*((2:ℝ)^(g+j+1))^s))/((2:ℝ)^p)^s ≤
      (1+(2:ℝ)^s*(p-g:ℕ))*
        ((2:ℝ)^N)^(PlanarFalconer.height (fun n : ℕ => m n-s*(n:ℝ)/N) g p+E) := by
  let Z := ((2:ℝ)^N)^(PlanarFalconer.height (fun n : ℕ => m n-s*(n:ℝ)/N) g p+E)
  rw [add_div,Finset.sum_div]
  have hbase := angular_profile_power_weight m hN s E (g := g) le_rfl hgp
  have hsum : (∑ j ∈ Finset.range (p-g),
      (((2:ℝ)^N)^(m p-m (g+j)+E)*((2:ℝ)^(g+j+1))^s)/((2:ℝ)^p)^s) ≤
        (p-g:ℕ)*((2:ℝ)^s*Z) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (p-g), ((2:ℝ)^s*Z) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have hh := angular_profile_power_weight m hN s E (g := g) (h := g+j) (p := p)
          (by omega) (by omega)
        simp only [Nat.cast_add] at hh
        rw [pow_succ,Real.mul_rpow (by positivity) (by positivity)]
        have he : (((2:ℝ)^N)^(m p-m (g+j)+E)*(((2:ℝ)^(g+j))^s*(2:ℝ)^s))/((2:ℝ)^p)^s =
            (2:ℝ)^s*((((2:ℝ)^N)^(m p-m (g+j)+E)*((2:ℝ)^(g+j))^s)/((2:ℝ)^p)^s) := by ring
        rw [he]
        exact mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by simp
  change _ ≤ (1+(2:ℝ)^s*(p-g:ℕ))*Z
  change _ ≤ Z at hbase
  nlinarith

end Falconer

end OAI
