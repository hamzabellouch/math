import OAI.MeasureTheory.Falconer.Angular.AngularDyadicSum
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.Falconer.Frostman.FrostmanProfileCells

namespace OAI

namespace PlanarFalconer

theorem dyadic_power_as_R {N : ℕ} (hN : 0 < N) (n : ℕ) :
    (2:ℝ)^n = ((2:ℝ)^N)^((n:ℝ)/(N:ℝ)) := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (N:ℝ)*((n:ℝ)/(N:ℝ)) = n := mul_div_cancel₀ (n : ℝ) hn
  rw [he,Real.rpow_natCast]

theorem angular_profile_weight (m : ℝ → ℝ) {N : ℕ} (hN : 0 < N)
    (lam : ℝ) {g h p : ℕ} (hgh : g ≤ h) (hhp : h ≤ p) :
    (((2:ℝ)^N)^(m p-m h+6*lam)*(2:ℝ)^h)/(2:ℝ)^p ≤
      ((2:ℝ)^N)^(height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p+6*lam) := by
  let R : ℝ := (2:ℝ)^N
  have hRp : 0 < R := by dsimp [R]; positivity
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  rw [dyadic_power_as_R hN h,dyadic_power_as_R hN p,
    ← Real.rpow_add hRp,← Real.rpow_sub hRp]
  apply Real.rpow_le_rpow_of_exponent_le hR
  have hh := intervalMin_le (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) hgh hhp
  dsimp [height]
  linarith

theorem angular_profile_dyadic_sum (m : ℝ → ℝ) {N : ℕ} (hN : 0 < N)
    (lam : ℝ) {g p : ℕ} (hgp : g ≤ p) :
    ((((2:ℝ)^N)^(m p-m g+6*lam)*(2:ℝ)^g +
      ∑ j ∈ Finset.range (p-g),
        ((2:ℝ)^N)^(m p-m (g+j)+6*lam)*(2:ℝ)^(g+j+1)))/(2:ℝ)^p ≤
      (1+2*(p-g:ℕ))*((2:ℝ)^N)^(height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p+6*lam) := by
  let Z := ((2:ℝ)^N)^(height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p+6*lam)
  rw [add_div,Finset.sum_div]
  have hbase := angular_profile_weight m hN lam (g := g) le_rfl hgp
  have hsum : (∑ j ∈ Finset.range (p-g),
      (((2:ℝ)^N)^(m p-m (g+j)+6*lam)*(2:ℝ)^(g+j+1))/(2:ℝ)^p) ≤
        (p-g:ℕ)*(2*Z) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (p-g), (2*Z) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have hh := angular_profile_weight m hN lam (g := g) (h := g+j) (p := p) (by omega) (by omega)
        rw [pow_succ]
        have he : (((2:ℝ)^N)^(m p-m (g+j)+6*lam)*((2:ℝ)^(g+j)*2))/(2:ℝ)^p =
            2*((((2:ℝ)^N)^(m p-m (g+j)+6*lam)*(2:ℝ)^(g+j))/(2:ℝ)^p) := by ring
        rw [he]
        simp only [Nat.cast_add] at hh
        change _ ≤ Z at hh
        linarith
      _ = _ := by simp
  change _ ≤ (1+2*(p-g:ℕ))*Z
  change _ ≤ Z at hbase
  linarith

end PlanarFalconer

end OAI
