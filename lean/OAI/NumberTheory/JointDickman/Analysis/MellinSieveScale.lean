import OAI.NumberTheory.JointDickman.Analysis.MellinSieveHighFrequency

namespace OAI

/-! # Polynomial cutoffs for the explicit Mellin divisor error -/
namespace JointDickman

lemma mellinSieve_grid_error_coarse {N : ℝ} (hN : 0 < N) (K d : ℕ) (hd : 0 < d)
    (hNK : N ≤ (K:ℝ)/2) (hdK : (d:ℝ) ≤ (K:ℝ)/2) (t : ℝ) :
    ‖mellinSieveDiscreteKernel K d N t-mellinSieveMainKernel N t/(d:ℂ)‖ ≤
      (K:ℝ)*(3+|t|)/N + 2*N^3/((d:ℝ)*(K:ℝ)^2) := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hK0 : (0:ℝ) < K := by linarith
  let L : ℝ := (d:ℝ)*(K/d:ℕ)
  have hL : (K:ℝ)/2 ≤ L := by
    have hmod : K % d < d := Nat.mod_lt K hd
    have he := Nat.mod_add_div K d
    have heR : (K:ℝ) = (K%d:ℕ)+(d:ℝ)*(K/d:ℕ) := by exact_mod_cast he.symm
    have hmR : ((K%d:ℕ):ℝ) < d := by exact_mod_cast hmod
    dsimp [L]
    linarith
  have hLK : L ≤ K := by dsimp [L]; exact_mod_cast Nat.mul_div_le K d
  have hL0 : 0 < L := (by linarith : 0 < (K:ℝ)/2).trans_le hL
  have hh := mellinSieve_grid_error hN K d hd (hNK.trans hL) t
  apply hh.trans
  apply add_le_add
  · have ht : 0 ≤ (3+|t|)/N := by positivity
    calc
      _ = L*((3+|t|)/N) := by dsimp [L]; ring
      _ ≤ _ := by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hLK ht
  · change N^3/((d:ℝ)*2*L^2) ≤ _
    calc
      _ ≤ N^3/((d:ℝ)*2*((K:ℝ)/2)^2) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hL 2) (by positivity)
      _ = _ := by field_simp

/-- One fixed set of integer powers gives a common low-frequency range
for all profiles between the tenth and eleventh powers. -/
theorem mellinSieve_integer_scale_low (q d : ℕ) (hq : 2 ≤ q) (hd : 0 < d) (hdq : d ≤ q)
    {N t : ℝ} (hNlo : (q:ℝ)^10 ≤ N) (hNhi : N ≤ (q:ℝ)^11)
    (ht : |t| ≤ (q:ℝ)^7) :
    ‖mellinSieveDiscreteKernel (q^12) d N t-mellinSieveMainKernel N t/(d:ℂ)‖ ≤
      6*(q:ℝ)^9 := by
  have hqR : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith
  have hq1 : (1:ℝ) ≤ q := by linarith
  have hN : 0 < N := (pow_pos hq0 10).trans_le hNlo
  have hNK : N ≤ ((q^12:ℕ):ℝ)/2 := by
    push_cast
    apply hNhi.trans
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2), pow_succ]
    nlinarith [pow_pos hq0 11]
  have hdK : (d:ℝ) ≤ ((q^12:ℕ):ℝ)/2 := by
    have hdR : (d:ℝ) ≤ q := by exact_mod_cast hdq
    have hp : (q:ℝ)^2 ≤ (q:ℝ)^12 := pow_le_pow_right₀ hq1 (by norm_num)
    push_cast
    linarith [sq_nonneg ((q:ℝ)-2)]
  have hh := mellinSieve_grid_error_coarse hN (q^12) d hd hNK hdK t
  have hfirst : ((q^12:ℕ):ℝ)*(3+|t|)/N ≤ 4*(q:ℝ)^9 := by
    calc
      _ ≤ (q:ℝ)^12*(3+(q:ℝ)^7)/(q:ℝ)^10 := by push_cast; gcongr
      _ = (q:ℝ)^2*(3+(q:ℝ)^7) := by field_simp
      _ ≤ 4*(q:ℝ)^9 := by
        have hp := one_le_pow₀ hq1 (n := 7)
        nlinarith [mul_nonneg (sq_nonneg (q:ℝ)) (sub_nonneg.mpr hp)]
  have hsecond : 2*N^3/((d:ℝ)*((q^12:ℕ):ℝ)^2) ≤ 2*(q:ℝ)^9 := by
    have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
    calc
      _ ≤ 2*((q:ℝ)^11)^3/(1*((q:ℝ)^12)^2) := by push_cast; gcongr
      _ = _ := by field_simp
  exact hh.trans (by linarith)

end JointDickman

end OAI
