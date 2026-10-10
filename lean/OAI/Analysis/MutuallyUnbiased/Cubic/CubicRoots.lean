import OAI.Analysis.MutuallyUnbiased.Tao.Tao

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem omega_ne_one : omega ≠ 1 := omega_isPrimitiveRoot.ne_one (by decide)

theorem omega_sq_ne_one : omega ^ 2 ≠ 1 := by
  intro h
  have he : omega ^ 3 = omega := by rw [pow_succ, h, one_mul]
  exact omega_ne_one (he.symm.trans omega_cube)

theorem omega_sq_ne_omega : omega ^ 2 ≠ omega := by
  intro h
  have he : omega * omega = omega * 1 := by simpa [pow_two] using h
  exact omega_ne_one (mul_left_cancel₀ (omega_isPrimitiveRoot.ne_zero (by decide)) he)

theorem omega_re : omega.re = (-1 / 2 : ℝ) := by
  have h := congrArg Complex.re omega_sum
  rw [← omega_conj] at h
  simp only [Complex.add_re, Complex.one_re, Complex.conj_re, Complex.zero_re] at h
  linarith

theorem omega_sq_re : (omega ^ 2).re = (-1 / 2 : ℝ) := by
  rw [← omega_conj, Complex.conj_re, omega_re]

theorem cube_roots_three (z : ℂ) (hz : z ^ 3 = 1) :
    z = 1 ∨ z = omega ∨ z = omega ^ 2 := by
  have hf : (z - 1) * (z - omega) * (z - omega ^ 2) = 0 := by
    calc
      (z - 1) * (z - omega) * (z - omega ^ 2) = z ^ 3 - 1 := by
        linear_combination (-z ^ 2 + z) * omega_sum + (z - 1) * omega_cube
      _ = 0 := by rw [hz, sub_self]
  rcases mul_eq_zero.mp hf with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

theorem cube_root_real_indicator (z : ℂ) (hz : z ^ 3 = 1) :
    z.re = (3 / 2 : ℝ) * (if z = 1 then 1 else 0) - 1 / 2 := by
  rcases cube_roots_three z hz with rfl | rfl | rfl
  · norm_num
  · rw [ite_eq_right omega_ne_one, omega_re]
    norm_num
  · rw [ite_eq_right omega_sq_ne_one, omega_sq_re]
    norm_num

/-- Six cube roots summing to zero contain the root one exactly twice. -/
theorem cube_roots_one_count (v : Coord → ℂ) (hv : ∀ i, v i ^ 3 = 1)
    (hs : ∑ i, v i = 0) : (Finset.univ.filter (fun i => v i = 1)).card = 2 := by
  classical
  have hre : (∑ i, (v i).re) = 0 := by
    simpa only [Complex.re_sum, Complex.zero_re] using congrArg Complex.re hs
  simp_rw [cube_root_real_indicator _ (hv _)] at hre
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hre
  have hc : (∑ i, if v i = 1 then (1 : ℝ) else 0) =
      ((Finset.univ.filter (fun i => v i = 1)).card : ℝ) := by simp
  rw [hc] at hre
  norm_num at hre
  have hn : ((Finset.univ.filter (fun i => v i = 1)).card : ℝ) = 2 := by
    linarith
  exact_mod_cast hn

/-- Every cube root occurs twice among six cube roots whose sum vanishes. -/
theorem cube_roots_each_count (v : Coord → ℂ) (hv : ∀ i, v i ^ 3 = 1)
    (hs : ∑ i, v i = 0) (a : ℂ) (ha : a ^ 3 = 1) :
    (Finset.univ.filter (fun i => v i = a)).card = 2 := by
  classical
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hv' : ∀ i, (v i / a) ^ 3 = 1 := by intro i; rw [div_pow, hv, ha, div_self one_ne_zero]
  have hs' : (∑ i, v i / a) = 0 := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, hs, zero_mul]
  have hc := cube_roots_one_count (fun i => v i / a) hv' hs'
  simpa only [div_eq_one_iff_eq ha0] using hc

end MUB6

end

end OAI
