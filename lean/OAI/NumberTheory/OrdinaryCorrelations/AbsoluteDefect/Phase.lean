import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory

namespace OrdinaryDirichletMeanSquare

def phase (u x : ℝ) : ℂ := Complex.exp (Complex.I * ((u * x : ℝ) : ℂ))

def gaussian (x : ℝ) : ℝ := Real.exp (-x ^ 2)

def polynomial {ι : Type*} (s : Finset ι) (a : ι → ℂ) (u : ι → ℝ) (x : ℝ) : ℂ :=
  ∑ n ∈ s, a n * phase (u n) x

def gaussianConstant : ℝ := ‖(Real.pi : ℂ) ^ (1 / 2 : ℂ)‖

lemma norm_phase (u x : ℝ) : ‖phase u x‖ = 1 := by
  simp [phase, Complex.norm_exp]

lemma phase_mul_conj (u v x : ℝ) :
    phase u x * star (phase v x) = phase (u - v) x := by
  simp only [phase, Complex.star_def, ← Complex.exp_conj, map_mul,
    Complex.conj_I, Complex.conj_ofReal, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma gaussian_nonneg (x : ℝ) : 0 ≤ gaussian x := (Real.exp_pos _).le

lemma gaussian_integrable : Integrable gaussian := by
  change Integrable (fun x : ℝ => Real.exp (-x ^ 2))
  simpa using integrable_exp_neg_mul_sq (b := (1 : ℝ)) zero_lt_one

lemma gaussian_phase_integrable (u : ℝ) :
    Integrable (fun x : ℝ => (gaussian x : ℂ) * phase u x) := by
  have h := integrable_cexp_quadratic (b := (1 : ℂ)) (by norm_num) (Complex.I * u) 0
  convert h using 1
  ext x
  simp only [gaussian, phase, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma gaussian_phase_integral (u : ℝ) :
    ∫ x : ℝ, (gaussian x : ℂ) * phase u x =
      (Real.pi : ℂ) ^ (1 / 2 : ℂ) * (Real.exp (-u ^ 2 / 4) : ℂ) := by
  have h := fourierIntegral_gaussian (b := (1 : ℂ)) (by norm_num) (u : ℂ)
  convert h using 1
  · apply MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    simp only [gaussian, phase, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow]
    rw [mul_comm]
    congr 1 <;> congr 1 <;> push_cast <;> ring
  · simp [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_pow]

lemma norm_gaussian_phase_integral (u : ℝ) :
    ‖∫ x : ℝ, (gaussian x : ℂ) * phase u x‖ =
      gaussianConstant * Real.exp (-u ^ 2 / 4) := by
  rw [gaussian_phase_integral, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rfl

lemma gaussian_polynomial_integrable {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (u : ι → ℝ) :
    Integrable (fun x : ℝ => gaussian x * ‖polynomial s a u x‖ ^ 2) := by
  have hc : Continuous (fun x : ℝ => gaussian x * ‖polynomial s a u x‖ ^ 2) := by
    unfold gaussian polynomial phase
    fun_prop
  apply Integrable.mono' (gaussian_integrable.mul_const ((∑ n ∈ s, ‖a n‖) ^ 2))
    hc.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussian_nonneg _) (sq_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (gaussian_nonneg _)
  apply pow_le_pow_left₀ (norm_nonneg _) _
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => by simp [norm_phase])

lemma gaussian_pair_integrable (a b : ℂ) (u v : ℝ) :
    Integrable (fun x : ℝ => (gaussian x : ℂ) *
      (a * phase u x * star (b * phase v x))) := by
  have h := (gaussian_phase_integrable (u-v)).const_mul (a * star b)
  convert h using 1
  ext x
  rw [star_mul, ← phase_mul_conj]
  ring

lemma gaussian_polynomial_expansion {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (u : ι → ℝ) :
    (((∫ x : ℝ, gaussian x * ‖polynomial s a u x‖ ^ 2) : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, (a m * star (a n)) *
        (∫ x : ℝ, (gaussian x : ℂ) * phase (u m - u n) x) := by
  rw [← integral_complex_ofReal]
  have hi (m n : ι) : Integrable (fun x : ℝ =>
      (a m * star (a n)) * ((gaussian x : ℂ) * phase (u m - u n) x)) :=
    (gaussian_phase_integrable _).const_mul _
  have he (x : ℝ) : ((gaussian x * ‖polynomial s a u x‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, (a m * star (a n)) *
        ((gaussian x : ℂ) * phase (u m - u n) x) := by
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj']
    unfold polynomial
    simp only [map_sum]
    rw [Finset.sum_mul_sum]
    simp only [Finset.mul_sum, Complex.star_def, map_mul]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    rw [← phase_mul_conj]
    simp only [Complex.star_def]
    ring
  simp_rw [he]
  rw [integral_finsetSum s (fun m hm => integrable_finsetSum s (fun n hn => hi m n))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [integral_finsetSum s (fun n hn => hi m n)]
  apply Finset.sum_congr rfl
  intro n hn
  exact MeasureTheory.integral_const_mul _ _

lemma gaussian_polynomial_energy {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (u : ι → ℝ) :
    (∫ x : ℝ, gaussian x * ‖polynomial s a u x‖ ^ 2) ≤
      gaussianConstant * ∑ m ∈ s, ∑ n ∈ s,
        ‖a m‖ * ‖a n‖ * Real.exp (-(u m - u n) ^ 2 / 4) := by
  have hp : 0 ≤ ∫ x : ℝ, gaussian x * ‖polynomial s a u x‖ ^ 2 :=
    integral_nonneg fun x => mul_nonneg (gaussian_nonneg x) (sq_nonneg _)
  calc
    _ = ‖(((∫ x : ℝ, gaussian x * ‖polynomial s a u x‖ ^ 2) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
    _ = ‖∑ m ∈ s, ∑ n ∈ s, (a m * star (a n)) *
        (∫ x : ℝ, (gaussian x : ℂ) * phase (u m - u n) x)‖ := by
      rw [gaussian_polynomial_expansion]
    _ ≤ ∑ m ∈ s, ∑ n ∈ s, ‖(a m * star (a n)) *
        (∫ x : ℝ, (gaussian x : ℂ) * phase (u m - u n) x)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => norm_sum_le _ _)
    _ = _ := by
      simp_rw [norm_mul, norm_star, norm_gaussian_phase_integral, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      ring

lemma geometric_row (s : Finset ℕ) (m : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ n ∈ s, r ^ (Nat.dist m n) ≤ 2 * (1 - r)⁻¹ := by
  classical
  have hsum := summable_geometric_of_lt_one hr0 hr1
  have hleft : ∑ n ∈ s.filter (fun n => n ≤ m), r ^ (Nat.dist m n) ≤ (1-r)⁻¹ := by
    calc
      _ = ∑ k ∈ (s.filter (fun n => n ≤ m)).image (fun n => m-n), r ^ k := by
        rw [Finset.sum_image]
        · apply Finset.sum_congr rfl
          intro n hn
          rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Finset.mem_filter.mp hn).2]
        · intro n hn j hj heq
          dsimp at heq
          have hn' := (Finset.mem_filter.mp hn).2
          have hj' := (Finset.mem_filter.mp hj).2
          omega
      _ ≤ ∑' k : ℕ, r^k := hsum.sum_le_tsum _ (fun k hk => pow_nonneg hr0 k)
      _ = _ := tsum_geometric_of_lt_one hr0 hr1
  have hright : ∑ n ∈ s.filter (fun n => ¬n ≤ m), r ^ (Nat.dist m n) ≤ (1-r)⁻¹ := by
    calc
      _ = ∑ k ∈ (s.filter (fun n => ¬ n ≤ m)).image (fun n => n-m), r ^ k := by
        rw [Finset.sum_image]
        · apply Finset.sum_congr rfl
          intro n hn
          rw [Nat.dist_eq_sub_of_le (by have := (Finset.mem_filter.mp hn).2; omega)]
        · intro n hn j hj heq
          dsimp at heq
          have hn' := (Finset.mem_filter.mp hn).2
          have hj' := (Finset.mem_filter.mp hj).2
          omega
      _ ≤ ∑' k : ℕ, r^k := hsum.sum_le_tsum _ (fun k hk => pow_nonneg hr0 k)
      _ = _ := tsum_geometric_of_lt_one hr0 hr1
  rw [← Finset.sum_filter_add_sum_filter_not s (fun n => n ≤ m)]
  linarith

lemma geometric_exponential_row (s : Finset ℕ) (m : ℕ) {d : ℝ} (hd : 0 < d) :
    ∑ n ∈ s, Real.exp (-d * (Nat.dist m n : ℝ)) ≤ 2 + 2 / d := by
  have hr0 : 0 ≤ Real.exp (-d) := (Real.exp_pos _).le
  have hr1 : Real.exp (-d) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hh : ∑ n ∈ s, Real.exp (-d * (Nat.dist m n : ℝ)) ≤ 2 * (1-Real.exp (-d))⁻¹ := by
    convert geometric_row s m hr0 hr1 using 2
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  refine hh.trans ?_
  have hp : 0 < Real.exp d - 1 := by have := Real.exp_lt_exp.mpr hd; simpa using this
  have he : d ≤ Real.exp d - 1 := by linarith [Real.add_one_le_exp d]
  have hrew : (1-Real.exp (-d))⁻¹ = 1 + (Real.exp d - 1)⁻¹ := by
    rw [Real.exp_neg]
    field_simp
    ring
  rw [hrew]
  have hinv : (Real.exp d - 1)⁻¹ ≤ d⁻¹ := inv_anti₀ hd he
  simp only [div_eq_mul_inv]
  nlinarith

lemma log_separation {x y N : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxN : x ≤ N) (hyN : y ≤ N) :
    |x-y| / N ≤ |Real.log x - Real.log y| := by
  have hN : 0 < N := hx.trans_le hxN
  wlog hxy : x ≤ y generalizing x y
  · simpa [abs_sub_comm] using this hy hx hyN hxN (le_of_not_ge hxy)
  have hlog : Real.log x ≤ Real.log y := Real.log_le_log hx hxy
  rw [abs_of_nonpos (sub_nonpos.mpr hxy), abs_of_nonpos (sub_nonpos.mpr hlog), neg_sub, neg_sub]
  have hb := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
  rw [Real.log_div (ne_of_gt hy) (ne_of_gt hx), inv_div] at hb
  have hc : (y-x)/y ≤ Real.log y - Real.log x := by
    rw [sub_div, div_self (ne_of_gt hy)]
    exact hb
  exact (div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hy hyN).trans hc

lemma dist_real (m n : ℕ) : (Nat.dist m n : ℝ) = |(m : ℝ) - n| := by
  rcases le_total m n with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr (by exact_mod_cast h)
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, abs_of_nonneg]
    exact sub_nonneg.mpr (by exact_mod_cast h)

lemma gaussian_kernel_le (z : ℝ) :
    Real.exp (-z^2 / 4) ≤ Real.exp (1/4) * Real.exp (-|z|/2) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have h := sq_nonneg (|z| / 2 - 1/2)
  nlinarith [sq_abs z]

lemma log_gaussian_row (s : Finset ℕ) {N T : ℝ}
    (hN : 0 < N) (hT : 0 < T)
    (hs : ∀ n ∈ s, 0 < (n : ℝ) ∧ (n : ℝ) ≤ N) (m : ℕ) (hm : m ∈ s) :
    ∑ n ∈ s, Real.exp (-(T * Real.log m - T * Real.log n)^2 / 4) ≤
      Real.exp (1/4) * (2 + 4 * N / T) := by
  have hd : 0 < T / (2*N) := div_pos hT (by positivity)
  calc
    _ ≤ ∑ n ∈ s, Real.exp (1/4) * Real.exp (-(T / (2*N)) * (Nat.dist m n : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      apply (gaussian_kernel_le _).trans
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      rw [Real.exp_le_exp]
      have hsep := log_separation (hs m hm).1 (hs n hn).1 (hs m hm).2 (hs n hn).2
      rw [← dist_real] at hsep
      have hmul := mul_le_mul_of_nonneg_left hsep hT.le
      rw [← mul_sub, abs_mul, abs_of_pos hT]
      have he : (T / (2*N)) * (Nat.dist m n : ℝ) =
          T * ((Nat.dist m n : ℝ) / N) / 2 := by field_simp
      rw [neg_mul, he]
      linarith
    _ = Real.exp (1/4) * ∑ n ∈ s, Real.exp (-(T / (2*N)) * (Nat.dist m n : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (1/4) * (2 + 2 / (T / (2*N))) :=
      mul_le_mul_of_nonneg_left (geometric_exponential_row s m hd) (Real.exp_pos _).le
    _ = _ := by congr 1; field_simp; ring

lemma finite_schur {ι : Type*} (s : Finset ι) (a : ι → ℝ) (K : ι → ι → ℝ)
    (R : ℝ) (hK : ∀ m ∈ s, ∀ n ∈ s, 0 ≤ K m n)
    (hsym : ∀ m ∈ s, ∀ n ∈ s, K m n = K n m)
    (hrow : ∀ m ∈ s, ∑ n ∈ s, K m n ≤ R) :
    ∑ m ∈ s, ∑ n ∈ s, a m * a n * K m n ≤ R * ∑ m ∈ s, (a m)^2 := by
  have heq : (∑ m ∈ s, ∑ n ∈ s, ((a m)^2 + (a n)^2) * K m n) =
      2 * ∑ m ∈ s, (a m)^2 * ∑ n ∈ s, K m n := by
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun m n => (a n)^2 * K m n)]
    have hsym' : (∑ n ∈ s, ∑ m ∈ s, (a n)^2 * K m n) =
        ∑ n ∈ s, ∑ m ∈ s, (a n)^2 * K n m := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      rw [hsym m hm n hn]
    rw [hsym']
    simp_rw [← Finset.mul_sum]
    ring
  have h := Finset.sum_le_sum (s := s) (fun m hm =>
    Finset.sum_le_sum (s := s) (fun n hn =>
      mul_le_mul_of_nonneg_right (show 2 * (a m * a n) ≤ (a m)^2 + (a n)^2 by
        nlinarith [sq_nonneg (a m - a n)]) (hK m hm n hn)))
  simp_rw [mul_assoc, ← Finset.mul_sum] at h
  rw [heq] at h
  have hb : (∑ m ∈ s, (a m)^2 * ∑ n ∈ s, K m n) ≤ R * ∑ m ∈ s, (a m)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hrow m hm) (sq_nonneg (a m))
  simp_rw [mul_assoc, ← Finset.mul_sum]
  linarith

lemma logarithmic_gaussian_energy (s : Finset ℕ) (a : ℕ → ℂ) {N T : ℝ}
    (hN : 0 < N) (hT : 0 < T)
    (hs : ∀ n ∈ s, 0 < (n : ℝ) ∧ (n : ℝ) ≤ N) :
    (∫ x : ℝ, gaussian x * ‖polynomial s a (fun n => T * Real.log n) x‖ ^ 2) ≤
      gaussianConstant * (Real.exp (1/4) * (2 + 4 * N / T)) * ∑ n ∈ s, ‖a n‖^2 := by
  apply (gaussian_polynomial_energy s a (fun n => T * Real.log n)).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply finite_schur
  · intro m hm n hn
    exact (Real.exp_pos _).le
  · intro m hm n hn
    congr 1
    rw [sub_sq_comm]
  · intro m hm
    exact log_gaussian_row s hN hT hs m hm

lemma polynomial_rescale (s : Finset ℕ) (a : ℕ → ℂ) {T : ℝ} (hT : T ≠ 0) (x : ℝ) :
    polynomial s a (fun n => T * Real.log n) (x/T) =
      polynomial s a (fun n => Real.log n) x := by
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  unfold phase
  congr 2
  field_simp

lemma logarithmic_scaled_integrable (s : Finset ℕ) (a : ℕ → ℂ) {T : ℝ} (hT : T ≠ 0) :
    Integrable (fun x : ℝ => gaussian (x/T) * ‖polynomial s a (fun n => Real.log n) x‖^2) := by
  have h := (integrable_comp_mul_right_iff
    (fun x => gaussian x * ‖polynomial s a (fun n => T * Real.log n) x‖^2)
    (inv_ne_zero hT)).mpr (gaussian_polynomial_integrable s a _)
  simpa only [← div_eq_mul_inv, polynomial_rescale s a hT] using h

lemma logarithmic_scaled_energy (s : Finset ℕ) (a : ℕ → ℂ) {N T : ℝ}
    (hN : 0 < N) (hT : 0 < T)
    (hs : ∀ n ∈ s, 0 < (n : ℝ) ∧ (n : ℝ) ≤ N) :
    (∫ x : ℝ, gaussian (x/T) * ‖polynomial s a (fun n => Real.log n) x‖ ^ 2) ≤
      gaussianConstant * Real.exp (1/4) * (2*T + 4*N) * ∑ n ∈ s, ‖a n‖^2 := by
  have he := Measure.integral_comp_div
    (fun x => gaussian x * ‖polynomial s a (fun n => T * Real.log n) x‖^2) T
  simp only [polynomial_rescale s a hT.ne', abs_of_pos hT, smul_eq_mul] at he
  rw [he]
  have hb := mul_le_mul_of_nonneg_left (logarithmic_gaussian_energy s a hN hT hs) hT.le
  calc
    _ ≤ T * (gaussianConstant * (Real.exp (1/4) * (2 + 4*N/T)) *
        ∑ n ∈ s, ‖a n‖^2) := hb
    _ = _ := by field_simp [hT.ne']

lemma logarithmic_interval_energy (s : Finset ℕ) (a : ℕ → ℂ) {N T : ℝ}
    (hN : 0 < N) (hT : 0 < T)
    (hs : ∀ n ∈ s, 0 < (n : ℝ) ∧ (n : ℝ) ≤ N) :
    (∫ x : ℝ in Set.Icc (-T) T, ‖polynomial s a (fun n => Real.log n) x‖ ^ 2) ≤
      4 * Real.exp (1+1/4) * gaussianConstant * (T+N) * ∑ n ∈ s, ‖a n‖^2 := by
  let P : ℝ → ℂ := polynomial s a (fun n => Real.log n)
  have hc : Continuous (fun x : ℝ => ‖P x‖^2) := by
    unfold P polynomial phase
    fun_prop
  have hw := (logarithmic_scaled_integrable s a hT.ne').const_mul (Real.exp 1)
  have hm : (∫ x : ℝ in Set.Icc (-T) T, ‖P x‖^2) ≤
      ∫ x : ℝ, Real.exp 1 * (gaussian (x/T) * ‖P x‖^2) := by
    apply (integral_mono_ae hc.integrableOn_Icc hw.integrableOn ?_).trans
      (setIntegral_le_integral hw (by
        filter_upwards [] with x
        exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (gaussian_nonneg _) (sq_nonneg _))))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hab : |x/T| ≤ 1 := by
      rw [abs_div, abs_of_pos hT, div_le_one hT]
      exact abs_le.mpr hx
    have hsquare : (x/T)^2 ≤ 1 := by
      have hab0 := abs_nonneg (x/T)
      nlinarith [sq_abs (x/T)]
    have hexp : 1 ≤ Real.exp 1 * gaussian (x/T) := by
      unfold gaussian
      rw [← Real.exp_add, Real.one_le_exp_iff]
      linarith
    nlinarith [sq_nonneg ‖P x‖, mul_le_mul_of_nonneg_right hexp (sq_nonneg ‖P x‖)]
  refine hm.trans ?_
  rw [MeasureTheory.integral_const_mul]
  have hb := mul_le_mul_of_nonneg_left (logarithmic_scaled_energy s a hN hT hs) (Real.exp_pos 1).le
  apply hb.trans
  rw [Real.exp_add]
  have hn : 0 ≤ ∑ n ∈ s, ‖a n‖^2 := Finset.sum_nonneg fun n hn => sq_nonneg _
  have hg : 0 ≤ gaussianConstant := norm_nonneg _
  have he : 0 ≤ Real.exp 1 * Real.exp (1/4) * gaussianConstant * ∑ n ∈ s, ‖a n‖^2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (show 2*T+4*N ≤ 4*(T+N) by linarith) he]

end OrdinaryDirichletMeanSquare

end

end OAI
