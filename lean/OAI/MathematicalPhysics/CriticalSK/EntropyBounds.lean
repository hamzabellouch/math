import OAI.MathematicalPhysics.CriticalSK.RelaxationBounds

namespace OAI

noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
namespace CriticalSK

lemma scalar_entropy_upper {z b : ℝ} (hz : 0 ≤ z) (hb : 0 < b) :
    b * (z * (Real.log z - Real.log b)) ≤ z ^ 2 - b * z := by
  by_cases hz0 : z = 0
  · simp [hz0]
  have hzp : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
  have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hzp hb))
    (mul_nonneg hb.le hz)
  rw [Real.log_div hz0 hb.ne'] at hh
  have he : (b * z) * (z / b - 1) = z ^ 2 - b * z := by
    field_simp
  rw [he] at hh
  simpa only [mul_assoc] using hh

lemma scalar_entropy_lower {z b : ℝ} (hz : 0 ≤ z) (hb : 0 < b) :
    2 * z ^ 2 - 2 * z * b ≤ z ^ 2 * (Real.log (z ^ 2) - Real.log (b ^ 2)) := by
  by_cases hz0 : z = 0
  · simp [hz0]
  have hh := mul_le_mul_of_nonneg_left (Real.self_sub_one_le_mul_log (div_nonneg hz hb.le)) hb.le
  have he : b * (z / b - 1) = z - b := by field_simp
  have he' : b * (z / b * Real.log (z / b)) = z * Real.log (z / b) := by field_simp
  rw [he, he', Real.log_div hz0 hb.ne'] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * z by positivity)
  rw [Real.log_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hmul]

section EntropyFinite
variable {n : ℕ} (W : Disorder n)

lemma variance_eq_second_moment (f : Spin n → ℝ) :
    variance W f = mean W (fun x => f x ^ 2) - (mean W f) ^ 2 := by
  have hh := mean_square_center_identity W f 0
  simp only [sub_zero] at hh
  linarith

lemma mean_square_pos_full {f : Spin n → ℝ} (hf : f ≠ 0) :
    0 < mean W (fun x => f x ^ 2) := by
  classical
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra! hh
    exact hf (funext hh)
  exact lt_of_lt_of_le (mul_pos (gibbs_pos W x) (sq_pos_of_ne_zero hx))
    (Finset.single_le_sum (fun y _ => mul_nonneg (gibbs_nonneg W y) (sq_nonneg (f y)))
      (Finset.mem_univ x))

lemma entropy_eq_centered_log (g : Spin n → ℝ) :
    entropy W g = mean W (fun x => g x * (Real.log (g x) - Real.log (mean W g))) := by
  simp only [entropy, mul_sub, mean_sub, mean_mul_const]

lemma entropy_times_mean_le_variance (g : Spin n → ℝ) (hg : ∀ x, 0 ≤ g x)
    (hp : 0 < mean W g) :
    mean W g * entropy W g ≤ variance W g := by
  have hh := mean_mono W (fun x => scalar_entropy_upper (hg x) hp)
  rw [mean_const_mul, ← entropy_eq_centered_log, mean_sub, mean_const_mul] at hh
  rw [variance_eq_second_moment]
  nlinarith only [hh]

lemma variance_le_entropy_square (f : Spin n → ℝ) (hf : ∀ x, 0 ≤ f x) :
    variance W f ≤ entropy W (fun x => f x ^ 2) := by
  by_cases hf0 : f = 0
  · simp [hf0, variance, entropy, mean]
  have hp := mean_square_pos_full W hf0
  have hh := mean_mono W (fun x => scalar_entropy_lower (hf x) (Real.sqrt_pos.mpr hp))
  rw [Real.sq_sqrt hp.le] at hh
  change mean W (fun x => 2 * f x ^ 2 - (2 * f x) * Real.sqrt (mean W (fun y => f y ^ 2))) ≤ _ at hh
  rw [mean_sub, mean_const_mul, mean_mul_const, mean_const_mul,
    ← entropy_eq_centered_log] at hh
  rw [variance_eq_second_moment]
  nlinarith [sq_nonneg (Real.sqrt (mean W (fun y => f y ^ 2)) - mean W f), Real.sq_sqrt hp.le]

lemma exists_gibbs_lower : ∃ m : ℝ, 0 < m ∧ ∀ x, m ≤ gibbs W x := by
  classical
  let T : Finset ℝ := Finset.univ.image (gibbs W)
  have hT : T.Nonempty := Finset.Nonempty.image Finset.univ_nonempty _
  refine ⟨T.min' hT, ?_, fun x => Finset.min'_le T _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)⟩
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp (Finset.min'_mem T hT)
  rw [← hx]
  exact gibbs_pos W x

lemma square_variance_bound {m : ℝ} (hm : 0 < m) (hmin : ∀ x, m ≤ gibbs W x)
    (f : Spin n → ℝ) :
    m * variance W (fun x => f x ^ 2) ≤ 4 * mean W (fun x => f x ^ 2) * variance W f := by
  let E := mean W (fun x => f x ^ 2)
  have hcoord (x : Spin n) : m * f x ^ 2 ≤ E := by
    calc
      _ ≤ gibbs W x * f x ^ 2 := mul_le_mul_of_nonneg_right (hmin x) (sq_nonneg _)
      _ ≤ _ := Finset.single_le_sum (fun y _ => mul_nonneg (gibbs_nonneg W y) (sq_nonneg (f y)))
        (Finset.mem_univ x)
  have hdiff (x y : Spin n) : m * (f x ^ 2 - f y ^ 2) ^ 2 ≤ 4 * E * (f x - f y) ^ 2 := by
    have hsum : m * (f x + f y) ^ 2 ≤ 4 * E := by
      nlinarith [hcoord x, hcoord y, mul_nonneg hm.le (sq_nonneg (f x - f y))]
    have hh := mul_le_mul_of_nonneg_right hsum (sq_nonneg (f x - f y))
    nlinarith only [hh]
  have hh : m * mean W (fun x => ∑ y, gibbs W y * (f x ^ 2 - f y ^ 2) ^ 2) ≤
      (4 * E) * mean W (fun x => ∑ y, gibbs W y * (f x - f y) ^ 2) := by
    rw [← mean_const_mul, ← mean_const_mul]
    apply mean_mono
    intro x
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _
    nlinarith only [mul_le_mul_of_nonneg_left (hdiff x y) (gibbs_nonneg W y)]
  rw [variance_pair_identity, variance_pair_identity] at hh
  change m * variance W (fun x => f x ^ 2) ≤ (4 * E) * variance W f
  linarith

lemma entropy_square_le_variance {m : ℝ} (hm : 0 < m) (hmin : ∀ x, m ≤ gibbs W x)
    (f : Spin n → ℝ) :
    entropy W (fun x => f x ^ 2) ≤ (4 / m) * variance W f := by
  by_cases hf0 : f = 0
  · simp [hf0, entropy, variance, mean]
  have hp := mean_square_pos_full W hf0
  have he := entropy_times_mean_le_variance W (fun x => f x ^ 2) (fun x => sq_nonneg _) hp
  have hv := square_variance_bound W hm hmin f
  have hh := (mul_le_mul_of_nonneg_left he hm.le).trans hv
  have hc : m * entropy W (fun x => f x ^ 2) ≤ 4 * variance W f := by
    apply (mul_le_mul_iff_left₀ hp).mp
    nlinarith only [hh]
  have := (le_div_iff₀ hm).mpr (by simpa only [mul_comm] using hc)
  convert this using 2
  first | rfl | ring

lemma exists_finite_logSobolev (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Spin n → ℝ,
      entropy W (fun x => f x ^ 2) ≤ C * dirichlet W f := by
  obtain ⟨m, hm, hmin⟩ := exists_gibbs_lower W
  obtain ⟨C, hC, hgap⟩ := exists_finite_poincare W hn
  have hb : 0 < 4 / m := div_pos (by norm_num) hm
  refine ⟨(4 / m) * C, mul_pos hb hC, fun f => ?_⟩
  calc
    _ ≤ (4 / m) * variance W f := entropy_square_le_variance W hm hmin f
    _ ≤ (4 / m) * (C * dirichlet W f) := mul_le_mul_of_nonneg_left (hgap f) hb.le
    _ = _ := by ring

lemma entropy_ratios_bdd (hn : 0 < n) :
    BddAbove {r : ℝ | ∃ f : Spin n → ℝ, 0 < entropy W (fun x => f x ^ 2) ∧
      r = entropy W (fun x => f x ^ 2) / dirichlet W f} := by
  obtain ⟨C, hC, hLS⟩ := exists_finite_logSobolev W hn
  refine ⟨C, ?_⟩
  rintro r ⟨f, hf, rfl⟩
  have hd : 0 < dirichlet W f := by
    by_contra h
    have ht := mul_nonpos_of_nonneg_of_nonpos hC.le (le_of_not_gt h)
    have hh := hLS f
    linarith
  exact (div_le_iff₀ hd).mpr (hLS f)

lemma variance_add_const (f : Spin n → ℝ) (c : ℝ) :
    variance W (fun x => f x + c) = variance W f := by
  simp only [variance, mean_add, mean_const, add_sub_add_right_eq_sub]

lemma dirichlet_add_const (f : Spin n → ℝ) (c : ℝ) :
    dirichlet W (fun x => f x + c) = dirichlet W f := by
  simp only [dirichlet, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    siteKernel_sum, one_mul, add_sub_add_right_eq_sub]

lemma full_ratios_nonempty (hn : 0 < n) :
    Set.Nonempty {r : ℝ | ∃ f : Spin n → ℝ, 0 < variance W f ∧
      r = variance W f / dirichlet W f} := by
  obtain ⟨r, a, ha, hr⟩ := linear_ratios_nonempty W hn
  exact ⟨r, linearObservable a, variance_linear_pos_full W ha, hr⟩

lemma relaxationTime_le_logSobolevConstant (hn : 0 < n) :
    relaxationTime W ≤ logSobolevConstant W := by
  apply csSup_le (full_ratios_nonempty W hn)
  rintro r ⟨f, hf, rfl⟩
  let c := ∑ x, |f x|
  have hnonneg (x : Spin n) : 0 ≤ f x + c := by
    have hh : |f x| ≤ c :=
      Finset.single_le_sum (fun x _ => abs_nonneg (f x)) (Finset.mem_univ x)
    linarith [neg_abs_le (f x)]
  have hvar := variance_le_entropy_square W (fun x => f x + c) hnonneg
  rw [variance_add_const] at hvar
  have he := lt_of_lt_of_le hf hvar
  have hratio : entropy W (fun x => (f x + c) ^ 2) / dirichlet W (fun x => f x + c) ≤
      logSobolevConstant W := le_csSup (entropy_ratios_bdd W hn) ⟨_, he, rfl⟩
  rw [dirichlet_add_const] at hratio
  exact (div_le_div_of_nonneg_right hvar (dirichlet_nonneg W f)).trans hratio

end EntropyFinite

end CriticalSK
end

end OAI
