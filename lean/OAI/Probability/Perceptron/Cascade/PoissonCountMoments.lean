import Mathlib
import OAI.Probability.Perceptron.Variational.StableLogIntensity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

lemma poisson_nat_lintegral (r : ℝ≥0) :
    (∫⁻ m : ℕ, ENNReal.ofReal (m:ℝ) ∂poissonMeasure r)=r := by
  simp_rw [ENNReal.ofReal_natCast]
  rw [lintegral_countable']
  simpa only [mul_comm] using poissonMeasure_mean r

lemma poisson_natSquare_lintegral (r : ℝ≥0) :
    (∫⁻ m : ℕ, ENNReal.ofReal ((m:ℝ)^2) ∂poissonMeasure r)=(r:ℝ≥0∞)^2+r := by
  have hmass : (∑' m : ℕ, poissonMeasure r {m})=1 := by
    simpa using (lintegral_countable' (μ := poissonMeasure r) (fun _ => (1:ℝ≥0∞))).symm
  simp_rw [ENNReal.ofReal_pow (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
  rw [lintegral_countable']
  simp_rw [mul_comm ((_:ℝ≥0∞)^2)]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,zero_add]
  have hterm (m : ℕ) : poissonMeasure r {m+1} * ((m+1:ℕ):ℝ≥0∞)^2=
      (r:ℝ≥0∞)*(poissonMeasure r {m}*(m:ℝ≥0∞))+(r:ℝ≥0∞)*poissonMeasure r {m} := by
    rw [pow_two,← mul_assoc]
    simp only [Nat.cast_add,Nat.cast_one]
    rw [poissonMeasure_atom_succ]
    ring
  simp_rw [hterm]
  rw [ENNReal.tsum_add,ENNReal.tsum_mul_left,ENNReal.tsum_mul_left,
    poissonMeasure_mean,hmass,mul_one,pow_two]

lemma poisson_nat_memLp (r : ℝ≥0) : MemLp (fun m : ℕ => (m:ℝ)) 2 (poissonMeasure r) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  refine ⟨by fun_prop,(hasFiniteIntegral_iff_norm _).mpr ?_⟩
  simp only [Real.norm_eq_abs,abs_sq]
  rw [poisson_natSquare_lintegral]
  finiteness

lemma poisson_nat_mean (r : ℝ≥0) : (∫ m : ℕ, (m:ℝ) ∂poissonMeasure r)=r := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun m => Nat.cast_nonneg m) (by fun_prop),
    poisson_nat_lintegral,ENNReal.coe_toReal]

lemma poisson_nat_square_mean (r : ℝ≥0) :
    (∫ m : ℕ, (m:ℝ)^2 ∂poissonMeasure r)=(r:ℝ)^2+r := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun m : ℕ => sq_nonneg (m:ℝ)) (by fun_prop),
    poisson_natSquare_lintegral,ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_pow,ENNReal.coe_toReal]

lemma poisson_nat_variance (r : ℝ≥0) : variance (fun m : ℕ => (m:ℝ)) (poissonMeasure r)=r := by
  rw [variance_eq_sub (poisson_nat_memLp r)]
  simp only [Pi.pow_apply,poisson_nat_mean,poisson_nat_square_mean]
  ring

lemma poisson_nat_center_square (r : ℝ≥0) (a : ℝ) :
    (∫ m : ℕ, ((m:ℝ)-a)^2 ∂poissonMeasure r)=(r:ℝ)+((r:ℝ)-a)^2 := by
  have hi := (poisson_nat_memLp r).integrable (by norm_num)
  have hs := (poisson_nat_memLp r).integrable_sq
  have he (m : ℕ) : ((m:ℝ)-a)^2=(m:ℝ)^2-2*a*(m:ℝ)+a^2 := by ring
  simp_rw [he]
  rw [integral_add (f := fun m : ℕ => (m:ℝ)^2-2*a*(m:ℝ))
      (g := fun _ : ℕ => a^2) (hs.sub (hi.const_mul (2*a))) (integrable_const _),
    integral_sub (f := fun m : ℕ => (m:ℝ)^2) (g := fun m : ℕ => 2*a*(m:ℝ))
      hs (hi.const_mul (2*a)),integral_const_mul]
  simp only [poisson_nat_mean,poisson_nat_square_mean]
  simp
  ring

lemma nat_bounded_increment_difference {F : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ m, |F (m+1)-F m| ≤ C) (m n : ℕ) :
    |F m-F n| ≤ C*|(m:ℝ)-(n:ℝ)| := by
  have hle (m n : ℕ) (hmn : m ≤ n) : |F n-F m| ≤ C*((n:ℝ)-(m:ℝ)) := by
    induction n,hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have ht := abs_sub_le (F (n+1)) (F n) (F m)
      have hh := hF n
      push_cast
      linarith
  rcases le_total m n with hmn|hnm
  · rw [abs_sub_comm (F m),abs_sub_comm (m:ℝ)]
    exact (hle m n hmn).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC)
  · exact (hle n m hnm).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC)

lemma poisson_bounded_increment_memLp (r : ℝ≥0) {F : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ m, |F (m+1)-F m| ≤ C) : MemLp F 2 (poissonMeasure r) := by
  have hi : MemLp (fun m : ℕ => |F 0|+C*(m:ℝ)) 2 (poissonMeasure r) :=
    (memLp_const (μ := poissonMeasure r) |F 0|).add ((poisson_nat_memLp r).const_mul C)
  refine hi.mono (measurable_of_countable F).aestronglyMeasurable (ae_of_all _ fun m => ?_)
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (show (0:ℝ) ≤ |F 0|+C*(m:ℝ) by positivity)]
  have hh := nat_bounded_increment_difference hC hF m 0
  simp only [Nat.cast_zero,sub_zero,abs_of_nonneg (show (0:ℝ) ≤ (m:ℝ) from Nat.cast_nonneg m)] at hh
  have ht := abs_sub_le (F m) (F 0) 0
  simp only [sub_zero] at ht
  linarith

lemma poisson_bounded_increment_variance (r : ℝ≥0) {F : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ m, |F (m+1)-F m| ≤ C) :
    variance F (poissonMeasure r) ≤ C^2*((r:ℝ)+1) := by
  let a : ℕ := ⌊(r:ℝ)⌋₊
  have hp := poisson_bounded_increment_memLp r hC hF
  have hv := variance_le_expectation_sq ((hp.sub (memLp_const (F a))).aestronglyMeasurable)
  change variance (fun m => F m-F a) (poissonMeasure r) ≤
    ∫ m, (F m-F a)^2 ∂poissonMeasure r at hv
  rw [variance_sub_const hp.aestronglyMeasurable] at hv
  have hc : Integrable (fun m : ℕ => C^2*((m:ℝ)-(a:ℝ))^2) (poissonMeasure r) :=
    ((poisson_nat_memLp r).sub (memLp_const (a:ℝ))).integrable_sq.const_mul _
  have hd : (∫ m, (F m-F a)^2 ∂poissonMeasure r) ≤
      C^2*((r:ℝ)+((r:ℝ)-(a:ℝ))^2) := by
    calc
      _ ≤ ∫ m : ℕ, C^2*((m:ℝ)-(a:ℝ))^2 ∂poissonMeasure r := by
        apply integral_mono (hp.sub (memLp_const (F a))).integrable_sq hc
        intro m
        have hh := nat_bounded_increment_difference hC hF m a
        have hs := pow_le_pow_left₀ (abs_nonneg _) hh 2
        simpa only [sq_abs,mul_pow,Pi.sub_apply] using hs
      _ = _ := by rw [integral_const_mul,poisson_nat_center_square]
  have hfloor : (a:ℝ) ≤ (r:ℝ) := Nat.floor_le r.coe_nonneg
  have hceil : (r:ℝ) < (a:ℝ)+1 := Nat.lt_floor_add_one (r:ℝ)
  have hsq : ((r:ℝ)-(a:ℝ))^2 ≤ 1 := by nlinarith
  exact hv.trans (hd.trans (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg C)))

end SphericalPerceptronFreeEnergy
end

end OAI
