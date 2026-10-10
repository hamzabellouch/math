import Mathlib
import OAI.Probability.Perceptron.Cascade.PoissonCountMoments

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

lemma summable_nat_mul_pow_div_factorial (r : ℝ) :
    Summable (fun n : ℕ => (n:ℝ)*r^n/(n.factorial:ℝ)) := by
  apply (summable_nat_add_iff 1).mp
  have hs := (Real.summable_pow_div_factorial r).mul_left r
  apply hs.congr
  intro n
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  field_simp

lemma summable_linear_pow_div_factorial (A C r : ℝ) :
    Summable (fun n : ℕ => (A+C*(n:ℝ))*r^n/(n.factorial:ℝ)) := by
  have h := ((Real.summable_pow_div_factorial r).mul_left A).add
    ((summable_nat_mul_pow_div_factorial r).mul_left C)
  apply h.congr
  intro n
  ring

lemma bounded_increment_linear_bound {F : ℕ→ℝ} {C : ℝ} (hC : 0≤C)
    (hF : ∀ n, |F (n+1)-F n|≤C) (n : ℕ) : |F n|≤|F 0|+C*(n:ℝ) := by
  have h := nat_bounded_increment_difference hC hF n 0
  simp only [Nat.cast_zero,sub_zero,Nat.abs_cast] at h
  calc |F n| ≤ |F n-F 0|+|F 0| := by simpa using abs_sub_le (F n) (F 0) 0
       _ ≤ |F 0|+C*(n:ℝ) := by linarith

lemma bounded_increment_factorial_summable {F : ℕ→ℝ} {C : ℝ} (hC : 0≤C)
    (hF : ∀ n, |F (n+1)-F n|≤C) (t : ℝ) :
    Summable (fun n => t^n/(n.factorial:ℝ)*F n) := by
  refine Summable.of_norm_bounded (summable_linear_pow_div_factorial |F 0| C |t|) fun n => ?_
  simp only [Real.norm_eq_abs,abs_mul,abs_div,abs_pow,Nat.abs_cast]
  simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using
    mul_le_mul_of_nonneg_left (bounded_increment_linear_bound hC hF n)
      (show 0≤|t|^n/(n.factorial:ℝ) by positivity)

lemma hasDerivAt_factorial_series {F : ℕ→ℝ} {C : ℝ} (hC : 0≤C)
    (hF : ∀ n, |F (n+1)-F n|≤C) (t : ℝ) :
    HasDerivAt (fun s => ∑' n, s^n/(n.factorial:ℝ)*F n)
      (∑' n, t^n/(n.factorial:ℝ)*F (n+1)) t := by
  let R := |t|+1
  let g := fun n : ℕ => fun s : ℝ => s^(n+1)/((n+1).factorial:ℝ)*F (n+1)
  let g' := fun n : ℕ => fun s : ℝ => s^n/(n.factorial:ℝ)*F (n+1)
  let b := fun n : ℕ => (|F 0|+C+C*(n:ℝ))*R^n/(n.factorial:ℝ)
  have hb : Summable b := summable_linear_pow_div_factorial (|F 0|+C) C R
  have hg : ∀ n s, s∈Ioo (-R) R → HasDerivAt (g n) (g' n s) s := by
    intro n s _
    unfold g g'
    apply HasDerivAt.congr_deriv ((((hasDerivAt_id s).pow (n+1)).div_const ((n+1).factorial:ℝ)).mul_const (F (n+1)))
    simp only [Nat.add_sub_cancel,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_one]
    field_simp
    simp [id_eq,mul_comm]
  have hbound : ∀ n s, s∈Ioo (-R) R → ‖g' n s‖≤b n := by
    intro n s hs
    have ha : |s|≤R := (abs_le.mpr ⟨hs.1.le,hs.2.le⟩)
    have hf := bounded_increment_linear_bound hC hF (n+1)
    simp only [Nat.cast_add,Nat.cast_one] at hf
    simp only [g',b,Real.norm_eq_abs,abs_mul,abs_div,abs_pow,Nat.abs_cast]
    calc _ ≤ (R^n/(n.factorial:ℝ))*(|F 0|+C+C*(n:ℝ)) := by
            apply mul_le_mul
            · exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) ha _) (by positivity)
            · linarith
            · positivity
            · positivity
         _ = _ := by ring
  have hz : (0:ℝ)∈Ioo (-R) R := by dsimp [R]; constructor <;> linarith [abs_nonneg t]
  have ht : t∈Ioo (-R) R := by dsimp [R]; constructor <;> linarith [le_abs_self t,neg_abs_le t]
  have hzero : Summable (fun n => g n 0) := by simp [g]
  have hd := hasDerivAt_tsum_of_isPreconnected hb isOpen_Ioo (convex_Ioo (-R) R).isPreconnected
    hg hbound hz hzero ht
  have he : ∀ s : ℝ, (F 0+(∑' n, g n s))=(∑' n, s^n/(n.factorial:ℝ)*F n) := by
    intro s
    rw [tsum_eq_zero_add' ((summable_nat_add_iff 1).mpr (bounded_increment_factorial_summable hC hF s))]
    simp [g]
  have hh := hd.const_add (F 0)
  simp_rw [he] at hh
  exact hh

def poissonRealMean (F : ℕ→ℝ) (t : ℝ) : ℝ :=
  Real.exp (-t)*(∑' n, t^n/(n.factorial:ℝ)*F n)

lemma poissonRealMean_eq_integral {F : ℕ→ℝ} {C : ℝ} (hC : 0≤C)
    (hF : ∀ n, |F (n+1)-F n|≤C) (t : ℝ≥0) :
    poissonRealMean F t = ∫ n, F n ∂poissonMeasure t := by
  rw [integral_countable ((poisson_bounded_increment_memLp t hC hF).integrable (by norm_num))]
  simp only [poissonMeasure_real_singleton,smul_eq_mul,poissonRealMean]
  rw [← tsum_mul_left]
  congr 1
  ext n
  ring

lemma hasDerivAt_poissonRealMean {F : ℕ→ℝ} {C : ℝ} (hC : 0≤C)
    (hF : ∀ n, |F (n+1)-F n|≤C) (t : ℝ) :
    HasDerivAt (poissonRealMean F)
      (poissonRealMean (fun n => F (n+1)-F n) t) t := by
  have hs := bounded_increment_factorial_summable hC hF t
  have hs' := bounded_increment_factorial_summable (F := fun n => F (n+1)) hC (fun n => hF (n+1)) t
  have hd := (((hasDerivAt_id t).neg).exp).mul (hasDerivAt_factorial_series hC hF t)
  apply hd.congr_deriv
  simp only [poissonRealMean,mul_sub,hs'.tsum_sub hs,Pi.neg_apply,id_eq]
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
