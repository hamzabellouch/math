import Mathlib
import OAI.Probability.SKGap.Localization.Magnetization

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
namespace SKGapCutoff

lemma semigroup_hasDerivAt {n : ℕ} (J : Interaction n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => semigroup J s)
      (semigroup J t * generatorCLM J) t :=
  hasDerivAt_exp_smul_const (generatorCLM J) t

lemma semigroup_hasDerivAt' {n : ℕ} (J : Interaction n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => semigroup J s)
      (generatorCLM J * semigroup J t) t :=
  hasDerivAt_exp_smul_const' (generatorCLM J) t

lemma semigroup_apply_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => semigroup J s f) (semigroup J t (generator J f)) t := by
  simpa only [mul_apply_eq_comp, map_zero, add_zero, generatorCLM, generatorLM,
    LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk] using
    (semigroup_hasDerivAt J t).clm_apply (hasDerivAt_const t f)

lemma semigroup_apply_hasDerivAt' {n : ℕ} (J : Interaction n) (f : Observables n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => semigroup J s f) (generator J (semigroup J t f)) t := by
  simpa only [mul_apply_eq_comp, map_zero, add_zero, generatorCLM, generatorLM,
    LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk] using
    (semigroup_hasDerivAt' J t).clm_apply (hasDerivAt_const t f)

lemma semigroup_continuous {n : ℕ} (J : Interaction n) :
    Continuous (fun s : ℝ => semigroup J s) := by
  have hd : Differentiable ℝ (fun s : ℝ => semigroup J s) :=
    fun t => (semigroup_hasDerivAt J t).differentiableAt
  exact hd.continuous

@[simp] lemma semigroup_zero {n : ℕ} (J : Interaction n) : semigroup J 0 = 1 := by
  simp [semigroup]

noncomputable def jumpEnergy {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) : ℝ :=
  2 * ∑ i, (1 - mean J x i * spin x i) * (halfDiff i f x) ^ 2

lemma generator_square {n : ℕ} (J : Interaction n) (f : Observables n) :
    generator J (fun x => f x ^ 2) =
      fun x => 2 * f x * generator J f x + jumpEnergy J f x := by
  funext x
  simpa only [pow_two, mul_assoc, ← two_mul, jumpEnergy] using generator_mul J f f x

lemma backward_flow_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n) (d s : ℝ) :
    HasDerivAt (fun r : ℝ => semigroup J (d - r) f)
      (fun x => -generator J (semigroup J (d - s) f) x) s := by
  have h := (semigroup_apply_hasDerivAt' J f (d - s)).scomp s
    ((hasDerivAt_id s).const_sub d)
  simpa only [id_eq, neg_smul, one_smul, Pi.neg_def, Function.comp_def] using h

lemma backward_square_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n) (d s : ℝ) :
    HasDerivAt (fun r : ℝ => fun x : Spin n => (semigroup J (d - r) f x) ^ 2)
      (fun x => -2 * semigroup J (d - s) f x * generator J (semigroup J (d - s) f) x) s := by
  apply hasDerivAt_pi.mpr
  intro x
  have h := (hasDerivAt_pi.mp (backward_flow_hasDerivAt J f d s) x).pow 2
  have he : (2 : ℝ) * semigroup J (d - s) f x *
      -generator J (semigroup J (d - s) f) x =
      -2 * semigroup J (d - s) f x * generator J (semigroup J (d - s) f) x := by ring
  convert h using 1
  simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using he.symm

lemma interpolated_square_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n) (d s : ℝ) :
    HasDerivAt (fun r : ℝ => semigroup J r
      (fun x => (semigroup J (d - r) f x) ^ 2))
      (semigroup J s (jumpEnergy J (semigroup J (d - s) f))) s := by
  have h := (semigroup_hasDerivAt J s).clm_apply (backward_square_hasDerivAt J f d s)
  apply h.congr_deriv
  simp only [mul_apply_eq_comp]
  change semigroup J s (generator J (fun x => semigroup J (d - s) f x ^ 2)) +
    semigroup J s (fun x => -2 * semigroup J (d - s) f x *
      generator J (semigroup J (d - s) f) x) = _
  rw [← map_add]
  congr 1
  funext x
  rw [generator_square]
  simp only [Pi.add_apply]
  ring

lemma jumpEnergy_continuous {n : ℕ} (J : Interaction n) :
    Continuous (jumpEnergy J) := by
  unfold jumpEnergy halfDiff
  fun_prop

lemma interpolated_energy_continuous {n : ℕ} (J : Interaction n) (f : Observables n)
    (d : ℝ) (x : Spin n) :
    Continuous (fun s : ℝ => semigroup J s (jumpEnergy J (semigroup J (d - s) f)) x) := by
  have hc : Continuous (fun s : ℝ => semigroup J (d - s) f) :=
    ((semigroup_continuous J).comp (continuous_const.sub continuous_id)).clm_apply continuous_const
  exact continuous_apply x |>.comp ((semigroup_continuous J).clm_apply
    ((jumpEnergy_continuous J).comp hc))

lemma semigroup_variance_integral {n : ℕ} (J : Interaction n) (f : Observables n)
    (d : ℝ) (x : Spin n) :
    semigroup J d (fun y => f y ^ 2) x - (semigroup J d f x) ^ 2 =
      ∫ s in (0 : ℝ)..d, semigroup J s (jumpEnergy J (semigroup J (d - s) f)) x := by
  have hd (s : ℝ) := hasDerivAt_pi.mp (interpolated_square_hasDerivAt J f d s) x
  have hi := (interpolated_energy_continuous J f d x).intervalIntegrable
    (μ := MeasureTheory.volume) 0 d
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi
  simpa only [sub_self, sub_zero, semigroup_zero, one_apply_eq_self] using he.symm

lemma jumpWeight_bounds {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    0 ≤ 1 - mean J x i * spin x i ∧ 1 - mean J x i * spin x i ≤ 2 := by
  have hl := Real.neg_one_lt_tanh (field J x i)
  have hu := Real.tanh_lt_one (field J x i)
  cases hs : x i <;> simp only [spin, hs, Bool.false_eq_true, ↓reduceIte, mul_one,
    mul_neg, sub_neg_eq_add, mean] <;> constructor <;> linarith

lemma jumpEnergy_nonneg {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) :
    0 ≤ jumpEnergy J f x := by
  unfold jumpEnergy
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg
    (fun i _ => mul_nonneg (jumpWeight_bounds J x i).1 (sq_nonneg _)))

lemma jumpEnergy_le_gradient {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) :
    jumpEnergy J f x ≤ 4 * ∑ i, (halfDiff i f x) ^ 2 := by
  unfold jumpEnergy
  calc
    _ ≤ 2 * ∑ i, 2 * (halfDiff i f x) ^ 2 := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum _) (by norm_num)
      intro i _
      exact mul_le_mul_of_nonneg_right (jumpWeight_bounds J x i).2 (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

lemma semigroup_mono {n : ℕ} (J : Interaction n) (t : ℝ) (ht : 0 ≤ t)
    {f g : Observables n} (hfg : ∀ x, f x ≤ g x) (x : Spin n) :
    semigroup J t f x ≤ semigroup J t g x := by
  have h := semigroup_nonneg J t ht (g - f) (fun x => sub_nonneg.mpr (hfg x)) x
  simpa only [map_sub, Pi.sub_apply, sub_nonneg] using h

lemma semigroup_le_const {n : ℕ} (J : Interaction n) (t : ℝ) (ht : 0 ≤ t)
    {f : Observables n} {C : ℝ} (hf : ∀ x, f x ≤ C) (x : Spin n) :
    semigroup J t f x ≤ C := by
  simpa only [semigroup_const] using semigroup_mono J t ht hf x

theorem semigroup_variance_le {n : ℕ} (J : Interaction n) (f : Observables n)
    (d : ℝ) (hd : 0 ≤ d) (b : ℝ → ℝ)
    (hb : IntervalIntegrable b MeasureTheory.volume 0 d)
    (hbound : ∀ r ∈ Set.Icc (0 : ℝ) d, ∀ x, ∑ i, (halfDiff i (semigroup J r f) x) ^ 2 ≤ b r)
    (x : Spin n) :
    semigroup J d (fun y => f y ^ 2) x - (semigroup J d f x) ^ 2 ≤
      4 * ∫ r in (0 : ℝ)..d, b r := by
  rw [semigroup_variance_integral]
  have hbr : IntervalIntegrable (fun s => b (d - s)) MeasureTheory.volume 0 d := by
    simpa only [sub_self, sub_zero] using (hb.comp_sub_left d).symm
  calc
    _ ≤ ∫ s in (0 : ℝ)..d, 4 * b (d - s) := by
      apply intervalIntegral.integral_mono_on hd
        ((interpolated_energy_continuous J f d x).intervalIntegrable 0 d)
        (hbr.const_mul 4)
      intro s hs
      apply semigroup_le_const J s hs.1
      intro y
      exact (jumpEnergy_le_gradient J (semigroup J (d - s) f) y).trans
        (mul_le_mul_of_nonneg_left (hbound (d - s) ⟨sub_nonneg.mpr hs.2, by linarith [hs.1]⟩ y)
          (by norm_num))
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left]
      simp only [sub_self, sub_zero]

end SKGapCutoff

lemma real_exp_remainder_le (z : ℝ) :
    Real.exp z - 1 - z ≤ z ^ 2 * Real.exp |z| / 2 := by
  by_cases hz : z = 0
  · simp [hz]
  have hn : (0 : ℝ) ≠ z := Ne.symm hz
  obtain ⟨u, hu, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) (f := Real.exp) hn Real.contDiff_exp.contDiffOn
  have hd : derivWithin Real.exp (Set.uIcc 0 z) 0 = 1 := by
    simpa using (Real.hasDerivAt_exp 0).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_uIcc hn) 0 (Set.left_mem_uIcc))
  have hi : iteratedDeriv 2 Real.exp = Real.exp := by
    simpa using iteratedDeriv_exp_const_mul 2 (1 : ℝ)
  simp [taylorWithinEval_succ, iteratedDerivWithin_one, hd, hi] at he
  have hu' : u ≤ |z| := by
    calc
      u ≤ max 0 z := le_of_lt hu.2
      _ ≤ |z| := max_le (abs_nonneg _) (le_abs_self _)
  calc
    Real.exp z - 1 - z = Real.exp u * z ^ 2 / 2 := by linarith [he]
    _ ≤ z ^ 2 * Real.exp |z| / 2 := by
      have h := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hu') (sq_nonneg z)
      nlinarith

open scoped BigOperators

end

end OAI
