import Mathlib
import OAI.Probability.SKRatio.Calculus.GibbsMeanCLM

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap MeasureTheory Filter
namespace SKRatio.Calculus

lemma energy_early_late_averaging (G : ℝ → ℝ) (hcontinuous : Continuous G)
    {t s a R : ℝ} (ht : 0 ≤ t) (hs : 0 < s) (ha : 0 ≤ a)
    (hnonneg : ∀ u ∈ Set.Icc (0:ℝ) (t+s), 0 ≤ G u)
    (hbudget : (∫ u in (0:ℝ)..(t+s), G u) ≤ 1/2)
    (hcompare : ∀ u ∈ Set.Icc (0:ℝ) t,
      ∀ z ∈ Set.Icc (t+s/2) (t+s), G u ≤ a*G z+R) :
    (∫ u in (0:ℝ)..t, G u) ≤ t*(a/s+R) := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hcontinuous.intervalIntegrable 0 (t+s/2))
    (hcontinuous.intervalIntegrable (t+s/2) (t+s))
  have hfirst : 0 ≤ ∫ u in (0:ℝ)..(t+s/2), G u := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro u hu
    exact hnonneg u ⟨hu.1, by linarith [hu.2]⟩
  have hlate : (∫ u in (t+s/2)..(t+s), G u) ≤ 1/2 := by
    linarith only [hsplit, hfirst, hbudget]
  have hearly (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) t) : G u ≤ a/s+R := by
    have hi := intervalIntegral.integral_mono_on (μ := volume) (by linarith : t+s/2 ≤ t+s)
      (continuous_const.intervalIntegrable (t+s/2) (t+s))
      ((hcontinuous.const_mul a |>.add_const R).intervalIntegrable (t+s/2) (t+s))
      (hcompare u hu)
    rw [intervalIntegral.integral_const,
      intervalIntegral.integral_add ((hcontinuous.const_mul a).intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hi
    simp only [smul_eq_mul] at hi
    have hlate' := mul_le_mul_of_nonneg_left hlate ha
    have heq : s*(a/s)=a := by field_simp
    nlinarith only [hi, hlate', heq, hs]
  calc
    _ ≤ ∫ _u in (0:ℝ)..t, (a/s+R) :=
      intervalIntegral.integral_mono_on ht (hcontinuous.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) hearly
    _ = _ := by rw [intervalIntegral.integral_const]; simp

theorem transient_variance_of_energy_comparison {n : ℕ} (J : Interaction n)
    (f : Observables n) (hf : ∀ y, |f y| ≤ 1) (x : Spin n)
    {t s a R : ℝ} (ht : 0 ≤ t) (hs : 0 < s) (ha : 0 ≤ a)
    (hcompare : ∀ u ∈ Set.Icc (0:ℝ) t,
      ∀ z ∈ Set.Icc (t+s/2) (t+s),
      backwardEnergy J f x (t+s) u ≤ a*backwardEnergy J f x (t+s) z+R) :
    FiniteLaw.variance (continuousKernel J t x) (semigroup J s f) ≤
      2*t*(a/s+R) := by
  have H := energy_early_late_averaging (backwardEnergy J f x (t+s))
    (backwardEnergy_continuous J f x (t+s)) ht hs ha
    (fun u hu => backwardEnergy_nonneg J f x (t+s) u hu.1)
    (backward_energy_budget J f hf x (by linarith)) hcompare
  have hv := backward_variance_budget J f x (t+s) t
  rw [show t+s-t = s by ring] at hv
  rw [hv]
  linarith only [H]

def stationaryEnergy {n : ℕ} (g : Disorder n) (f : Observables n) : ℝ :=
  FiniteLaw.mean (mass g 0) (weightedGradient (coupling g) f)

lemma stationaryEnergy_nonneg {n : ℕ} (g : Disorder n) (f : Observables n) :
    0 ≤ stationaryEnergy g f := by
  exact Finset.sum_nonneg (fun x _ =>
    mul_nonneg (mass_nonneg g 0 x) (weightedGradient_nonneg _ f x))

lemma stationaryEnergy_eq {n : ℕ} (g : Disorder n) (f : Observables n) :
    stationaryEnergy g f =
      -FiniteLaw.mean (mass g 0) (fun x => f x*generator (coupling g) f x) := by
  have hg : generator (coupling g) (fun x => f x^2) =
      (2:ℝ) • ((fun x => f x*generator (coupling g) f x) +
        weightedGradient (coupling g) f) := by
    funext x
    change generator (coupling g) (fun y => f y^2) x =
      2*(f x*generator (coupling g) f x + weightedGradient (coupling g) f x)
    have h := variance_density (coupling g) f x
    linarith only [h]
  have h := congrArg (gibbsMeanCLM g) hg
  rw [gibbsMean_generator, map_smul, map_add] at h
  simp only [gibbsMeanCLM_apply, smul_eq_mul] at h
  unfold stationaryEnergy
  linarith only [h]

lemma equilibrium_variance_hasDerivAt {n : ℕ} (g : Disorder n) (f : Observables n)
    (t : ℝ) :
    HasDerivAt (fun r => FiniteLaw.variance (mass g 0) (semigroup (coupling g) r f))
      (-2*stationaryEnergy g (semigroup (coupling g) t f)) t := by
  have hsq : HasDerivAt (fun r : ℝ => fun x : Spin n => (semigroup (coupling g) r f x)^2)
      (fun x => 2*semigroup (coupling g) t f x*
        generator (coupling g) (semigroup (coupling g) t f) x) t := by
    apply hasDerivAt_pi.mpr
    intro x
    have h := (hasDerivAt_pi.mp (semigroup_apply_hasDerivAt' (coupling g) f t) x).fun_pow 2
    convert h using 1
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  have hm := (gibbsMeanCLM g).hasFDerivAt.comp_hasDerivAt t hsq
  have hm' := hm.sub_const ((FiniteLaw.mean (mass g 0) f)^2)
  have heq : (fun r => FiniteLaw.variance (mass g 0) (semigroup (coupling g) r f)) =
      (fun r => gibbsMeanCLM g (fun x => (semigroup (coupling g) r f x)^2) -
        (FiniteLaw.mean (mass g 0) f)^2) := by
    funext r
    rw [FiniteLaw.variance_eq _ _ (sum_mass g 0), gibbsMean_semigroup, gibbsMeanCLM_apply]
  rw [heq]
  apply hm'.congr_deriv
  rw [stationaryEnergy_eq]
  simp only [gibbsMeanCLM_apply, FiniteLaw.mean, mul_neg, neg_mul, neg_neg, Finset.mul_sum, Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem equilibrium_variance_decay {n : ℕ} (g : Disorder n) {γ : ℝ}
    (hgap : ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (f : Observables n) {s : ℝ} (hs : 0 ≤ s) :
    FiniteLaw.variance (mass g 0) (semigroup (coupling g) s f) ≤
      Real.exp (-2*γ*s)*FiniteLaw.variance (mass g 0) f := by
  let V (r : ℝ) := FiniteLaw.variance (mass g 0) (semigroup (coupling g) r f)
  let E (r : ℝ) := stationaryEnergy g (semigroup (coupling g) r f)
  let H (r : ℝ) := Real.exp (2*γ*r)*V r
  have hderiv (r : ℝ) : HasDerivAt H (Real.exp (2*γ*r)*(2*γ*V r-2*E r)) r := by
    have h := (((hasDerivAt_id r).const_mul (2*γ)).exp).mul
      (equilibrium_variance_hasDerivAt g f r)
    convert h using 1 <;> first | rfl | (dsimp [V, E]; ring)
  have hanti : Antitone H := antitone_of_deriv_nonpos
    (fun r => (hderiv r).differentiableAt) (fun r => by
      rw [(hderiv r).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) (by
        have h := hgap (semigroup (coupling g) r f)
        change γ*V r ≤ E r at h
        linarith only [h]))
  have h := hanti hs
  have hzero : H 0 = FiniteLaw.variance (mass g 0) f := by
    simp [H, V]
  rw [hzero] at h
  have hscaled := mul_le_mul_of_nonneg_left h (Real.exp_nonneg (-2*γ*s))
  calc
    V s = Real.exp (-2*γ*s)*H s := by
      dsimp [H]
      rw [← mul_assoc, ← Real.exp_add, show -2*γ*s+2*γ*s=0 by ring, Real.exp_zero, one_mul]
    _ ≤ _ := hscaled

lemma equilibrium_variance_le_one {n : ℕ} (g : Disorder n) (f : Observables n)
    (hf : ∀ x, |f x| ≤ 1) : FiniteLaw.variance (mass g 0) f ≤ 1 := by
  have hle : FiniteLaw.mean (mass g 0) (fun x => f x^2) ≤ 1 := by
    calc
      _ ≤ ∑ x : Spin n, mass g 0 x*1 :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
          ((sq_le_one_iff_abs_le_one _).mpr (hf x)) (mass_nonneg g 0 x))
      _ = _ := by simp [sum_mass]
  rw [FiniteLaw.variance_eq _ _ (sum_mass g 0)]
  linarith only [hle, sq_nonneg (FiniteLaw.mean (mass g 0) f)]

theorem equilibrium_smoothing {n : ℕ} (g : Disorder n) {γ : ℝ}
    (hgap : ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (f : Observables n) (hf : ∀ x, |f x| ≤ 1) {s : ℝ} (hs : 0 ≤ s) :
    FiniteLaw.variance (mass g 0) (semigroup (coupling g) s f) ≤ Real.exp (-2*γ*s) := by
  exact (equilibrium_variance_decay g hgap f hs).trans
    ((mul_le_mul_of_nonneg_left (equilibrium_variance_le_one g f hf)
      (Real.exp_nonneg _)).trans_eq (mul_one _))

theorem smoothing_of_energy_comparison {n : ℕ} (g : Disorder n)
    {t s a R γ ε : ℝ} (ht : 0 ≤ t) (hs : 0 < s) (ha : 0 ≤ a) (hε : 0 < ε)
    (hoverlap : continuousDistance g t ≤ 1-ε)
    (hgap : ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (hcompare : ∀ (f : Observables n), (∀ y, |f y| ≤ 1) →
      ∀ (x : Spin n), ∀ u ∈ Set.Icc (0:ℝ) t,
      ∀ z ∈ Set.Icc (t+s/2) (t+s),
      backwardEnergy (coupling g) f x (t+s) u ≤
        a*backwardEnergy (coupling g) f x (t+s) z+R) :
    continuousDistance g (t+s) ≤
      (Real.sqrt (2*t*(a/s+R))+Real.exp (-γ*s))/(2*Real.sqrt ε) := by
  have h := continuousDistance_smoothing g ht hε hoverlap
    (fun x f hf => transient_variance_of_energy_comparison (coupling g)
      f hf x ht hs ha (hcompare f hf x))
    (fun f hf => equilibrium_smoothing g hgap f hf hs.le)
  have heq : Real.sqrt (Real.exp (-2*γ*s)) = Real.exp (-γ*s) := by
    rw [show -2*γ*s = (2:ℕ)*(-γ*s) by push_cast; ring,
      Real.exp_nat_mul, Real.sqrt_sq (Real.exp_nonneg _)]
  rwa [heq] at h

end SKRatio.Calculus

end
end

end OAI
