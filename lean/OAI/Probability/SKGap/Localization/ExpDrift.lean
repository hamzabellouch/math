import Mathlib
import OAI.Probability.SKGap.Terminal.GibbsExpectation
import OAI.Probability.SKGap.Localization.JumpEnergy

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
namespace SKGapCutoff

noncomputable def expDrift {n : ℕ} (J : Interaction n) (θ : ℝ)
    (f : Observables n) (x : Spin n) : ℝ :=
  generator J (fun y => Real.exp (θ * f y)) x -
    θ * Real.exp (θ * f x) * generator J f x

lemma expDrift_eq_sum {n : ℕ} (J : Interaction n) (θ : ℝ) (f : Observables n) (x : Spin n) :
    expDrift J θ f x = Real.exp (θ * f x) * ∑ i, flipRate J x i *
      (Real.exp (θ * (f (flip x i) - f x)) - 1 - θ * (f (flip x i) - f x)) := by
  have he (i : Fin n) : Real.exp (θ * f (flip x i)) =
      Real.exp (θ * f x) * Real.exp (θ * (f (flip x i) - f x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [expDrift, generator_flip, he, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma flipRate_nonneg {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    0 ≤ flipRate J x i := by
  unfold flipRate
  exact div_nonneg (by simpa only [mul_comm] using (jumpWeight_bounds J x i).1) (by norm_num)

lemma jumpEnergy_eq_jump_square {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) :
    jumpEnergy J f x = ∑ i, flipRate J x i * (f (flip x i) - f x) ^ 2 := by
  simp only [jumpEnergy, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [flip_sub]
  simp only [mul_pow, spin_sq, mul_one, flipRate]
  ring

lemma abs_flip_sub_le {n : ℕ} (f : Observables n) (x : Spin n) (B : ℝ)
    (hB : ∑ j, (halfDiff j f x) ^ 2 ≤ B) (i : Fin n) :
    |f (flip x i) - f x| ≤ 2 * Real.sqrt B := by
  have hi : (halfDiff i f x) ^ 2 ≤ B :=
    (Finset.single_le_sum (fun j _ => sq_nonneg (halfDiff j f x)) (Finset.mem_univ i)).trans hB
  have hs : |spin x i| = 1 := by cases hx : x i <;> simp [spin, hx]
  rw [flip_sub, abs_mul, abs_mul, hs]
  norm_num
  exact Real.abs_le_sqrt hi

lemma expDrift_le {n : ℕ} (J : Interaction n) (θ : ℝ) (f : Observables n) (x : Spin n)
    (B b : ℝ) (hB : ∑ i, (halfDiff i f x) ^ 2 ≤ B)
    (hb : ∑ i, (halfDiff i f x) ^ 2 ≤ b) :
    expDrift J θ f x ≤ (2 * θ ^ 2 * Real.exp (2 * |θ| * Real.sqrt B) * b) *
      Real.exp (θ * f x) := by
  let R := Real.exp (2 * |θ| * Real.sqrt B)
  have hR : 0 ≤ θ ^ 2 * R / 2 := by positivity
  have hrem (i : Fin n) :
      Real.exp (θ * (f (flip x i) - f x)) - 1 - θ * (f (flip x i) - f x) ≤
        θ ^ 2 * R / 2 * (f (flip x i) - f x) ^ 2 := by
    have ha : |θ * (f (flip x i) - f x)| ≤ 2 * |θ| * Real.sqrt B := by
      rw [abs_mul]
      calc
        _ ≤ |θ| * (2 * Real.sqrt B) :=
          mul_le_mul_of_nonneg_left (abs_flip_sub_le f x B hB i) (abs_nonneg θ)
        _ = _ := by ring
    calc
      _ ≤ (θ * (f (flip x i) - f x)) ^ 2 *
          Real.exp |θ * (f (flip x i) - f x)| / 2 := real_exp_remainder_le _
      _ ≤ (θ * (f (flip x i) - f x)) ^ 2 * R / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ha) (sq_nonneg _)
      _ = _ := by ring
  rw [expDrift_eq_sum]
  calc
    _ ≤ Real.exp (θ * f x) * ∑ i, flipRate J x i *
        (θ ^ 2 * R / 2 * (f (flip x i) - f x) ^ 2) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum _) (Real.exp_pos _).le
      intro i _
      exact mul_le_mul_of_nonneg_left (hrem i) (flipRate_nonneg J x i)
    _ = Real.exp (θ * f x) * (θ ^ 2 * R / 2) * jumpEnergy J f x := by
      rw [jumpEnergy_eq_jump_square]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ Real.exp (θ * f x) * (θ ^ 2 * R / 2) * (4 * b) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.exp_pos _).le hR)
      exact (jumpEnergy_le_gradient J f x).trans (mul_le_mul_of_nonneg_left hb (by norm_num))
    _ = _ := by dsimp [R]; ring

lemma backward_exp_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n)
    (θ d s : ℝ) :
    HasDerivAt (fun r : ℝ => fun x : Spin n => Real.exp (θ * semigroup J (d - r) f x))
      (fun x => -θ * Real.exp (θ * semigroup J (d - s) f x) *
        generator J (semigroup J (d - s) f) x) s := by
  apply hasDerivAt_pi.mpr
  intro x
  have h := ((hasDerivAt_pi.mp (backward_flow_hasDerivAt J f d s) x).const_mul θ).exp
  convert h using 1
  ring

lemma interpolated_exp_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n)
    (θ d s : ℝ) :
    HasDerivAt (fun r : ℝ => semigroup J r
      (fun x => Real.exp (θ * semigroup J (d - r) f x)))
      (semigroup J s (expDrift J θ (semigroup J (d - s) f))) s := by
  have h := (semigroup_hasDerivAt J s).clm_apply (backward_exp_hasDerivAt J f θ d s)
  apply h.congr_deriv
  simp only [mul_apply_eq_comp]
  change semigroup J s (generator J (fun x => Real.exp (θ * semigroup J (d - s) f x))) +
    semigroup J s (fun x => -θ * Real.exp (θ * semigroup J (d - s) f x) *
      generator J (semigroup J (d - s) f) x) = _
  rw [← map_add]
  congr 1
  funext x
  simp only [Pi.add_apply, expDrift]
  ring

lemma semigroup_pos {n : ℕ} (J : Interaction n) (t : ℝ) (ht : 0 ≤ t)
    {f : Observables n} (hf : ∀ x, 0 < f x) (x : Spin n) : 0 < semigroup J t f x := by
  obtain ⟨y, _, hy⟩ := Finset.exists_min_image (Finset.univ : Finset (Spin n)) f
    Finset.univ_nonempty
  have h := semigroup_mono J t ht (fun z => hy z (Finset.mem_univ z)) x
  exact (hf y).trans_le (by simpa only [semigroup_const] using h)

lemma expDrift_continuous {n : ℕ} (J : Interaction n) (θ : ℝ) :
    Continuous (expDrift J θ) := by
  unfold expDrift generator halfDiff
  fun_prop

lemma interpolated_exp_continuous {n : ℕ} (J : Interaction n) (f : Observables n)
    (θ d : ℝ) (x : Spin n) :
    Continuous (fun s : ℝ => semigroup J s
      (fun y => Real.exp (θ * semigroup J (d - s) f y)) x) := by
  exact continuous_apply x |>.comp
    ((show Differentiable ℝ (fun s : ℝ => semigroup J s
      (fun y => Real.exp (θ * semigroup J (d - s) f y))) from
      fun s => (interpolated_exp_hasDerivAt J f θ d s).differentiableAt).continuous)

lemma interpolated_expDrift_continuous {n : ℕ} (J : Interaction n) (f : Observables n)
    (θ d : ℝ) (x : Spin n) :
    Continuous (fun s : ℝ => semigroup J s (expDrift J θ (semigroup J (d - s) f)) x) := by
  have hc : Continuous (fun s : ℝ => semigroup J (d - s) f) :=
    ((semigroup_continuous J).comp (continuous_const.sub continuous_id)).clm_apply continuous_const
  exact continuous_apply x |>.comp ((semigroup_continuous J).clm_apply
    ((expDrift_continuous J θ).comp hc))

theorem semigroup_jump_mgf {n : ℕ} (J : Interaction n) (f : Observables n)
    (d : ℝ) (hd : 0 ≤ d) (b : ℝ → ℝ) (B θ : ℝ)
    (hb : IntervalIntegrable b MeasureTheory.volume 0 d)
    (hB : ∀ r ∈ Set.Icc (0 : ℝ) d, b r ≤ B)
    (hbound : ∀ r ∈ Set.Icc (0 : ℝ) d, ∀ x, ∑ i, (halfDiff i (semigroup J r f) x) ^ 2 ≤ b r)
    (x : Spin n) :
    semigroup J d (fun y => Real.exp (θ * (f y - semigroup J d f x))) x ≤
      Real.exp (2 * θ ^ 2 * Real.exp (2 * |θ| * Real.sqrt B) * ∫ r in (0 : ℝ)..d, b r) := by
  let F (s : ℝ) := semigroup J s (fun y => Real.exp (θ * semigroup J (d - s) f y)) x
  let F' (s : ℝ) := semigroup J s (expDrift J θ (semigroup J (d - s) f)) x
  let K := 2 * θ ^ 2 * Real.exp (2 * |θ| * Real.sqrt B)
  have hFpos (s : ℝ) (hs : 0 ≤ s) : 0 < F s :=
    semigroup_pos J s hs (fun y => Real.exp_pos _) x
  have hFderiv (s : ℝ) : HasDerivAt F (F' s) s :=
    hasDerivAt_pi.mp (interpolated_exp_hasDerivAt J f θ d s) x
  have hlog (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) d) :
      HasDerivAt (fun r => Real.log (F r)) (F' s / F s) s :=
    (hFderiv s).log (hFpos s hs.1).ne'
  have hcont : ContinuousOn (fun s => F' s / F s) (Set.uIcc (0 : ℝ) d) := by
    apply (interpolated_expDrift_continuous J f θ d x).continuousOn.div
      (interpolated_exp_continuous J f θ d x).continuousOn
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) d := by simpa only [Set.uIcc_of_le hd] using hs
    exact (hFpos s hs'.1).ne'
  have hI : Real.log (F d) - Real.log (F 0) =
      ∫ s in (0 : ℝ)..d, F' s / F s := by
    symm
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hcont.intervalIntegrable
    intro s hs
    exact hlog s (by simpa only [Set.uIcc_of_le hd] using hs)
  have hbr : IntervalIntegrable (fun s => b (d - s)) MeasureTheory.volume 0 d := by
    simpa only [sub_self, sub_zero] using (hb.comp_sub_left d).symm
  have hle : Real.log (F d) - Real.log (F 0) ≤ K * ∫ r in (0 : ℝ)..d, b r := by
    rw [hI]
    calc
      _ ≤ ∫ s in (0 : ℝ)..d, K * b (d - s) := by
        apply intervalIntegral.integral_mono_on hd hcont.intervalIntegrable (hbr.const_mul K)
        intro s hs
        apply (div_le_iff₀ (hFpos s hs.1)).mpr
        have hr : d - s ∈ Set.Icc (0 : ℝ) d := ⟨sub_nonneg.mpr hs.2, by linarith [hs.1]⟩
        have hp := semigroup_mono J s hs.1
          (fun y => expDrift_le J θ (semigroup J (d - s) f) y B (b (d - s))
            ((hbound (d - s) hr y).trans (hB (d - s) hr)) (hbound (d - s) hr y)) x
        change F' s ≤ semigroup J s ((K * b (d - s)) •
          (fun y => Real.exp (θ * semigroup J (d - s) f y))) x at hp
        simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using hp
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left]
        simp only [sub_self, sub_zero]
  have hF0 : F 0 = Real.exp (θ * semigroup J d f x) := by
    dsimp [F]
    rw [sub_zero, semigroup_zero, one_apply_eq_self]
  have hFd : F d = semigroup J d (fun y => Real.exp (θ * f y)) x := by
    simp only [F, sub_self, semigroup_zero, one_apply_eq_self]
  rw [hF0, Real.log_exp] at hle
  have hle' := (Real.log_le_iff_le_exp (hFpos d hd)).mp (sub_le_iff_le_add.mp hle)
  have hfactor : (fun y => Real.exp (θ * (f y - semigroup J d f x))) =
      Real.exp (-(θ * semigroup J d f x)) • (fun y => Real.exp (θ * f y)) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, mul_sub, Real.exp_sub, Real.exp_neg]
    ring
  rw [hfactor, map_smul, Pi.smul_apply, smul_eq_mul]
  calc
    _ ≤ Real.exp (-(θ * semigroup J d f x)) *
        Real.exp (K * (∫ r in (0 : ℝ)..d, b r) + θ * semigroup J d f x) :=
      mul_le_mul_of_nonneg_left (by rwa [hFd] at hle') (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [K]; ring

end SKGapCutoff

end

end OAI
