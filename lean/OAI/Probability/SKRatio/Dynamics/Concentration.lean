import Mathlib
import OAI.Probability.SKRatio.Calculus.SignedVector

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap MeasureTheory Filter
namespace SKRatio.Calculus

lemma flip_sub {n : ℕ} (f : Observables n) (x : Spin n) (i : Fin n) :
    f (flip i x)-f x = -2*spin x i*halfDiff i f x := by
  have hx := replace_self x i
  cases hi : x i <;> simp only [hi] at hx
  · simp only [spin, hi, Bool.false_eq_true, ↓reduceIte, flip, Bool.not_false, halfDiff]
    rw [hx]
    simp only [replace]
    ring
  · simp only [spin, hi, ↓reduceIte, flip, Bool.not_true, halfDiff]
    rw [hx]
    simp only [replace]
    ring

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
  try rfl
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

lemma semigroup_le_const {n : ℕ} (J : Interaction n) (t : ℝ) (ht : 0 ≤ t)
    {f : Observables n} {C : ℝ} (hf : ∀ x, f x ≤ C) (x : Spin n) :
    semigroup J t f x ≤ C := by
  simpa only [semigroup_const] using semigroup_mono J ht _ _ hf x

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

noncomputable def expDrift {n : ℕ} (J : Interaction n) (θ : ℝ)
    (f : Observables n) (x : Spin n) : ℝ :=
  generator J (fun y => Real.exp (θ * f y)) x -
    θ * Real.exp (θ * f x) * generator J f x

lemma expDrift_eq_sum {n : ℕ} (J : Interaction n) (θ : ℝ) (f : Observables n) (x : Spin n) :
    expDrift J θ f x = Real.exp (θ * f x) * ∑ i, flipRate J x i *
      (Real.exp (θ * (f (flip i x) - f x)) - 1 - θ * (f (flip i x) - f x)) := by
  have he (i : Fin n) : Real.exp (θ * f (flip i x)) =
      Real.exp (θ * f x) * Real.exp (θ * (f (flip i x) - f x)) := by
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
    jumpEnergy J f x = ∑ i, flipRate J x i * (f (flip i x) - f x) ^ 2 := by
  simp only [jumpEnergy, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [flip_sub]
  simp only [mul_pow, spin_sq, mul_one, flipRate]
  ring

lemma abs_flip_sub_le {n : ℕ} (f : Observables n) (x : Spin n) (B : ℝ)
    (hB : ∑ j, (halfDiff j f x) ^ 2 ≤ B) (i : Fin n) :
    |f (flip i x) - f x| ≤ 2 * Real.sqrt B := by
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
      Real.exp (θ * (f (flip i x) - f x)) - 1 - θ * (f (flip i x) - f x) ≤
        θ ^ 2 * R / 2 * (f (flip i x) - f x) ^ 2 := by
    have ha : |θ * (f (flip i x) - f x)| ≤ 2 * |θ| * Real.sqrt B := by
      rw [abs_mul]
      calc
        _ ≤ |θ| * (2 * Real.sqrt B) :=
          mul_le_mul_of_nonneg_left (abs_flip_sub_le f x B hB i) (abs_nonneg θ)
        _ = _ := by ring
    calc
      _ ≤ (θ * (f (flip i x) - f x)) ^ 2 *
          Real.exp |θ * (f (flip i x) - f x)| / 2 := real_exp_remainder_le _
      _ ≤ (θ * (f (flip i x) - f x)) ^ 2 * R / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ha) (sq_nonneg _)
      _ = _ := by ring
  rw [expDrift_eq_sum]
  calc
    _ ≤ Real.exp (θ * f x) * ∑ i, flipRate J x i *
        (θ ^ 2 * R / 2 * (f (flip i x) - f x) ^ 2) := by
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
  try rfl
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
  have h := semigroup_mono J ht _ _ (fun z => hy z (Finset.mem_univ z)) x
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
        have hp := semigroup_mono J hs.1 _ _
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

end SKRatio.Calculus

end
end

end OAI
