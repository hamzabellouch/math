import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Model

namespace OAI

noncomputable section
namespace VelocityDetection.Cutoff
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Filter
open scoped Topology ContDiff

def joinAt (c : ℝ) (f g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => if x ≤ c then f x else g x

theorem hasDerivAt_joinAt {f g fd gd : ℝ → ℝ} {c : ℝ}
    (hf : ∀ x, HasDerivAt f (fd x) x) (hg : ∀ x, HasDerivAt g (gd x) x)
    (hval : f c = g c) (hder : fd c = gd c) (x : ℝ) :
    HasDerivAt (joinAt c f g) (joinAt c fd gd x) x := by
  rcases lt_trichotomy x c with hxc | hxc | hcx
  · have he : joinAt c f g =ᶠ[𝓝 x] f := by
      filter_upwards [eventually_lt_nhds hxc] with y hy
      simp [joinAt, hy.le]
    simpa [joinAt, hxc.le] using (hf x).congr_of_eventuallyEq he
  · subst x
    have hl : HasDerivWithinAt (joinAt c f g) (fd c) (Iic c) c := by
      apply (hf c).hasDerivWithinAt.congr
      · intro y hy
        simp [joinAt, mem_Iic.mp hy]
      · simp [joinAt]
    have hr : HasDerivWithinAt (joinAt c f g) (fd c) (Ici c) c := by
      rw [hder]
      apply (hg c).hasDerivWithinAt.congr
      · intro y hy
        dsimp [joinAt]
        split_ifs with hyc
        · have : y = c := le_antisymm hyc hy
          subst y
          exact hval
        · rfl
      · simp [joinAt, hval]
    simpa [joinAt, Iic_union_Ici] using hl.union hr
  · have he : joinAt c f g =ᶠ[𝓝 x] g := by
      filter_upwards [eventually_gt_nhds hcx] with y hy
      simp [joinAt, not_le.mpr hy]
    simpa [joinAt, not_le.mpr hcx] using (hg x).congr_of_eventuallyEq he

theorem continuous_joinAt {f g : ℝ → ℝ} {c : ℝ} (hf : Continuous f)
    (hg : Continuous g) (hval : f c = g c) : Continuous (joinAt c f g) := by
  apply Continuous.if_le hf hg continuous_id continuous_const
  intro x hx
  change x = c at hx
  simpa only [hx] using hval

def polynomial (s : ℝ) : ℝ := 10 * s ^ 3 - 15 * s ^ 4 + 6 * s ^ 5

def polynomialD (s : ℝ) : ℝ := 30 * s ^ 2 - 60 * s ^ 3 + 30 * s ^ 4

def polynomialDD (s : ℝ) : ℝ := 60 * s - 180 * s ^ 2 + 120 * s ^ 3

theorem hasDerivAt_polynomial (s : ℝ) : HasDerivAt polynomial (polynomialD s) s := by
  convert! (((hasDerivAt_id s).pow 3).const_mul 10 |>.sub
    (((hasDerivAt_id s).pow 4).const_mul 15)).add
    (((hasDerivAt_id s).pow 5).const_mul 6) using 1
  simp only [polynomialD, id_eq]
  ring

theorem hasDerivAt_polynomialD (s : ℝ) : HasDerivAt polynomialD (polynomialDD s) s := by
  convert! (((hasDerivAt_id s).pow 2).const_mul 30 |>.sub
    (((hasDerivAt_id s).pow 3).const_mul 60)).add
    (((hasDerivAt_id s).pow 4).const_mul 30) using 1
  simp only [polynomialDD, id_eq]
  ring

def step : ℝ → ℝ := joinAt 0 (fun _ => 0) (joinAt 1 polynomial (fun _ => 1))

def stepD : ℝ → ℝ := joinAt 0 (fun _ => 0) (joinAt 1 polynomialD (fun _ => 0))

def stepDD : ℝ → ℝ := joinAt 0 (fun _ => 0) (joinAt 1 polynomialDD (fun _ => 0))

theorem hasDerivAt_step (s : ℝ) : HasDerivAt step (stepD s) s := by
  apply hasDerivAt_joinAt (fun x => hasDerivAt_const x 0)
    (hasDerivAt_joinAt hasDerivAt_polynomial (fun x => hasDerivAt_const x 1) ?_ ?_)
    <;> norm_num [joinAt, polynomial, polynomialD]

theorem hasDerivAt_stepD (s : ℝ) : HasDerivAt stepD (stepDD s) s := by
  apply hasDerivAt_joinAt (fun x => hasDerivAt_const x 0)
    (hasDerivAt_joinAt hasDerivAt_polynomialD (fun x => hasDerivAt_const x 0) ?_ ?_)
    <;> norm_num [joinAt, polynomialD, polynomialDD]

@[simp] theorem deriv_step : deriv step = stepD := funext (fun s => (hasDerivAt_step s).deriv)

@[simp] theorem deriv_stepD : deriv stepD = stepDD := funext (fun s => (hasDerivAt_stepD s).deriv)

theorem continuous_stepDD : Continuous stepDD := by
  apply continuous_joinAt continuous_const
    (continuous_joinAt (by unfold polynomialDD; fun_prop) continuous_const ?_)
    <;> norm_num [polynomialDD, joinAt]

theorem contDiff_step : ContDiff ℝ 2 step := by
  have hdiff : Differentiable ℝ step := fun x => (hasDerivAt_step x).differentiableAt
  have hdiffD : Differentiable ℝ stepD := fun x => (hasDerivAt_stepD x).differentiableAt
  have hD : ContDiff ℝ 1 stepD := by
    rw [contDiff_one_iff_deriv, deriv_stepD]
    exact ⟨hdiffD, continuous_stepDD⟩
  rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num, contDiff_succ_iff_deriv, deriv_step]
  exact ⟨hdiff, by simp, hD⟩

theorem step_of_nonpos {s : ℝ} (hs : s ≤ 0) : step s = 0 := by
  simp [step, joinAt, hs]

theorem step_of_one_le {s : ℝ} (hs : 1 ≤ s) : step s = 1 := by
  have hn : ¬s ≤ 0 := by linarith
  dsimp [step, joinAt]
  rw [ite_eq_right hn]
  split_ifs with hs1
  · have : s = 1 := le_antisymm hs1 hs
    norm_num [this, polynomial]
  · rfl

theorem stepD_of_nonpos {s : ℝ} (hs : s ≤ 0) : stepD s = 0 := by
  simp [stepD, joinAt, hs]

theorem stepD_of_one_le {s : ℝ} (hs : 1 ≤ s) : stepD s = 0 := by
  have hn : ¬s ≤ 0 := by linarith
  dsimp [stepD, joinAt]
  rw [ite_eq_right hn]
  split_ifs with hs1
  · have : s = 1 := le_antisymm hs1 hs
    norm_num [this, polynomialD]
  · rfl

theorem stepDD_of_nonpos {s : ℝ} (hs : s ≤ 0) : stepDD s = 0 := by
  simp [stepDD, joinAt, hs]

theorem stepDD_of_one_le {s : ℝ} (hs : 1 ≤ s) : stepDD s = 0 := by
  have hn : ¬s ≤ 0 := by linarith
  dsimp [stepDD, joinAt]
  rw [ite_eq_right hn]
  split_ifs with hs1
  · have : s = 1 := le_antisymm hs1 hs
    norm_num [this, polynomialDD]
  · rfl

theorem stepD_nonneg (s : ℝ) : 0 ≤ stepD s := by
  unfold stepD joinAt
  split_ifs
  · exact le_rfl
  · have heq : polynomialD s = 30 * s ^ 2 * (1 - s) ^ 2 := by
      unfold polynomialD
      ring
    rw [heq]
    positivity
  · exact le_rfl

theorem monotone_step : Monotone step := by
  apply monotone_of_deriv_nonneg (fun x => (hasDerivAt_step x).differentiableAt)
  simpa only [deriv_step] using stepD_nonneg

theorem step_mem_Icc (s : ℝ) : 0 ≤ step s ∧ step s ≤ 1 := by
  constructor
  · rcases le_total s 0 with hs | hs
    · rw [step_of_nonpos hs]
    · simpa only [step_of_nonpos (le_refl 0)] using monotone_step hs
  · rcases le_total 1 s with hs | hs
    · rw [step_of_one_le hs]
    · simpa only [step_of_one_le (le_refl 1)] using monotone_step hs

theorem polynomialDD_bound {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |polynomialDD s| ≤ 360 := by
  have h2 : s ^ 2 ≤ 1 := pow_le_one₀ hs0 hs1
  have h3 : s ^ 3 ≤ 1 := pow_le_one₀ hs0 hs1
  calc
    |polynomialDD s| ≤ |60 * s - 180 * s ^ 2| + |120 * s ^ 3| := abs_add_le _ _
    _ ≤ |60 * s| + |180 * s ^ 2| + |120 * s ^ 3| := by
      have hb : |60 * s - 180 * s ^ 2| ≤ |60 * s| + |180 * s ^ 2| := by
        simpa only [Real.norm_eq_abs] using (norm_sub_le (60 * s) (180 * s ^ 2))
      linarith
    _ ≤ 360 := by
      rw [abs_of_nonneg (by positivity : 0 ≤ 60 * s),
        abs_of_nonneg (by positivity : 0 ≤ 180 * s ^ 2),
        abs_of_nonneg (by positivity : 0 ≤ 120 * s ^ 3)]
      linarith

theorem stepDD_bound (s : ℝ) : |stepDD s| ≤ 360 := by
  dsimp [stepDD, joinAt]
  split_ifs with hs0 hs1
  · norm_num
  · exact polynomialDD_bound (by linarith) hs1
  · norm_num

def profile (s : ℝ) : ℝ := step (2 * (1 + s)) * step (2 * (1 - s))

def profileD (s : ℝ) : ℝ :=
  2 * stepD (2 * (1 + s)) * step (2 * (1 - s)) -
  2 * step (2 * (1 + s)) * stepD (2 * (1 - s))

def profileDD (s : ℝ) : ℝ :=
  4 * stepDD (2 * (1 + s)) * step (2 * (1 - s)) -
  8 * stepD (2 * (1 + s)) * stepD (2 * (1 - s)) +
  4 * step (2 * (1 + s)) * stepDD (2 * (1 - s))

private theorem left_deriv (s : ℝ) : HasDerivAt (fun r : ℝ => 2 * (1 + r)) 2 s := by
  simpa using ((hasDerivAt_id s).const_add 1).const_mul 2

private theorem right_deriv (s : ℝ) : HasDerivAt (fun r : ℝ => 2 * (1 - r)) (-2) s := by
  simpa using ((hasDerivAt_const s 1).sub (hasDerivAt_id s)).const_mul 2

theorem hasDerivAt_profile (s : ℝ) : HasDerivAt profile (profileD s) s := by
  have hl := (hasDerivAt_step (2 * (1 + s))).comp s (left_deriv s)
  have hr := (hasDerivAt_step (2 * (1 - s))).comp s (right_deriv s)
  convert! hl.mul hr using 1
  dsimp [profileD]
  ring

theorem hasDerivAt_profileD (s : ℝ) : HasDerivAt profileD (profileDD s) s := by
  have hl := (hasDerivAt_step (2 * (1 + s))).comp s (left_deriv s)
  have hr := (hasDerivAt_step (2 * (1 - s))).comp s (right_deriv s)
  have hld := (hasDerivAt_stepD (2 * (1 + s))).comp s (left_deriv s)
  have hrd := (hasDerivAt_stepD (2 * (1 - s))).comp s (right_deriv s)
  convert! ((hld.const_mul 2).mul hr).sub ((hl.const_mul 2).mul hrd) using 1
  dsimp [profileDD]
  ring

@[simp] theorem deriv_profile : deriv profile = profileD :=
  funext (fun s => (hasDerivAt_profile s).deriv)

@[simp] theorem deriv_profileD : deriv profileD = profileDD :=
  funext (fun s => (hasDerivAt_profileD s).deriv)

theorem contDiff_profile : ContDiff ℝ 2 profile :=
  (contDiff_step.comp (by fun_prop)).mul (contDiff_step.comp (by fun_prop))

theorem profile_mem_Icc (s : ℝ) : 0 ≤ profile s ∧ profile s ≤ 1 := by
  have hl := step_mem_Icc (2 * (1 + s))
  have hr := step_mem_Icc (2 * (1 - s))
  refine ⟨mul_nonneg hl.1 hr.1, ?_⟩
  calc
    _ ≤ 1 * step (2 * (1 - s)) := mul_le_mul_of_nonneg_right hl.2 hr.1
    _ ≤ 1 := by simpa only [one_mul] using hr.2

theorem profile_one {s : ℝ} (hs : |s| ≤ 1 / 2) : profile s = 1 := by
  obtain ⟨hs0, hs1⟩ := abs_le.mp hs
  rw [profile, step_of_one_le (by linarith), step_of_one_le (by linarith), mul_one]

theorem profile_zero {s : ℝ} (hs : 1 ≤ |s|) : profile s = 0 := by
  rcases le_total s 0 with h | h
  · rw [abs_of_nonpos h] at hs
    rw [profile, step_of_nonpos (by linarith), zero_mul]
  · rw [abs_of_nonneg h] at hs
    rw [profile, step_of_nonpos (s := 2 * (1 - s)) (by linarith), mul_zero]

theorem profileDD_bound (s : ℝ) : |profileDD s| ≤ 1440 := by
  rcases le_total s 0 with hs | hs
  · have hr : 1 ≤ 2 * (1 - s) := by linarith
    simp only [profileDD, step_of_one_le hr, stepD_of_one_le hr,
      stepDD_of_one_le hr, mul_one, mul_zero, sub_zero, add_zero]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    linarith [stepDD_bound (2 * (1 + s))]
  · have hl : 1 ≤ 2 * (1 + s) := by linarith
    simp only [profileDD, step_of_one_le hl, stepD_of_one_le hl,
      stepDD_of_one_le hl, mul_one, mul_zero, zero_mul, zero_sub, neg_zero, zero_add]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    linarith [stepDD_bound (2 * (1 - s))]

def cutoff (R : ℝ) (Y : Coord 2) : ℝ := profile (Y 0 / R) * profile (Y 1 / R)

theorem contDiff_cutoff (R : ℝ) : ContDiff ℝ 2 (cutoff R) :=
  (contDiff_profile.comp (by fun_prop)).mul (contDiff_profile.comp (by fun_prop))

theorem cutoff_mem_Icc (R : ℝ) (Y : Coord 2) : 0 ≤ cutoff R Y ∧ cutoff R Y ≤ 1 := by
  have hl := profile_mem_Icc (Y 0 / R)
  have hr := profile_mem_Icc (Y 1 / R)
  refine ⟨mul_nonneg hl.1 hr.1, ?_⟩
  calc
    _ ≤ 1 * profile (Y 1 / R) := mul_le_mul_of_nonneg_right hl.2 hr.1
    _ ≤ 1 := by simpa only [one_mul] using hr.2

theorem cutoff_one {R : ℝ} (hR : 0 < R) {Y : Coord 2}
    (hY : ∀ i, |Y i| ≤ R / 2) : cutoff R Y = 1 := by
  have hb (i : Fin 2) : |Y i / R| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hR, div_le_iff₀ hR]
    linarith [hY i]
  simp only [cutoff, profile_one (hb 0), profile_one (hb 1), mul_one]

theorem cutoff_zero {R : ℝ} (hR : 0 < R) {Y : Coord 2}
    (hY : ∃ i, R ≤ |Y i|) : cutoff R Y = 0 := by
  obtain ⟨i, hi⟩ := hY
  have hb : 1 ≤ |Y i / R| := by
    rw [abs_div, abs_of_pos hR, le_div_iff₀ hR, one_mul]
    exact hi
  fin_cases i
  · change 1 ≤ |Y 0 / R| at hb
    simp only [cutoff, profile_zero hb, zero_mul]
  · change 1 ≤ |Y 1 / R| at hb
    simp only [cutoff, profile_zero hb, mul_zero]

theorem cutoff_one_on_support {R S : ℝ} (hR : 0 < R) (hRS : 2 * R ≤ S)
    {Y : Coord 2} (hY : cutoff R Y ≠ 0) : cutoff S Y = 1 := by
  apply cutoff_one (by linarith)
  intro i
  have hi : |Y i| < R := lt_of_not_ge (fun h => hY (cutoff_zero hR ⟨i, h⟩))
  linarith

theorem cutoff_le_doubled {R S : ℝ} (hR : 0 < R) (hRS : 2 * R ≤ S) (Y : Coord 2) :
    cutoff R Y ≤ cutoff S Y := by
  by_cases hY : cutoff R Y = 0
  · rw [hY]
    exact (cutoff_mem_Icc S Y).1
  · rw [cutoff_one_on_support hR hRS hY]
    exact (cutoff_mem_Icc R Y).2

theorem hasCompactSupport_cutoff {R : ℝ} (hR : 0 < R) : HasCompactSupport (cutoff R) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Coord 2) R)
  intro Y hY
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR.le]
  intro i
  have hi : |Y i| < R := lt_of_not_ge (fun h => hY (cutoff_zero hR ⟨i, h⟩))
  simpa only [Real.norm_eq_abs] using hi.le

theorem spatialD_cutoff_zero (R : ℝ) :
    spatialD 0 (fun _ Y => cutoff R Y) =
      fun _ Y => (profileD (Y 0 / R) / R) * profile (Y 1 / R) := by
  funext t Y
  change deriv (fun s => profile (s / R) * profile (Y 1 / R)) (Y 0) = _
  have h := ((hasDerivAt_profile (Y 0 / R)).comp (Y 0)
    ((hasDerivAt_id (Y 0)).div_const R)).mul_const (profile (Y 1 / R))
  simpa only [Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using h.deriv

theorem spatialD_cutoff_one (R : ℝ) :
    spatialD 1 (fun _ Y => cutoff R Y) =
      fun _ Y => profile (Y 0 / R) * (profileD (Y 1 / R) / R) := by
  funext t Y
  change deriv (fun s => profile (Y 0 / R) * profile (s / R)) (Y 1) = _
  have h := ((hasDerivAt_profile (Y 1 / R)).comp (Y 1)
    ((hasDerivAt_id (Y 1)).div_const R)).const_mul (profile (Y 0 / R))
  simpa only [Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using h.deriv

theorem spatialD_cutoff_zero_zero (R : ℝ) :
    spatialD 0 (spatialD 0 (fun _ Y => cutoff R Y)) =
      fun _ Y => (profileDD (Y 0 / R) / R ^ 2) * profile (Y 1 / R) := by
  rw [spatialD_cutoff_zero]
  funext t Y
  change deriv (fun s => (profileD (s / R) / R) * profile (Y 1 / R)) (Y 0) = _
  have h := (((hasDerivAt_profileD (Y 0 / R)).comp (Y 0)
    ((hasDerivAt_id (Y 0)).div_const R)).div_const R).mul_const (profile (Y 1 / R))
  convert! h.deriv using 1
  simp only [div_eq_mul_inv]
  ring

theorem spatialD_cutoff_one_one (R : ℝ) :
    spatialD 1 (spatialD 1 (fun _ Y => cutoff R Y)) =
      fun _ Y => profile (Y 0 / R) * (profileDD (Y 1 / R) / R ^ 2) := by
  rw [spatialD_cutoff_one]
  funext t Y
  change deriv (fun s => profile (Y 0 / R) * (profileD (s / R) / R)) (Y 1) = _
  have h := (((hasDerivAt_profileD (Y 1 / R)).comp (Y 1)
    ((hasDerivAt_id (Y 1)).div_const R)).div_const R).const_mul (profile (Y 0 / R))
  convert! h.deriv using 1
  simp only [div_eq_mul_inv]
  ring

theorem laplacian_cutoff (R t : ℝ) (Y : Coord 2) :
    laplacian (fun _ X => cutoff R X) t Y =
      (profileDD (Y 0 / R) * profile (Y 1 / R) +
        profile (Y 0 / R) * profileDD (Y 1 / R)) / R ^ 2 := by
  simp only [laplacian, Fin.sum_univ_two,
    spatialD_cutoff_zero_zero, spatialD_cutoff_one_one]
  ring

private theorem profile_abs_le (s : ℝ) : |profile s| ≤ 1 := by
  rw [abs_of_nonneg (profile_mem_Icc s).1]
  exact (profile_mem_Icc s).2

theorem laplacian_cutoff_bound {R : ℝ} (hR : 0 < R) (t : ℝ) (Y : Coord 2) :
    |laplacian (fun _ X => cutoff R X) t Y| ≤ 2880 / R ^ 2 := by
  have hb0 : |profileDD (Y 0 / R) * profile (Y 1 / R)| ≤ 1440 := by
    rw [abs_mul]
    calc
      _ ≤ 1440 * 1 := mul_le_mul (profileDD_bound _) (profile_abs_le _) (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hb1 : |profile (Y 0 / R) * profileDD (Y 1 / R)| ≤ 1440 := by
    rw [abs_mul]
    calc
      _ ≤ 1 * 1440 := mul_le_mul (profile_abs_le _) (profileDD_bound _) (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  rw [laplacian_cutoff, abs_div, abs_of_pos (sq_pos_of_pos hR)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg R)
  have htri := abs_add_le (profileDD (Y 0 / R) * profile (Y 1 / R))
    (profile (Y 0 / R) * profileDD (Y 1 / R))
  linarith

theorem laplacian_cutoff_bound_3000 {R : ℝ} (hR : 0 < R) (t : ℝ) (Y : Coord 2) :
    |laplacian (fun _ X => cutoff R X) t Y| ≤ 3000 / R ^ 2 := by
  exact (laplacian_cutoff_bound hR t Y).trans
    (div_le_div_of_nonneg_right (by norm_num) (sq_nonneg R))

theorem continuous_profileD : Continuous profileD :=
  (show Differentiable ℝ profileD from fun s => (hasDerivAt_profileD s).differentiableAt).continuous

theorem continuous_profileDD : Continuous profileDD := by
  have hP := contDiff_step.continuous
  have hD : Continuous stepD :=
    (show Differentiable ℝ stepD from fun s => (hasDerivAt_stepD s).differentiableAt).continuous
  have hDD := continuous_stepDD
  unfold profileDD
  fun_prop

theorem continuous_laplacian_cutoff (R t : ℝ) :
    Continuous (laplacian (fun _ X => cutoff R X) t) := by
  have hP := contDiff_profile.continuous
  have hDD := continuous_profileDD
  change Continuous fun Y => laplacian (fun _ X => cutoff R X) t Y
  simp_rw [laplacian_cutoff]
  fun_prop

theorem profileD_zero {s : ℝ} (hs : 1 ≤ |s|) : profileD s = 0 := by
  rcases le_total s 0 with h | h
  · rw [abs_of_nonpos h] at hs
    simp only [profileD, step_of_nonpos (by linarith : 2 * (1 + s) ≤ 0),
      stepD_of_nonpos (by linarith : 2 * (1 + s) ≤ 0), mul_zero, zero_mul, sub_zero]
  · rw [abs_of_nonneg h] at hs
    simp only [profileD, step_of_nonpos (by linarith : 2 * (1 - s) ≤ 0),
      stepD_of_nonpos (by linarith : 2 * (1 - s) ≤ 0), mul_zero, sub_zero]

end VelocityDetection.Cutoff
end

end OAI
