import OAI.Analysis.LipschitzEquivalence.SlowAngles

namespace OAI

universe uX uE

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal

namespace LipschitzCounterexample.RotatingStages
open Set Filter
open scoped Topology InnerProductSpace
open SlowAngles RadialBudget
variable {X : Type uX} {E : Type uE} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def path (W : ℕ → X → E) (α : ℕ → X → ℝ) : ℕ → X → E
  | 0, x => W 0 x
  | N+1, x => Real.cos (α N x) • path W α N x + Real.sin (α N x) • W (N+1) x

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
@[simp] theorem path_zero (W : ℕ → X → E) (α : ℕ → X → ℝ) (x : X) :
    path W α 0 x = W 0 x := rfl

theorem path_contDiff (W : ℕ → X → E) (α : ℕ → X → ℝ)
    (hW : ∀ k, ContDiff ℝ 1 (W k)) (hα : ∀ k, ContDiff ℝ 1 (α k)) (N : ℕ) :
    ContDiff ℝ 1 (path W α N) := by
  induction N with
  | zero => exact hW 0
  | succ N ih => exact ((hα N).cos.smul ih).add ((hα N).sin.smul (hW (N+1)))

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem inner_path_stage (W : ℕ → X → E) (α : ℕ → X → ℝ)
    (N k : ℕ) (hk : N < k) (x : X)
    (horth : ∀ j ≤ N, ⟪W j x,W k x⟫_ℝ = 0) :
    ⟪path W α N x,W k x⟫_ℝ = 0 := by
  induction N with
  | zero => exact horth 0 (le_refl _)
  | succ N ih =>
    rw [path, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      ih (by omega) (fun j hj => horth j (by omega)), horth (N+1) (le_refl _)]
    ring

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem norm_path (W : ℕ → X → E) (α : ℕ → X → ℝ) (N : ℕ) (x : X)
    (hnorm : ∀ j ≤ N, ‖W j x‖ = 1)
    (horth : ∀ j k, j < k → k ≤ N → ⟪W j x,W k x⟫_ℝ = 0) :
    ‖path W α N x‖ = 1 := by
  induction N with
  | zero => exact hnorm 0 (le_refl _)
  | succ N ih =>
    have hp := ih (fun j hj => hnorm j (by omega)) (fun j k hjk hk => horth j k hjk (by omega))
    have ho := inner_path_stage W α N (N+1) (by omega) x (fun j hj => horth j (N+1) (by omega) (le_refl _))
    have hs : ‖path W α (N+1) x‖^2 = 1 := by
      rw [path, norm_add_sq_real, norm_smul, norm_smul, hp, hnorm (N+1) (le_refl _),
        real_inner_smul_left, real_inner_smul_right, ho]
      simp only [Real.norm_eq_abs, mul_one, mul_zero, add_zero, sq_abs]
      exact Real.cos_sq_add_sin_sq _
    nlinarith [norm_nonneg (path W α (N+1) x)]

omit [NormedSpace ℝ X] in
theorem path_small_eventually (W : ℕ → X → E) (L : ℕ → ℝ) (hL : ∀ k, 0 ≤ L k)
    (R : X → ℝ) (hcR : Continuous R) (N : ℕ) (x : X) (hr : R x ≤ lower L hL N) :
    path W (fun k x => theta L hL k (R x)) (N+1) =ᶠ[𝓝 x] W (N+1) := by
  have he := (theta_small_eventually L hL N hr).comp_tendsto hcR.continuousAt
  filter_upwards [he] with y hy
  simp only [Function.comp_def] at hy
  simp [path, hy]

omit [NormedSpace ℝ X] in
theorem path_large_eventually (W : ℕ → X → E) (L : ℕ → ℝ) (hL : ∀ k, 0 ≤ L k)
    (R : X → ℝ) (hcR : Continuous R) (N : ℕ) (x : X) (hr : upper L hL N ≤ R x) :
    path W (fun k x => theta L hL k (R x)) (N+1) =ᶠ[𝓝 x]
      path W (fun k x => theta L hL k (R x)) N := by
  have he := (theta_large_eventually L hL N hr).comp_tendsto hcR.continuousAt
  filter_upwards [he] with y hy
  simp only [Function.comp_def] at hy
  simp [path, hy]

end LipschitzCounterexample.RotatingStages

namespace LipschitzCounterexample.RotatingStages
open Set Filter
open scoped Topology InnerProductSpace
open SlowAngles RadialBudget
variable {X : Type uX} {E : Type uE} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem norm_angular {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : ⟪u,v⟫_ℝ = 0) (a : ℝ) : ‖(-Real.sin a) • u + Real.cos a • v‖ = 1 := by
  have hs : ‖(-Real.sin a) • u + Real.cos a • v‖^2 = 1 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, hu, hv,
      real_inner_smul_left, real_inner_smul_right, huv]
    simp only [norm_neg, Real.norm_eq_abs, mul_one, mul_zero, add_zero, sq_abs]
    exact Real.sin_sq_add_cos_sq _
  nlinarith [norm_nonneg ((-Real.sin a) • u + Real.cos a • v)]

theorem rotation_deriv_bound (f g : X → E) (α : X → ℝ) (x : X)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (hα : DifferentiableAt ℝ α x)
    (hnf : ‖f x‖ = 1) (hng : ‖g x‖ = 1) (horth : ⟪f x,g x⟫_ℝ = 0) :
    ‖fderiv ℝ (fun y => Real.cos (α y) • f y + Real.sin (α y) • g y) x‖ ≤
      ‖fderiv ℝ f x‖ + ‖fderiv ℝ g x‖ + ‖fderiv ℝ α x‖ := by
  have hd := ((hα.hasFDerivAt.cos).smul hf.hasFDerivAt).add
    ((hα.hasFDerivAt.sin).smul hg.hasFDerivAt)
  have he : fderiv ℝ (fun y => Real.cos (α y) • f y + Real.sin (α y) • g y) x =
      (Real.cos (α x)) • fderiv ℝ f x + (Real.sin (α x)) • fderiv ℝ g x +
        (fderiv ℝ α x).smulRight ((-Real.sin (α x)) • f x + Real.cos (α x) • g x) := by
    change fderiv ℝ ((fun x => Real.cos (α x)) • f + (fun x => Real.sin (α x)) • g) x = _
    rw [hd.fderiv]
    ext z
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul, smul_add, smul_smul]
    module
  rw [he]
  calc
    _ ≤ ‖Real.cos (α x) • fderiv ℝ f x + Real.sin (α x) • fderiv ℝ g x‖ +
        ‖(fderiv ℝ α x).smulRight ((-Real.sin (α x)) • f x + Real.cos (α x) • g x)‖ := norm_add_le _ _
    _ ≤ (‖Real.cos (α x) • fderiv ℝ f x‖ + ‖Real.sin (α x) • fderiv ℝ g x‖) +
        ‖fderiv ℝ α x‖ * ‖(-Real.sin (α x)) • f x + Real.cos (α x) • g x‖ := by
      exact add_le_add (norm_add_le _ _) (ContinuousLinearMap.norm_smulRight_apply _ _).le
    _ ≤ _ := by
      rw [norm_smul, norm_smul, norm_angular hnf hng horth, mul_one]
      simp only [Real.norm_eq_abs]
      have hc := mul_le_of_le_one_left (norm_nonneg (fderiv ℝ f x)) (Real.abs_cos_le_one (α x))
      have hs := mul_le_of_le_one_left (norm_nonneg (fderiv ℝ g x)) (Real.abs_sin_le_one (α x))
      linarith

end LipschitzCounterexample.RotatingStages

namespace LipschitzCounterexample.RotatingStages
open Set Filter
open scoped Topology InnerProductSpace
open SlowAngles RadialBudget
variable {X : Type uX} {E : Type uE} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem path_derivative_budget (W : ℕ → X → E) (L : ℕ → ℝ) (hL : ∀ k, 0 ≤ L k)
    (hL0 : L 0 = 0) (R : X → ℝ) (hcR : Continuous R)
    (hdR : ∀ x, 0 < R x → ContDiffAt ℝ 1 R x)
    (hLipR : LipschitzWith ⟨Real.sqrt 3, Real.sqrt_nonneg _⟩ R)
    (hdW : ∀ k, ContDiff ℝ 1 (W k)) (hbW : ∀ k x, ‖fderiv ℝ (W k) x‖ ≤ L k)
    (N : ℕ) (x : X) (hr : 0 < R x)
    (hnW : ∀ j ≤ N, ‖W j x‖ = 1)
    (hoW : ∀ j k, j < k → k ≤ N → ⟪W j x,W k x⟫_ℝ = 0) :
    ‖fderiv ℝ (path W (fun k x => theta L hL k (R x)) N) x‖ ≤ gamma (R x) := by
  induction N with
  | zero =>
    change ‖fderiv ℝ (W 0) x‖ ≤ _
    exact (hbW 0 x).trans (hL0 ▸ gamma_nonneg (R x))
  | succ N ih =>
    by_cases hlarge : upper L hL N ≤ R x
    · rw [(path_large_eventually W L hL R hcR N x hlarge).fderiv_eq]
      exact ih (fun j hj => hnW j (by omega)) (fun j k hjk hk => hoW j k hjk (by omega))
    by_cases hsmall : R x ≤ lower L hL N
    · rw [(path_small_eventually W L hL R hcR N x hsmall).fderiv_eq]
      have hb := stage_budget L hL N hr (le_of_not_ge hlarge)
      exact (hbW (N+1) x).trans (by linarith [hL N, gamma_nonneg (R x)])
    have hp : path W (fun k x => theta L hL k (R x)) N =ᶠ[𝓝 x] W N := by
      cases N with
      | zero => exact Filter.EventuallyEq.rfl
      | succ K =>
        apply path_small_eventually W L hL R hcR K x
        exact (le_of_not_ge hlarge).trans (interval_separation L hL K).le
    have he : path W (fun k x => theta L hL k (R x)) (N+1) =ᶠ[𝓝 x]
        fun y => Real.cos (theta L hL N (R y)) • W N y +
          Real.sin (theta L hL N (R y)) • W (N+1) y := by
      filter_upwards [hp] with y hy
      simp only [path, hy]
    rw [he.fderiv_eq]
    have ht : DifferentiableAt ℝ (fun y => theta L hL N (R y)) x :=
      (((theta_contDiff L hL N (d := 1)).contDiffAt.comp x (hdR x hr)).differentiableAt (by norm_num))
    have hb := rotation_deriv_bound (W N) (W (N+1)) (fun y => theta L hL N (R y)) x
      ((hdW N).differentiable (by norm_num) x) ((hdW (N+1)).differentiable (by norm_num) x) ht
      (hnW N (by omega)) (hnW (N+1) (le_refl _)) (hoW N (N+1) (by omega) (le_refl _))
    have hθ := pulledAngle_deriv_bound L hL R hdR hLipR N x hr
    have hstage := stage_budget L hL N hr (le_of_not_ge hlarge)
    linarith [hbW N x, hbW (N+1) x]

end LipschitzCounterexample.RotatingStages

namespace LipschitzCounterexample.SlowAngles
open Set Filter

theorem angle_antitone (A : ℝ) {B : ℝ} (hB : 0 < B) : Antitone (angle A B) := by
  intro r s hrs
  by_cases hr : r ≤ warp (A+B)
  · rw [angle_small hB hr]
    exact (angle_between A B s).2
  by_cases hs : warp A ≤ s
  · rw [angle_large hB hs]
    exact (angle_between A B r).1
  have hr0 : 0 < r := (warp_pos _).trans (lt_of_not_ge hr)
  have hs1 : s < 1 := (lt_of_not_ge hs).trans (warp_lt_one _)
  have hsmall := warp_strictAnti (by linarith : A+B < A+B+1)
  have hlarge := warp_strictAnti (by linarith : A-1 < A)
  rw [(angle_eventually_formula (hsmall.trans (lt_of_not_ge hr)) (hrs.trans_lt ((lt_of_not_ge hs).trans hlarge))).eq_of_nhds,
    (angle_eventually_formula ((hsmall.trans (lt_of_not_ge hr)).trans_le hrs) ((lt_of_not_ge hs).trans hlarge)).eq_of_nhds]
  unfold angleFormula
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.smoothTransition.monotone
  apply div_le_div_of_nonneg_right _ hB.le
  apply sub_le_sub_right
  apply Real.log_le_log (neg_pos.mpr (Real.log_neg (hr0.trans_le hrs) hs1))
  exact neg_le_neg (Real.log_le_log hr0 hrs)

theorem theta_antitone (L : ℕ → ℝ) (hL : ∀ k, 0 ≤ L k) (k : ℕ) :
    Antitone (theta L hL k) := angle_antitone _ width_pos

end LipschitzCounterexample.SlowAngles

namespace LipschitzCounterexample.HilbertSlots
open scoped ENNReal NNReal InnerProductSpace
variable {E : ℕ → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]

theorem radius_contDiffAt (N : ℕ) (x : SlotDomain E) (hr : 0 < radius N x) :
    ContDiffAt ℝ 1 (radius (E := E) N) x := by
  let T : SlotDomain E →L[ℝ] HilbertSum (RadiusBlock E) :=
    (tailCLM (E := RadiusBlock E) N).comp (radiusCLM (E := E))
  have hn : T x ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact ne_of_gt hr
  change ContDiffAt ℝ 1 (fun y => ‖T y‖) x
  exact T.contDiff.contDiffAt.norm ℝ hn

end LipschitzCounterexample.HilbertSlots

end

end OAI
