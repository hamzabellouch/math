import Mathlib
import OAI.Analysis.CoulombRadii.Model

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom

theorem second_deriv_nonpos_of_local_max {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra h
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge h
  have hn : IsLocalMin f x := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hm, hn] with y hy hz
    exact le_antisymm hy hz
  have hed : deriv f =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [he.eventually_nhds] with y hy
    have hy' : f =ᶠ[𝓝 y] fun _ => f x := hy
    simpa using hy'.deriv_eq
  have : deriv (deriv f) x = 0 := by simpa using hed.deriv_eq
  linarith

def axis (a : Fin 3) : Position := EuclideanSpace.single a 1

def coordinateLaplacian (f : Position → ℝ) (x : Position) : ℝ :=
  ∑ a : Fin 3, deriv (deriv (fun t : ℝ => f (x+t • axis a))) 0

theorem coordinateLaplacian_nonpos_of_local_max {f : Position → ℝ} {x : Position}
    (hm : IsLocalMax f x) (hc : ContinuousAt f x) : coordinateLaplacian f x ≤ 0 := by
  apply Finset.sum_nonpos
  intro a _
  have hl : ContinuousAt (fun t : ℝ => x+t • axis a) 0 := by fun_prop
  have hl' : Tendsto (fun t : ℝ => x+t • axis a) (𝓝 0) (𝓝 x) := by simpa using hl.tendsto
  apply second_deriv_nonpos_of_local_max
  · change ∀ᶠ t in 𝓝 0, f (x+t • axis a) ≤ f (x+0 • axis a)
    simpa only [zero_smul, add_zero] using hl'.eventually hm
  · simpa only [ContinuousAt, Function.comp_def, zero_smul, add_zero] using hc.tendsto.comp hl'

theorem norm_sq_axis_shift (x : Position) (a : Fin 3) (t : ℝ) :
    ‖x+t • axis a‖^2 = ‖x‖^2 + 2*t*x a + t^2 := by
  rw [norm_add_sq_real]
  simp [axis, inner_smul_right, EuclideanSpace.inner_single_right, norm_smul,
    Real.norm_eq_abs, sq_abs]
  ring

theorem second_deriv_quadratic_rpow {q b p : ℝ} (hq : 0 < q) :
    deriv (deriv (fun t : ℝ => (q+2*t*b+t^2)^p)) 0 =
      p*(p-1)*q^(p-2)*(2*b)^2 + 2*p*q^(p-1) := by
  let Q : ℝ → ℝ := fun t => q+2*t*b+t^2
  have hQ (t : ℝ) : HasDerivAt Q (2*b+2*t) t := by
    convert (((hasDerivAt_const t q).add
      (((hasDerivAt_id t).const_mul 2).mul_const b)).add
      ((hasDerivAt_id t).pow 2)) using 1
    all_goals first | rfl | norm_num [Q]
  have hQ0 : Q 0 = q := by simp [Q]
  have hQe : ∀ᶠ t in 𝓝 (0 : ℝ), Q t ≠ 0 :=
    (hQ 0).continuousAt.eventually_ne (by simpa [hQ0] using ne_of_gt hq)
  have hder : deriv (fun t => Q t ^ p) =ᶠ[𝓝 0]
      fun t => p*Q t^(p-1)*(2*b+2*t) := by
    filter_upwards [hQe] with t ht
    convert ((hQ t).rpow_const (Or.inl ht)).deriv using 1
    ring
  rw [hder.deriv_eq]
  have hh := (((hQ 0).rpow_const (p := p-1)
      (Or.inl (by simpa [hQ0] using ne_of_gt hq))).const_mul p).mul
    ((hasDerivAt_const 0 (2*b)).add ((hasDerivAt_id 0).const_mul 2))
  have hh' : HasDerivAt (fun t => p*Q t^(p-1)*(2*b+2*t))
      (p*((2*b)*(p-1)*q^(p-1-1))*(2*b)+p*q^(p-1)*2) 0 := by
    convert hh using 1
    all_goals first | rfl | norm_num [Q]
  rw [hh'.deriv]
  rw [show p-1-1 = p-2 by ring]
  ring

def radialPower (p : ℝ) (x : Position) : ℝ := (‖x‖^2)^p

theorem coordinateLaplacian_radialPower {x : Position} (hx : x ≠ 0) (p : ℝ) :
    coordinateLaplacian (radialPower p) x = 2*p*(2*p+1)*(‖x‖^2)^(p-1) := by
  have hx0 : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  unfold coordinateLaplacian radialPower
  conv_lhs => arg 2; ext a; arg 1; arg 1; ext t; rw [norm_sq_axis_shift]
  simp only [second_deriv_quadratic_rpow hx0, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hpow : (‖x‖^2)^(p-2) * (‖x‖^2) = (‖x‖^2)^(p-1) := by
    rw [← Real.rpow_add_one hx0.ne']
    congr 1
    ring
  calc
    _ = 4*p*(p-1)*(‖x‖^2)^(p-2)*(∑ a : Fin 3, (x a)^2) +
        6*p*(‖x‖^2)^(p-1) := by
      rw [Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro a _
        ring
      · norm_num
        ring
    _ = _ := by
      rw [← EuclideanSpace.real_norm_sq_eq]
      calc
        _ = 4*p*(p-1)*((‖x‖^2)^(p-2) * ‖x‖^2) +
          6*p*(‖x‖^2)^(p-1) := by ring
        _ = _ := by rw [hpow]; ring

theorem deriv_affine_line {f : Position → ℝ} {x v : Position} {t : ℝ}
    (hf : DifferentiableAt ℝ f (x+t • v)) :
    deriv (fun u : ℝ => f (x+u • v)) t = fderiv ℝ f (x+t • v) v := by
  have hl : HasDerivAt (fun u : ℝ => x+u • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  exact (hf.hasFDerivAt.comp_hasDerivAt t hl).deriv

theorem second_deriv_affine_line {f : Position → ℝ} {x v : Position}
    (hf : ContDiffAt ℝ 2 f x) :
    deriv (deriv (fun u : ℝ => f (x+u • v))) 0 =
      fderiv ℝ (fun y => fderiv ℝ f y v) x v := by
  have hl : Tendsto (fun u : ℝ => x+u • v) (𝓝 0) (𝓝 x) := by
    simpa using (show ContinuousAt (fun u : ℝ => x+u • v) 0 by fun_prop).tendsto
  have he : deriv (fun u : ℝ => f (x+u • v)) =ᶠ[𝓝 0]
      fun u => fderiv ℝ f (x+u • v) v := by
    filter_upwards [hl.eventually (hf.eventually (by norm_num))] with u hu
    exact deriv_affine_line (hu.differentiableAt (by norm_num))
  rw [he.deriv_eq]
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x :=
    ((hf.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply contDiffAt_const).differentiableAt_one
  simpa using deriv_affine_line (x := x) (v := v) (t := 0) (by simpa using hd)

theorem coordinateLaplacian_reflect (f : Position → ℝ) (x y : Position) :
    coordinateLaplacian (fun z => f (x-z)) y = coordinateLaplacian f (x-y) := by
  apply Finset.sum_congr rfl
  intro a _
  have he : (fun t : ℝ => f (x-(y+t • axis a))) =
      (fun t : ℝ => f ((x-y)+(-t) • axis a)) := by
    ext t
    congr 1
    module
  rw [he]
  let g : ℝ → ℝ := fun t => f ((x-y)+t • axis a)
  change deriv (deriv (fun t => g (-t))) 0 = deriv (deriv g) 0
  have hd : deriv (fun t => g (-t)) = fun t => -deriv g (-t) := by
    ext t
    exact deriv_comp_neg g t
  rw [hd]
  change deriv (-(fun t => deriv g (-t))) 0 = _
  rw [deriv.neg, deriv_comp_neg]
  simp

open scoped Convolution
open ContinuousLinearMap

def dirPartial (f : Position → ℝ) (v : Position) : Position → ℝ :=
  fun x => fderiv ℝ f x v

theorem contDiff_partial {f : Position → ℝ} {n : WithTop ℕ∞}
    (hf : ContDiff ℝ (n+1) f) (v : Position) : ContDiff ℝ n (dirPartial f v) := by
  exact (hf.fderiv_right le_rfl).clm_apply contDiff_const

theorem hasCompactSupport_partial {f : Position → ℝ} (hf : HasCompactSupport f)
    (v : Position) : HasCompactSupport (dirPartial f v) := hf.fderiv_apply ℝ v

theorem partial_convolution {f g : Position → ℝ}
    (hf : LocallyIntegrable f volume) (hg : ContDiff ℝ 1 g)
    (hcg : HasCompactSupport g) (x v : Position) :
    dirPartial (f ⋆[lsmul ℝ ℝ, volume] g) v x =
      (f ⋆[lsmul ℝ ℝ, volume] dirPartial g v) x := by
  unfold dirPartial
  rw [(hcg.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hf hg x).fderiv]
  exact convolution_precompR_apply (lsmul ℝ ℝ) hf (hcg.fderiv ℝ)
    (hg.continuous_fderiv (by norm_num)) x v

theorem coordinateLaplacian_eq_partials {f : Position → ℝ} {x : Position}
    (hf : ContDiffAt ℝ 2 f x) :
    coordinateLaplacian f x = ∑ a : Fin 3, dirPartial (dirPartial f (axis a)) (axis a) x := by
  apply Finset.sum_congr rfl
  intro a _
  exact second_deriv_affine_line hf

theorem coordinateLaplacian_convolution {f g : Position → ℝ}
    (hf : LocallyIntegrable f volume) (hg : ContDiff ℝ 2 g)
    (hcg : HasCompactSupport g) (x : Position) :
    coordinateLaplacian (f ⋆[lsmul ℝ ℝ, volume] g) x =
      ∫ y, f y * coordinateLaplacian g (x-y) := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hc : ContDiff ℝ 2 (f ⋆[lsmul ℝ ℝ, volume] g) :=
    hcg.contDiff_convolution_right (lsmul ℝ ℝ) hf hg
  rw [coordinateLaplacian_eq_partials (hc.contDiffAt)]
  have hpart (a : Fin 3) : dirPartial (f ⋆[lsmul ℝ ℝ, volume] g) (axis a) =
      f ⋆[lsmul ℝ ℝ, volume] dirPartial g (axis a) := by
    ext y
    exact partial_convolution hf hg1 hcg y (axis a)
  simp_rw [hpart]
  have hgpart (a : Fin 3) : ContDiff ℝ 1 (dirPartial g (axis a)) := by
    exact contDiff_partial hg (axis a)
  simp_rw [partial_convolution hf (hgpart _) (hasCompactSupport_partial hcg _) x]
  simp only [convolution_def, lsmul_apply, smul_eq_mul]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards [] with y
    rw [coordinateLaplacian_eq_partials hg.contDiffAt, Finset.mul_sum]
  · intro a _
    have hs := hasCompactSupport_partial (hasCompactSupport_partial hcg (axis a)) (axis a)
    have hd : Continuous (dirPartial (dirPartial g (axis a)) (axis a)) := by
      exact ((hgpart a).continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact hs.convolutionExists_right (lsmul ℝ ℝ) hf hd x

theorem dirPartial_sub {f g : Position → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (v : Position) :
    dirPartial (fun x => f x-g x) v = fun x => dirPartial f v x-dirPartial g v x := by
  ext x
  exact congrArg (fun T : Position →L[ℝ] ℝ => T v) (fderiv_sub (hf x) (hg x))

theorem coordinateLaplacian_sub {f g : Position → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Position) :
    coordinateLaplacian (fun y => f y-g y) x =
      coordinateLaplacian f x-coordinateLaplacian g x := by
  rw [coordinateLaplacian_eq_partials (hf.sub hg).contDiffAt,
    coordinateLaplacian_eq_partials hf.contDiffAt, coordinateLaplacian_eq_partials hg.contDiffAt,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [dirPartial_sub (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num))]
  rw [dirPartial_sub ((contDiff_partial (n := 1) hf (axis a)).differentiable (by norm_num))
    ((contDiff_partial (n := 1) hg (axis a)).differentiable (by norm_num))]

theorem coordinateLaplacian_quadratic (z x : Position) (c : ℝ) :
    coordinateLaplacian (fun y => c*‖y-z‖^2) x = 6*c := by
  unfold coordinateLaplacian
  have he (a : Fin 3) : (fun t : ℝ => c*‖x+t • axis a-z‖^2) =
      fun t : ℝ => c*(‖x-z‖^2+2*t*(x-z) a+t^2) := by
    ext t
    rw [show x+t • axis a-z = (x-z)+t • axis a by module, norm_sq_axis_shift]
  simp_rw [he]
  have hd (a : Fin 3) : deriv (fun t : ℝ => c*(‖x-z‖^2+2*t*(x-z) a+t^2)) =
      fun t => c*(2*(x-z) a+2*t) := by
    ext t
    convert (((hasDerivAt_const t (‖x-z‖^2)).add
      (((hasDerivAt_id t).const_mul 2).mul_const ((x-z) a))).add
      ((hasDerivAt_id t).pow 2)).const_mul c |>.deriv using 1
    all_goals norm_num [id_eq, Pi.add_apply]
  simp_rw [hd]
  have hdd (a : Fin 3) : deriv (fun t : ℝ => c*(2*(x-z) a+2*t)) 0 = 2*c := by
    convert (((hasDerivAt_const 0 (2*(x-z) a)).add
      ((hasDerivAt_id 0).const_mul 2)).const_mul c).deriv using 1
    all_goals norm_num [id_eq, Pi.add_apply]
    ring
  simp_rw [hdd]
  simp
  ring

def WeakLaplacianLower (f : Position → ℝ) (U : Set Position) (c : ℝ) : Prop :=
  ∀ φ : Position → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ U → (∀ x, 0 ≤ φ x) →
      c*(∫ x, φ x) ≤ ∫ x, f x*coordinateLaplacian φ x

theorem normed_bump_reflect_tsupport (φ : ContDiffBump (0 : Position)) (x : Position) :
    tsupport (fun y => φ.normed volume (x-y)) ⊆ Metric.closedBall x φ.rOut := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro y hy
  have hy' : x-y ∈ Function.support (φ.normed volume) := hy
  rw [φ.support_normed_eq] at hy'
  have hh : ‖x-y‖ < φ.rOut := by simpa using hy'
  simpa only [Metric.mem_closedBall, dist_eq_norm_sub'] using hh.le

theorem continuous_convolution_comm (f g : Position → ℝ) :
    f ⋆[lsmul ℝ ℝ, volume] g = g ⋆[lsmul ℝ ℝ, volume] f := by
  ext x
  rw [convolution_eq_swap]
  apply integral_congr_ae
  filter_upwards [] with y
  exact mul_comm _ _

theorem weakLaplacianLower_mollify {f : Position → ℝ} {U : Set Position} {c : ℝ}
    (hf : LocallyIntegrable f volume) (hw : WeakLaplacianLower f U c)
    (φ : ContDiffBump (0 : Position)) {x : Position}
    (hx : Metric.closedBall x φ.rOut ⊆ U) :
    c ≤ coordinateLaplacian (f ⋆[lsmul ℝ ℝ, volume] φ.normed volume) x := by
  have ht := normed_bump_reflect_tsupport φ x
  have hc : HasCompactSupport (fun y => φ.normed volume (x-y)) :=
    (isCompact_closedBall x φ.rOut).of_isClosed_subset (isClosed_tsupport _) ht
  have hs : ContDiff ℝ ∞ (fun y => φ.normed volume (x-y)) :=
    φ.contDiff_normed.comp (contDiff_const.sub contDiff_id)
  have hb := hw _ hs hc (ht.trans hx) (fun y => φ.nonneg_normed _)
  rw [integral_sub_left_eq_self, φ.integral_normed, mul_one] at hb
  rw [coordinateLaplacian_convolution hf φ.contDiff_normed φ.hasCompactSupport_normed]
  simpa only [coordinateLaplacian_reflect] using hb

theorem integrable_normed_bump_reflect (φ : ContDiffBump (0 : Position)) (x : Position) :
    Integrable (fun y => φ.normed volume (x-y)) := by
  have hc : HasCompactSupport (fun y => φ.normed volume (x-y)) :=
    (isCompact_closedBall x φ.rOut).of_isClosed_subset (isClosed_tsupport _)
      (normed_bump_reflect_tsupport φ x)
  exact (φ.continuous_normed.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport hc

theorem mollify_le_of_bound {f : Position → ℝ} {U : Set Position} {a : ℝ}
    (hf : LocallyIntegrable f volume) (hbound : ∀ y ∈ U, f y ≤ a)
    (φ : ContDiffBump (0 : Position)) {x : Position}
    (hx : Metric.closedBall x φ.rOut ⊆ U) :
    (f ⋆[lsmul ℝ ℝ, volume] φ.normed volume) x ≤ a := by
  have hi := (φ.hasCompactSupport_normed (μ := volume)).convolutionExists_right (lsmul ℝ ℝ) hf
    φ.continuous_normed x
  calc
    _ ≤ ∫ y, a*φ.normed volume (x-y) := by
      apply integral_mono hi ((integrable_normed_bump_reflect φ x).const_mul a)
      intro y
      by_cases hy : φ.normed volume (x-y) = 0
      · simp [hy]
      · have hm : y ∈ tsupport (fun y => φ.normed volume (x-y)) := subset_closure hy
        exact mul_le_mul_of_nonneg_right
          (hbound y (hx (normed_bump_reflect_tsupport φ x hm))) (φ.nonneg_normed _)
    _ = a := by rw [integral_const_mul, integral_sub_left_eq_self, φ.integral_normed, mul_one]

theorem no_maximum_of_strict_weakLaplacian {f : Position → ℝ} {o : Position} {R c : ℝ}
    (hf : Continuous f) (hR : 0 < R) (hc : 0 < c)
    (hw : WeakLaplacianLower f (Metric.ball o R) c)
    (hmax : ∀ y ∈ Metric.ball o R, f y ≤ f o) : False := by
  let r := R/2
  let η := c/12
  let κ := η*r^2/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have he : ∀ᶠ y in 𝓝 o, dist (f y) (f o) < κ :=
    hf.continuousAt.eventually (Metric.ball_mem_nhds _ hκ)
  obtain ⟨d, hd, hfd⟩ := Metric.mem_nhds_iff.mp he
  let e := min (R/4) (d/2)
  have hep : 0 < e := by dsimp [e]; positivity
  let φ : ContDiffBump (0 : Position) := ⟨e/2, e, by positivity, by linarith⟩
  have hφR : φ.rOut ≤ R/4 := min_le_left _ _
  have hφd : φ.rOut < d := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  let u := f ⋆[lsmul ℝ ℝ, volume] φ.normed volume
  have hu : ContDiff ℝ 2 u := φ.hasCompactSupport_normed.contDiff_convolution_right
    (lsmul ℝ ℝ) hf.locallyIntegrable φ.contDiff_normed
  have hcenter : f o-κ ≤ u o := by
    have hh := φ.dist_normed_convolution_le (μ := volume) (g := f) (x₀ := o) hf.aestronglyMeasurable (fun y hy =>
      (hfd (lt_trans hy hφd)).le)
    rw [continuous_convolution_comm] at hh
    rw [Real.dist_eq] at hh
    exact sub_le_iff_le_add.mpr (by linarith [(abs_le.mp hh).1])
  have hinside {x : Position} (hx : x ∈ Metric.closedBall o r) :
      Metric.closedBall x φ.rOut ⊆ Metric.ball o R := by
    intro y hy
    apply lt_of_le_of_lt (dist_triangle y x o)
    have hxy : dist y x ≤ φ.rOut := hy
    have hxo : dist x o ≤ r := hx
    dsimp [r] at hxo
    linarith
  have hub {x : Position} (hx : x ∈ Metric.closedBall o r) : u x ≤ f o :=
    mollify_le_of_bound hf.locallyIntegrable hmax φ (hinside hx)
  let v : Position → ℝ := fun x => u x-η*‖x-o‖^2
  have hq : ContDiff ℝ 2 (fun y : Position => η*‖y-o‖^2) :=
    contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ)
  have hv : ContDiff ℝ 2 v := hu.sub hq
  obtain ⟨x, hx, hxm⟩ := (isCompact_closedBall o r).exists_isMaxOn
    ⟨o, Metric.mem_closedBall_self hr.le⟩ hv.continuous.continuousOn
  have hvcenter : f o-η*r^2 < v o := by
    dsimp [v]
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero]
    dsimp [κ] at hcenter
    nlinarith [sq_pos_of_pos hr]
  have hxi : x ∈ Metric.ball o r := by
    by_contra hn
    have hdist : ‖x-o‖ = r := by
      apply le_antisymm
      · exact hx
      · exact le_of_not_gt hn
    have hvb : v x ≤ f o-η*r^2 := by dsimp [v]; rw [hdist]; linarith [hub hx]
    have hcx : v o ≤ v x := hxm (Metric.mem_closedBall_self hr.le)
    linarith
  have hlmax : IsLocalMax v x := hxm.isLocalMax
    (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hxi) Metric.ball_subset_closedBall)
  have hl := coordinateLaplacian_nonpos_of_local_max hlmax hv.continuous.continuousAt
  have hp := weakLaplacianLower_mollify hf.locallyIntegrable hw φ (hinside hx)
  change coordinateLaplacian (fun y => u y-η*‖y-o‖^2) x ≤ 0 at hl
  rw [coordinateLaplacian_sub hu hq, coordinateLaplacian_quadratic] at hl
  change c ≤ coordinateLaplacian u x at hp
  dsimp [η] at hl
  linarith

theorem coordinateLaplacian_congr_nhds {f g : Position → ℝ} {x : Position}
    (h : f =ᶠ[𝓝 x] g) : coordinateLaplacian f x = coordinateLaplacian g x := by
  apply Finset.sum_congr rfl
  intro a _
  have ht : Tendsto (fun t : ℝ => x+t • axis a) (𝓝 0) (𝓝 x) := by
    simpa using (show ContinuousAt (fun t : ℝ => x+t • axis a) 0 by fun_prop).tendsto
  have he : (fun t : ℝ => f (x+t • axis a)) =ᶠ[𝓝 0]
      (fun t : ℝ => g (x+t • axis a)) := ht.eventually h
  exact he.deriv.deriv_eq

theorem coordinateLaplacian_zero (x : Position) :
    coordinateLaplacian (fun _ => (0 : ℝ)) x = 0 := by
  simp [coordinateLaplacian]

theorem coordinateLaplacian_eq_zero_of_notMem_tsupport {f : Position → ℝ} {x : Position}
    (h : x ∉ tsupport f) : coordinateLaplacian f x = 0 := by
  rw [coordinateLaplacian_congr_nhds (notMem_tsupport_iff_eventuallyEq.mp h)]
  exact coordinateLaplacian_zero x

end NeutralAtom
end
end
end

end OAI
