import Mathlib
import OAI.Analysis.CoulombRadii.Variational.Axis

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

theorem WeakLaplacianLower.congr {f g : Position → ℝ} {U : Set Position} {c : ℝ}
    (h : WeakLaplacianLower f U c) (he : Set.EqOn f g U) : WeakLaplacianLower g U c := by
  intro φ hφ hc ht hp
  convert h φ hφ hc ht hp using 1
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ tsupport φ
  · rw [he (ht hx)]
  · simp only [coordinateLaplacian_eq_zero_of_notMem_tsupport hx, mul_zero]

theorem WeakLaplacianLower.mono {f : Position → ℝ} {U V : Set Position} {c : ℝ}
    (h : WeakLaplacianLower f U c) (he : V ⊆ U) : WeakLaplacianLower f V c := by
  intro φ hφ hc ht hp
  exact h φ hφ hc (ht.trans he) hp

theorem no_maximum_of_strict_weakLaplacian_local
    {f : Position → ℝ} {o : Position} {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hf : ContinuousOn f (Metric.closedBall o R))
    (hw : WeakLaplacianLower f (Metric.ball o R) c)
    (hm : ∀ x ∈ Metric.ball o R, f x ≤ f o) : False := by
  let f' : C(Metric.closedBall o R, ℝ) := ⟨_, hf.domRestrict⟩
  obtain ⟨g, hg⟩ := f'.exists_restrict_eq Metric.isClosed_closedBall
  have he : Set.EqOn f g (Metric.closedBall o R) := by
    intro x hx
    exact (congrArg (fun u : C(Metric.closedBall o R, ℝ) => u ⟨x, hx⟩) hg).symm
  have heb : Set.EqOn f g (Metric.ball o R) := he.mono Metric.ball_subset_closedBall
  have hcenter := he (Metric.mem_closedBall_self hR.le)
  exact no_maximum_of_strict_weakLaplacian g.continuous hR hc (hw.congr heb)
    (by intro x hx; rw [← heb hx, ← hcenter]; exact hm x hx)

theorem integrable_mul_compact_of_continuousAt {f g : Position → ℝ}
    (hf : ∀ x ∈ tsupport g, ContinuousAt f x) (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (fun x => f x*g x) := by
  have hc : Continuous (fun x => f x*g x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ tsupport g
    · exact (hf x hx).mul hg.continuousAt
    · have he : (fun y => f y*g y) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        change g y = 0 at hy
        simp only [hy, mul_zero]
      exact continuousAt_const.congr_of_eventuallyEq he
  exact hc.integrable_of_hasCompactSupport (hgc.mono (Function.support_mul_subset_right f g))

theorem tsupport_dirPartial_subset (f : Position → ℝ) (v : Position) :
    tsupport (dirPartial f v) ⊆ tsupport f := tsupport_fderiv_apply_subset ℝ v

theorem integral_mul_coordinateLaplacian_eq {f φ : Position → ℝ}
    (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, f x * coordinateLaplacian φ x) =
      ∫ x, coordinateLaplacian f x * φ x := by
  have hpφ (v : Position) : ContDiff ℝ ∞ (dirPartial φ v) :=
    contDiff_partial (by simpa using hφ) v
  have hppφ (v : Position) : ContDiff ℝ ∞ (dirPartial (dirPartial φ v) v) :=
    contDiff_partial (by simpa using hpφ v) v
  have hdφ (v : Position) := (hpφ v).differentiable (by simp)
  have hiφ (v : Position) := hasCompactSupport_partial hφc v
  have hpcont (v : Position) (x : Position) (hx : x ∈ tsupport φ) :
      ContDiffAt ℝ 1 (dirPartial f v) x :=
    ((hf x hx).fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply
      contDiffAt_const
  have hppcont (v : Position) (x : Position) (hx : x ∈ tsupport φ) :
      ContinuousAt (dirPartial (dirPartial f v) v) x :=
    (((hpcont v x hx).fderiv_right (show (0 : WithTop ℕ∞)+1 ≤ 1 by norm_num)).clm_apply
      contDiffAt_const).continuousAt
  have hleft (v : Position) : Integrable (fun x => f x*dirPartial (dirPartial φ v) v x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => (hf x ((tsupport_dirPartial_subset φ v)
        (tsupport_dirPartial_subset (dirPartial φ v) v hx))).continuousAt)
      (hppφ v).continuous
      (hasCompactSupport_partial (hiφ v) v)
  have hright (v : Position) : Integrable (fun x => dirPartial (dirPartial f v) v x*φ x) :=
    integrable_mul_compact_of_continuousAt (hppcont v) hφ.continuous hφc
  have hcross (v : Position) : Integrable (fun x => dirPartial f v x*dirPartial φ v x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => (hpcont v x (tsupport_dirPartial_subset φ v hx)).continuousAt)
      (hpφ v).continuous (hiφ v)
  have hfg (v : Position) : Integrable (fun x => f x*dirPartial φ v x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => (hf x (tsupport_dirPartial_subset φ v hx)).continuousAt)
      (hpφ v).continuous (hiφ v)
  have hfpg (v : Position) : Integrable (fun x => dirPartial f v x*φ x) :=
    integrable_mul_compact_of_continuousAt (fun x hx => (hpcont v x hx).continuousAt)
      hφ.continuous hφc
  have hby (v : Position) :
      (∫ x, f x*dirPartial (dirPartial φ v) v x) = ∫ x, dirPartial (dirPartial f v) v x*φ x := by
    calc
      _ = -(∫ x, dirPartial f v x*dirPartial φ v x) :=
        integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
          (hcross v) (hleft v) (hfg v)
          (fun x hx => (hf x (tsupport_dirPartial_subset φ v hx)).differentiableAt (by norm_num))
          (fun x _ => hdφ v x)
      _ = _ := by
        have he : (∫ x, dirPartial f v x*dirPartial φ v x) =
            -(∫ x, dirPartial (dirPartial f v) v x*φ x) :=
          integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
            (hright v) (hcross v) (hfpg v)
            (fun x hx => (hpcont v x hx).differentiableAt (by norm_num))
            (fun x _ => hφ.differentiable (by simp) x)
        rw [he, neg_neg]
  calc
    _ = ∫ x, ∑ a : Fin 3, f x*dirPartial (dirPartial φ (axis a)) (axis a) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [coordinateLaplacian_eq_partials (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt, Finset.mul_sum]
    _ = ∑ a : Fin 3, ∫ x, f x*dirPartial (dirPartial φ (axis a)) (axis a) x :=
      integral_finsetSum _ (fun a _ => hleft (axis a))
    _ = ∑ a : Fin 3, ∫ x, dirPartial (dirPartial f (axis a)) (axis a) x*φ x := by
      simp_rw [hby]
    _ = ∫ x, ∑ a : Fin 3, dirPartial (dirPartial f (axis a)) (axis a) x*φ x :=
      (integral_finsetSum _ (fun a _ => hright (axis a))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport φ
      · rw [coordinateLaplacian_eq_partials (hf x hx), Finset.sum_mul]
      · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, Finset.sum_const_zero]

theorem continuousAt_coordinateLaplacian {f : Position → ℝ} {x : Position}
    (hf : ContDiffAt ℝ 2 f x) : ContinuousAt (coordinateLaplacian f) x := by
  have hp (v : Position) : ContDiffAt ℝ 1 (dirPartial f v) x :=
    (hf.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply contDiffAt_const
  have hpp (v : Position) : ContinuousAt (dirPartial (dirPartial f v) v) x :=
    (((hp v).fderiv_right (show (0 : WithTop ℕ∞)+1 ≤ 1 by norm_num)).clm_apply
      contDiffAt_const).continuousAt
  have he : coordinateLaplacian f =ᶠ[𝓝 x]
      fun y => ∑ a : Fin 3, dirPartial (dirPartial f (axis a)) (axis a) y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact coordinateLaplacian_eq_partials hy
  have hsum : ContinuousAt (fun y => ∑ a : Fin 3,
      dirPartial (dirPartial f (axis a)) (axis a) y) x :=
    tendsto_finsetSum _ (fun a _ => hpp (axis a))
  exact hsum.congr_of_eventuallyEq he

theorem continuous_coordinateLaplacian {f : Position → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (coordinateLaplacian f) :=
  continuous_iff_continuousAt.mpr fun _ => continuousAt_coordinateLaplacian hf.contDiffAt

theorem hasCompactSupport_coordinateLaplacian {f : Position → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (coordinateLaplacian f) := by
  apply hf.mono'
  intro x hx
  by_contra hn
  exact hx (coordinateLaplacian_eq_zero_of_notMem_tsupport hn)

def HasWeakLaplacian (f : Position → ℝ) (U : Set Position) (q : Position → ℝ) : Prop :=
  ∀ φ : Position → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∫ x, f x*coordinateLaplacian φ x) = ∫ x, q x*φ x

theorem HasWeakLaplacian.mono {f q : Position → ℝ} {U V : Set Position}
    (h : HasWeakLaplacian f U q) (he : V ⊆ U) : HasWeakLaplacian f V q := by
  intro φ hφ hc ht
  exact h φ hφ hc (ht.trans he)

theorem HasWeakLaplacian.sub_smooth_lower {f q b : Position → ℝ}
    {U : Set Position} {c : ℝ} (ho : IsOpen U)
    (hf : ContinuousOn f U) (hq : ContinuousOn q U) (hb : ContDiffOn ℝ 2 b U)
    (hw : HasWeakLaplacian f U q) (hl : ∀ x ∈ U, c ≤ q x-coordinateLaplacian b x) :
    WeakLaplacianLower (fun x => f x-b x) U c := by
  intro φ hφ hc ht hp
  have hb' (x : Position) (hx : x ∈ U) := hb.contDiffAt (ho.mem_nhds hx)
  have hiq : Integrable (fun x => q x*φ x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => hq.continuousAt (ho.mem_nhds (ht hx))) hφ.continuous hc
  have hib : Integrable (fun x => coordinateLaplacian b x*φ x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => continuousAt_coordinateLaplacian (hb' x (ht hx))) hφ.continuous hc
  have hts : tsupport (coordinateLaplacian φ) ⊆ tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    exact hx (coordinateLaplacian_eq_zero_of_notMem_tsupport hn)
  have hφl := continuous_coordinateLaplacian (hφ.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by exact WithTop.coe_le_coe.mpr le_top))
  have hφlc := hasCompactSupport_coordinateLaplacian hc
  have hif : Integrable (fun x => f x*coordinateLaplacian φ x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => hf.continuousAt (ho.mem_nhds (ht (hts hx)))) hφl hφlc
  have hib' : Integrable (fun x => b x*coordinateLaplacian φ x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => (hb' x (ht (hts hx))).continuousAt) hφl hφlc
  simp_rw [sub_mul]
  rw [integral_sub hif hib', hw φ hφ hc ht,
    integral_mul_coordinateLaplacian_eq (fun x hx => hb' x (ht hx)) hφ hc,
    ← integral_sub hiq hib, ← integral_const_mul]
  apply integral_mono (hφ.continuous.integrable_of_hasCompactSupport hc |>.const_mul c)
    (hiq.sub hib)
  intro x
  change c*φ x ≤ q x*φ x-coordinateLaplacian b x*φ x
  by_cases hx : x ∈ tsupport φ
  · rw [← sub_mul]
    exact mul_le_mul_of_nonneg_right (hl x (ht hx)) (hp x)
  · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, sub_self, le_refl]

theorem weakLaplacian_le_at_local_max {f q b : Position → ℝ} {U : Set Position}
    {o : Position} (ho : IsOpen U) (hx : o ∈ U)
    (hf : ContinuousOn f U) (hq : ContinuousOn q U) (hb : ContDiffOn ℝ 2 b U)
    (hw : HasWeakLaplacian f U q) (hm : IsLocalMax (fun x => f x-b x) o) :
    q o ≤ coordinateLaplacian b o := by
  by_contra hn
  have hg : 0 < q o-coordinateLaplacian b o := sub_pos.mpr (lt_of_not_ge hn)
  let c := (q o-coordinateLaplacian b o)/2
  have hc : 0 < c := by dsimp [c]; positivity
  have hg' : c < q o-coordinateLaplacian b o := by dsimp [c]; linarith
  have hcont : ContinuousAt (fun x => q x-coordinateLaplacian b x) o :=
    (hq.continuousAt (ho.mem_nhds hx)).sub
      (continuousAt_coordinateLaplacian (hb.contDiffAt (ho.mem_nhds hx)))
  have he : ∀ᶠ x in 𝓝 o, x ∈ U ∧ c < q x-coordinateLaplacian b x ∧
      f x-b x ≤ f o-b o := by
    filter_upwards [ho.mem_nhds hx, hcont.eventually (Ioi_mem_nhds hg'), hm] with x hx hg hm
    exact ⟨hx, hg, hm⟩
  obtain ⟨d, hd, hd'⟩ := Metric.mem_nhds_iff.mp he
  let R := d/2
  have hR : 0 < R := by dsimp [R]; positivity
  have hRd : R < d := by dsimp [R]; linarith
  have hlocal (x : Position) (hx : x ∈ Metric.closedBall o R) :
      x ∈ U ∧ c < q x-coordinateLaplacian b x ∧ f x-b x ≤ f o-b o :=
    hd' (lt_of_le_of_lt hx hRd)
  have hsub : Metric.ball o R ⊆ U :=
    fun x hx => (hlocal x (Metric.ball_subset_closedBall hx)).1
  exact no_maximum_of_strict_weakLaplacian_local hR hc
    ((hf.sub hb.continuousOn).mono (fun x hx => (hlocal x hx).1))
    ((hw.mono hsub).sub_smooth_lower Metric.isOpen_ball (hf.mono hsub) (hq.mono hsub)
      (hb.mono hsub) (fun x hx => (hlocal x (Metric.ball_subset_closedBall hx)).2.1.le))
    (fun x hx => (hlocal x (Metric.ball_subset_closedBall hx)).2.2)

theorem coordinateLaplacian_neg (f : Position → ℝ) (x : Position) :
    coordinateLaplacian (fun y => -f y) x = -coordinateLaplacian f x := by
  unfold coordinateLaplacian
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have he : deriv (fun t : ℝ => -f (x+t • axis a)) =
      -deriv (fun t : ℝ => f (x+t • axis a)) := by ext t; exact deriv.neg
  rw [he, deriv.neg]

theorem HasWeakLaplacian.neg {f q : Position → ℝ} {U : Set Position}
    (h : HasWeakLaplacian f U q) :
    HasWeakLaplacian (fun x => -f x) U (fun x => -q x) := by
  intro φ hφ hc ht
  simpa only [neg_mul, integral_neg] using congrArg Neg.neg (h φ hφ hc ht)

theorem weakLaplacian_ge_at_local_min {f q b : Position → ℝ} {U : Set Position}
    {o : Position} (ho : IsOpen U) (hx : o ∈ U)
    (hf : ContinuousOn f U) (hq : ContinuousOn q U) (hb : ContDiffOn ℝ 2 b U)
    (hw : HasWeakLaplacian f U q) (hm : IsLocalMin (fun x => f x-b x) o) :
    coordinateLaplacian b o ≤ q o := by
  have hm' : IsLocalMax (fun x => (-f x)-(-b x)) o := by
    filter_upwards [hm] with x hx
    linarith
  have h := weakLaplacian_le_at_local_max ho hx hf.neg hq.neg hb.neg hw.neg hm'
  rw [coordinateLaplacian_neg] at h
  exact neg_le_neg_iff.mp h

theorem coordinateLaplacian_add_at {f g : Position → ℝ} {x : Position}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    coordinateLaplacian (fun y => f y+g y) x = coordinateLaplacian f x+coordinateLaplacian g x := by
  rw [coordinateLaplacian_eq_partials (hf.add hg), coordinateLaplacian_eq_partials hf,
    coordinateLaplacian_eq_partials hg, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have he : dirPartial (fun y => f y+g y) (axis a) =ᶠ[𝓝 x]
      fun y => dirPartial f (axis a) y+dirPartial g (axis a) y := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hy hz
    exact congrArg (fun T : Position →L[ℝ] ℝ => T (axis a))
      (fderiv_add (hy.differentiableAt (by norm_num)) (hz.differentiableAt (by norm_num)))
  have hfd : DifferentiableAt ℝ (dirPartial f (axis a)) x :=
    ((hf.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply
      contDiffAt_const).differentiableAt_one
  have hgd : DifferentiableAt ℝ (dirPartial g (axis a)) x :=
    ((hg.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply
      contDiffAt_const).differentiableAt_one
  change fderiv ℝ _ x (axis a) = _
  rw [he.fderiv_eq]
  exact congrArg (fun T : Position →L[ℝ] ℝ => T (axis a)) (fderiv_add hfd hgd)

theorem coordinateLaplacian_const_mul (f : Position → ℝ) (x : Position) (c : ℝ) :
    coordinateLaplacian (fun y => c*f y) x = c*coordinateLaplacian f x := by
  unfold coordinateLaplacian
  simp only [deriv_const_mul_field', deriv_const_mul_field, Finset.mul_sum]

def punctured : Set Position := {x | x ≠ 0}

theorem isOpen_punctured : IsOpen punctured := isClosed_singleton.isOpen_compl

theorem contDiffOn_radialPower (p : ℝ) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (radialPower p) punctured := by
  exact (contDiff_id.norm_sq ℝ).contDiffOn.rpow_const_of_ne
    (fun _ hx => pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

def radialBarrier (a d : ℝ) (x : Position) : ℝ :=
  a*radialPower (-2) x + d*(radialPower (-1) x+radialPower (-3) x)

theorem contDiffOn_radialBarrier (a d : ℝ) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (radialBarrier a d) punctured :=
  (contDiffOn_const.mul (contDiffOn_radialPower (-2) n)).add
    (contDiffOn_const.mul ((contDiffOn_radialPower (-1) n).add (contDiffOn_radialPower (-3) n)))

theorem radialBarrier_scaled {x : Position} (hx : x ≠ 0) (a d : ℝ) :
    (‖x‖^2)^2 * radialBarrier a d x = a+d*((‖x‖^2)+(‖x‖^2)⁻¹) := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  norm_num [radialBarrier, radialPower, Real.rpow_neg_natCast, Real.rpow_neg_one]
  field_simp

theorem laplacian_radialBarrier_scaled {x : Position} (hx : x ≠ 0) (a d : ℝ) :
    (‖x‖^2)^3 * coordinateLaplacian (radialBarrier a d) x =
      12*a+d*(2*(‖x‖^2)+30*(‖x‖^2)⁻¹) := by
  have hcp (p : ℝ) : ContDiffAt ℝ 2 (radialPower p) x :=
    (contDiffOn_radialPower p 2).contDiffAt (isOpen_punctured.mem_nhds hx)
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  unfold radialBarrier
  rw [coordinateLaplacian_add_at (contDiffAt_const.mul (hcp (-2)))
      (contDiffAt_const.mul ((hcp (-1)).add (hcp (-3)))),
    coordinateLaplacian_const_mul, coordinateLaplacian_const_mul,
    coordinateLaplacian_add_at (hcp (-1)) (hcp (-3))]
  simp only [coordinateLaplacian_radialPower hx]
  norm_num [Real.rpow_neg_natCast, Real.rpow_neg_one]
  field_simp

def radialPenalty (x : Position) : ℝ := ‖x‖^2+(‖x‖^2)⁻¹

theorem radialPenalty_pos {x : Position} (hx : x ≠ 0) : 0 < radialPenalty x := by
  unfold radialPenalty
  exact add_pos (sq_pos_of_pos (norm_pos_iff.mpr hx)) (inv_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hx)))

theorem continuousOn_radialPenalty : ContinuousOn radialPenalty punctured :=
  (continuous_norm.pow 2).continuousOn.add
    ((continuous_norm.pow 2).continuousOn.inv₀ (fun _ hx => pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)))

theorem exists_penalized_max {V : Position → ℝ} {C δ : ℝ} {x₀ : Position}
    (hV : ContinuousOn V punctured) (hC : ∀ x ≠ 0, V x ≤ C) (hδ : 0 < δ)
    (hx₀ : x₀ ≠ 0) :
    ∃ x, x ≠ 0 ∧ ∀ y ≠ 0, V y-δ*radialPenalty y ≤ V x-δ*radialPenalty x := by
  let T := C-(V x₀-δ*radialPenalty x₀)+1
  have hT : 0 < T := by
    dsimp [T]
    nlinarith [hC x₀ hx₀, mul_pos hδ (radialPenalty_pos hx₀)]
  let α := min (‖x₀‖^2) (δ/T)/2
  let β := max (‖x₀‖^2) (T/δ)+1
  have hq₀ : 0 < ‖x₀‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx₀)
  have hα : 0 < α := by dsimp [α]; positivity
  have hβ : 0 < β := by dsimp [β]; positivity
  have hαq : α ≤ ‖x₀‖^2 := by
    dsimp [α]
    have := min_le_left (‖x₀‖^2) (δ/T)
    linarith
  have hαT : α ≤ δ/T := by
    dsimp [α]
    have := min_le_right (‖x₀‖^2) (δ/T)
    have := div_pos hδ hT
    linarith
  have hqβ : ‖x₀‖^2 ≤ β := by
    dsimp [β]
    have := le_max_left (‖x₀‖^2) (T/δ)
    linarith
  have hTβ : T/δ ≤ β := by
    dsimp [β]
    have := le_max_right (‖x₀‖^2) (T/δ)
    linarith
  let K : Set Position := {x | α ≤ ‖x‖^2 ∧ ‖x‖^2 ≤ β}
  have hKclosed : IsClosed K := isClosed_Icc.preimage (continuous_norm.pow 2)
  have hKsub : K ⊆ Metric.closedBall 0 (β+1) := by
    intro x hx
    simp only [Metric.mem_closedBall, dist_zero_right]
    have hu := hx.2
    nlinarith [sq_nonneg (‖x‖-1)]
  have hK : IsCompact K := (isCompact_closedBall (0 : Position) (β+1)).of_isClosed_subset hKclosed hKsub
  have hKp : K ⊆ punctured := by
    intro x hx hn
    subst x
    simpa using lt_of_lt_of_le hα hx.1
  have hcont : ContinuousOn (fun x => V x-δ*radialPenalty x) K :=
    (hV.sub (continuousOn_const.mul continuousOn_radialPenalty)).mono hKp
  obtain ⟨x, hx, hxm⟩ := hK.exists_isMaxOn ⟨x₀, hαq, hqβ⟩ hcont
  refine ⟨x, hKp hx, ?_⟩
  intro y hy
  by_cases hyK : y ∈ K
  · exact hxm hyK
  have hqy : 0 < ‖y‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hy)
  have hYP : T < δ*radialPenalty y := by
    by_cases hyl : α ≤ ‖y‖^2
    · have hyh : β < ‖y‖^2 := lt_of_not_ge (fun hn => hyK ⟨hyl, hn⟩)
      have htq : T < (‖y‖^2)*δ := (div_lt_iff₀ hδ).mp (lt_of_le_of_lt hTβ hyh)
      dsimp [radialPenalty]
      nlinarith [mul_nonneg hδ.le (inv_nonneg.mpr hqy.le)]
    · have hylo : ‖y‖^2 < δ/T := lt_of_lt_of_le (lt_of_not_ge hyl) hαT
      have htq : (‖y‖^2)*T < δ := (lt_div_iff₀ hT).mp hylo
      have htid : T < δ/(‖y‖^2) := (lt_div_iff₀ hqy).mpr (by nlinarith)
      dsimp [radialPenalty]
      rw [div_eq_mul_inv] at htid
      nlinarith [mul_pos hδ hqy]
  have hxm₀ : V x₀-δ*radialPenalty x₀ ≤ V x-δ*radialPenalty x := hxm ⟨hαq, hqβ⟩
  dsimp [T] at hYP
  linarith [hC y hy]

theorem exists_penalized_min {V : Position → ℝ} {B δ : ℝ} {x₀ : Position}
    (hV : ContinuousOn V punctured) (hB : ∀ x ≠ 0, B ≤ V x) (hδ : 0 < δ)
    (hx₀ : x₀ ≠ 0) :
    ∃ x, x ≠ 0 ∧ ∀ y ≠ 0, V x+δ*radialPenalty x ≤ V y+δ*radialPenalty y := by
  obtain ⟨x, hx, hxm⟩ := exists_penalized_max hV.neg (C := -B)
    (fun y hy => neg_le_neg (hB y hy)) hδ hx₀
  refine ⟨x, hx, ?_⟩
  intro y hy
  have hh := hxm y hy
  simp only [Pi.neg_apply] at hh
  linarith

end NeutralAtom
end
end
end

end OAI
