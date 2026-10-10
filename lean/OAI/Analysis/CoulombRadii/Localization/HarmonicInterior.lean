import Mathlib
import OAI.Analysis.CoulombRadii.Variational.CorrectionDensity

namespace OAI

section
section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
noncomputable section
namespace NeutralAtom
theorem dirPartial_mul {f g : Position → ℝ} {x v : Position}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dirPartial (fun y => f y*g y) v x = f x*dirPartial g v x+g x*dirPartial f v x := by
  change fderiv ℝ (f*g) x v = _
  rw [fderiv_mul hf hg]
  simp [dirPartial]

theorem dirPartial_add {f g : Position → ℝ} {x v : Position}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dirPartial (fun y => f y+g y) v x = dirPartial f v x+dirPartial g v x := by
  change fderiv ℝ (f+g) x v = _
  rw [fderiv_add hf hg]
  rfl

theorem coordinateLaplacian_mul {f g : Position → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Position) :
    coordinateLaplacian (fun y => f y*g y) x =
      f x*coordinateLaplacian g x+g x*coordinateLaplacian f x+
        2*∑ a : Fin 3, dirPartial f (axis a) x*dirPartial g (axis a) x := by
  have hf1 := hf.differentiable (by norm_num)
  have hg1 := hg.differentiable (by norm_num)
  have hpf (a) : Differentiable ℝ (dirPartial f (axis a)) :=
    (contDiff_partial (n := 1) hf (axis a)).differentiable (by norm_num)
  have hpg (a) : Differentiable ℝ (dirPartial g (axis a)) :=
    (contDiff_partial (n := 1) hg (axis a)).differentiable (by norm_num)
  rw [coordinateLaplacian_eq_partials (hf.mul hg).contDiffAt,
    coordinateLaplacian_eq_partials hg.contDiffAt,
    coordinateLaplacian_eq_partials hf.contDiffAt]
  have hh (a : Fin 3) : dirPartial (dirPartial (fun y => f y*g y) (axis a)) (axis a) x =
      f x*dirPartial (dirPartial g (axis a)) (axis a) x+
      g x*dirPartial (dirPartial f (axis a)) (axis a) x+
      2*(dirPartial f (axis a) x*dirPartial g (axis a) x) := by
    have heq : dirPartial (fun y => f y*g y) (axis a) =
        fun y => f y*dirPartial g (axis a) y+g y*dirPartial f (axis a) y :=
      funext (fun y => dirPartial_mul (hf1 y) (hg1 y))
    rw [heq, dirPartial_add
      (f := fun y => f y*dirPartial g (axis a) y)
      (g := fun y => g y*dirPartial f (axis a) y)
      (by simpa only [Pi.mul_def] using (hf1 x).mul (hpg a x))
      (by simpa only [Pi.mul_def] using (hg1 x).mul (hpf a x)),
      dirPartial_mul (hf1 x) (hpg a x), dirPartial_mul (hg1 x) (hpf a x)]
    ring
  simp_rw [hh, Finset.sum_add_distrib, Finset.mul_sum]

theorem dirPartial_regularizedKernel {ε : ℝ} (hε : ε ≠ 0)
    (a : Fin 3) (x : Position) :
    dirPartial (regularizedKernel ε) (axis a) x =
      -(x a)*(‖x‖^2+ε^2)^(-3/2 : ℝ) := by
  have hq : 0 < ‖x‖^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hε)
  have heq : (fun t : ℝ => regularizedKernel ε (x+t • axis a)) =
      fun t : ℝ => (‖x‖^2+2*t*x a+t^2+ε^2)^(-1/2 : ℝ) := by
    ext t
    rw [regularizedKernel, norm_sq_axis_shift]
  have hd : HasDerivAt (fun t : ℝ => ‖x‖^2+2*t*x a+t^2+ε^2) (2*x a) 0 := by
    convert (((hasDerivAt_const 0 (‖x‖^2)).add
      (((hasDerivAt_id 0).const_mul 2).mul_const (x a))).add
      ((hasDerivAt_id 0).pow 2)).add_const (ε^2) using 1
    all_goals first | rfl | norm_num
  have hr := hd.rpow_const (p := (-1/2 : ℝ)) (Or.inl (by simpa using hq.ne'))
  have he := deriv_affine_line (v := axis a) (t := 0)
    (by simpa using (contDiff_regularizedKernel hε).differentiable (by norm_num) x)
  simp only [zero_smul, add_zero] at he
  unfold dirPartial
  rw [← he, heq]
  rw [hr.deriv]
  norm_num
  ring_nf
  all_goals simp

def coulombPartial (a : Fin 3) (x : Position) : ℝ :=
  -(x a)*(‖x‖^2)^(-3/2 : ℝ)

theorem regularizedPartial_tendsto {ε : ℕ → ℝ} (hε : ∀ n, ε n ≠ 0)
    (hlim : Tendsto ε atTop (𝓝 0)) (a : Fin 3) {x : Position} (hx : x ≠ 0) :
    Tendsto (fun n => dirPartial (regularizedKernel (ε n)) (axis a) x)
      atTop (𝓝 (coulombPartial a x)) := by
  simp only [dirPartial_regularizedKernel (hε _)]
  have hh : Tendsto (fun n => ‖x‖^2+(ε n)^2) atTop (𝓝 (‖x‖^2)) := by
    simpa using tendsto_const_nhds.add (hlim.pow 2)
  exact tendsto_const_nhds.mul (hh.rpow_const (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))))

theorem dirPartial_regularizedKernel_bound {ε : ℝ} (hε : ε ≠ 0)
    (a : Fin 3) {x : Position} (hx : x ≠ 0) :
    ‖dirPartial (regularizedKernel ε) (axis a) x‖ ≤ (coulombKernel x)^2 := by
  rw [dirPartial_regularizedKernel hε]
  simp only [norm_mul, norm_neg, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.rpow_nonneg (add_nonneg (sq_nonneg ‖x‖) (sq_nonneg ε)) (-3/2 : ℝ))]
  have hnorm : |x a| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x a
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hr : (‖x‖^2+ε^2)^(-3/2 : ℝ) ≤ (‖x‖^2)^(-3/2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ε]) (by norm_num)
  have he : ‖x‖*(‖x‖^2)^(-3/2 : ℝ) = (coulombKernel x)^2 := by
    rw [← Real.rpow_natCast_mul (norm_nonneg x)]
    norm_num [Real.rpow_neg hpos.le, coulombKernel]
    field_simp
  exact (mul_le_mul hnorm hr (by positivity) (norm_nonneg x)).trans_eq he

theorem locallyIntegrable_coulombKernel_sq :
    LocallyIntegrable (fun x => (coulombKernel x)^2) volume := by
  intro x
  refine ⟨Metric.ball 0 (‖x‖+1), IsOpen.mem_nhds Metric.isOpen_ball ?_,
    coulombKernel_sq_integrableOn_ball _⟩
  simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖x‖

theorem regularizedPartial_integral_tendsto {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (a : Fin 3) {φ : Position → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, dirPartial (regularizedKernel (ε n)) (axis a) x*φ x)
      atTop (𝓝 (∫ x, coulombPartial a x*φ x)) := by
  have hae : ∀ᵐ x : Position ∂volume, x ≠ 0 := volume.ae_ne 0
  have hb : Integrable (fun x => (coulombKernel x)^2*‖φ x‖) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_coulombKernel_sq.integrable_smul_right_of_hasCompactSupport hφ.norm hφc.norm
  apply tendsto_integral_of_dominated_convergence (fun x => (coulombKernel x)^2*‖φ x‖)
  · intro n
    exact ((contDiff_partial (n := ∞) (by simpa using contDiff_regularizedKernel (hε n).ne')
      (axis a)).continuous.mul hφ).aestronglyMeasurable
  · exact hb
  · intro n
    filter_upwards [hae] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (dirPartial_regularizedKernel_bound (hε n).ne' a hx)
      (norm_nonneg _)
  · filter_upwards [hae] with x hx
    exact (regularizedPartial_tendsto (fun n => (hε n).ne') hlim a hx).mul_const (φ x)

theorem weak_harmonic_reproduction {h χ : Position → ℝ} {U : Set Position}
    (hh : Continuous h) (hharm : HasWeakLaplacian h U (fun _ => 0))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    (∫ x, coulombKernel x*(h x*coordinateLaplacian χ x)) +
      2*∑ a : Fin 3, ∫ x, coulombPartial a x*(h x*dirPartial χ (axis a) x) =
      4*Real.pi*(h 0*χ 0) := by
  let ε : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hcdelta : Continuous (coordinateLaplacian χ) := continuous_coordinateLaplacian hχ2
  have hcsdelta : HasCompactSupport (coordinateLaplacian χ) :=
    hasCompactSupport_coordinateLaplacian hχc
  have hcp (a : Fin 3) : ContDiff ℝ ∞ (dirPartial χ (axis a)) :=
    contDiff_partial (by simpa using hχ) (axis a)
  have hcsp (a : Fin 3) := hasCompactSupport_partial hχc (axis a)
  have hn (n : ℕ) :
      (∫ x, regularizedKernel (ε n) x*(h x*coordinateLaplacian χ x)) +
        2*∑ a : Fin 3, ∫ x, dirPartial (regularizedKernel (ε n)) (axis a) x*
          (h x*dirPartial χ (axis a) x) =
        ∫ x, regularizedCharge (ε n) x*(h x*χ x) := by
    have hK := contDiff_regularizedKernel (hε n).ne'
    have hK2 : ContDiff ℝ 2 (regularizedKernel (ε n)) :=
      hK.of_le (by exact WithTop.coe_le_coe.mpr le_top)
    have hpK (a : Fin 3) : Continuous (dirPartial (regularizedKernel (ε n)) (axis a)) :=
      (contDiff_partial (n := ∞) (by simpa using hK) (axis a)).continuous
    have hq : Continuous (regularizedCharge (ε n)) := by
      have heq : regularizedCharge (ε n) = fun x => -coordinateLaplacian (regularizedKernel (ε n)) x := by
        ext x
        rw [laplacian_regularizedKernel (hε n).ne']
        ring
      rw [heq]
      exact (continuous_coordinateLaplacian hK2).neg
    have hiK : Integrable (fun x => regularizedKernel (ε n) x*(h x*coordinateLaplacian χ x)) :=
      (hK.continuous.mul (hh.mul hcdelta)).integrable_of_hasCompactSupport
        (hcsdelta.mul_left.mul_left)
    have hiq : Integrable (fun x => regularizedCharge (ε n) x*(h x*χ x)) :=
      (hq.mul (hh.mul hχ.continuous)).integrable_of_hasCompactSupport (hχc.mul_left.mul_left)
    have hip (a : Fin 3) : Integrable (fun x => dirPartial (regularizedKernel (ε n)) (axis a) x*
        (h x*dirPartial χ (axis a) x)) :=
      ((hpK a).mul (hh.mul (hcp a).continuous)).integrable_of_hasCompactSupport
        ((hcsp a).mul_left.mul_left)
    have he := hharm (fun x => χ x*regularizedKernel (ε n) x) (hχ.mul hK)
      hχc.mul_right (by exact (closure_mono (Function.support_mul_subset_left _ _)).trans hχU)
    have heq : (fun x => h x*coordinateLaplacian (fun y => χ y*regularizedKernel (ε n) y) x) =
        fun x => (regularizedKernel (ε n) x*(h x*coordinateLaplacian χ x)-
          regularizedCharge (ε n) x*(h x*χ x)) +
          2*∑ a : Fin 3, dirPartial (regularizedKernel (ε n)) (axis a) x*
              (h x*dirPartial χ (axis a) x) := by
      ext x
      rw [coordinateLaplacian_mul hχ2 hK2, laplacian_regularizedKernel (hε n).ne']
      simp only [Fin.sum_univ_three]
      ring
    have hisub : Integrable (fun x => regularizedKernel (ε n) x*(h x*coordinateLaplacian χ x)-
        regularizedCharge (ε n) x*(h x*χ x)) := by
      simpa only [Pi.sub_def] using hiK.sub hiq
    have hisum : Integrable (fun x => 2*∑ a : Fin 3,
        dirPartial (regularizedKernel (ε n)) (axis a) x*(h x*dirPartial χ (axis a) x)) :=
      (integrable_finsetSum Finset.univ (fun a _ => hip a)).const_mul 2
    rw [heq, integral_add hisub hisum,
      integral_sub hiK hiq, integral_const_mul, integral_finsetSum _ (fun a _ => hip a)] at he
    simp only [zero_mul, integral_zero] at he
    linarith
  have h1 := regularizedKernel_integral_tendsto hε hεlim (hh.mul hcdelta) hcsdelta.mul_left
  have h2 := tendsto_finsetSum Finset.univ (fun a _ =>
    regularizedPartial_integral_tendsto hε hεlim a (hh.mul (hcp a).continuous) (hcsp a).mul_left)
  have h3 := regularizedCharge_tendsto_dirac hε hεlim (hh.mul hχ.continuous) hχc.mul_left
  exact tendsto_nhds_unique ((h1.add (h2.const_mul 2)).congr' (Filter.Eventually.of_forall hn)) h3

def cutoffHarmonicKernel (χ : Position → ℝ) (x : Position) : ℝ :=
  (coulombKernel x*coordinateLaplacian χ x +
    2*∑ a : Fin 3, coulombPartial a x*dirPartial χ (axis a) x)/(4*Real.pi)

theorem contDiffAt_coulombKernel {x : Position} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ coulombKernel x := by
  have he : coulombKernel = fun x : Position => (‖x‖^2)^(-1/2 : ℝ) :=
    funext coulombKernel_eq_rpow
  rw [he]
  exact (contDiff_norm_sq ℝ).contDiffAt.rpow_const_of_ne
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

theorem contDiffAt_coulombPartial (a : Fin 3) {x : Position} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (coulombPartial a) x := by
  exact (EuclideanSpace.proj a).contDiff.contDiffAt.neg.mul
    ((contDiff_norm_sq ℝ).contDiffAt.rpow_const_of_ne (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)))

theorem contDiff_coordinateLaplacian {χ : Position → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (coordinateLaplacian χ) := by
  have he : coordinateLaplacian χ = fun x => ∑ a : Fin 3,
      dirPartial (dirPartial χ (axis a)) (axis a) x := funext (fun x =>
    coordinateLaplacian_eq_partials
      (hχ.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt)
  rw [he]
  apply ContDiff.sum
  intro a _
  have hp : ContDiff ℝ ∞ (dirPartial χ (axis a)) :=
    contDiff_partial (n := ∞) (by simpa using hχ) (axis a)
  exact contDiff_partial (n := ∞) (by simpa using hp) (axis a)

theorem cutoffHarmonicKernel_eq_zero_of_eventually_const {χ : Position → ℝ} {x : Position}
    {c : ℝ} (hχ : χ =ᶠ[𝓝 x] fun _ => c) : cutoffHarmonicKernel χ x = 0 := by
  have hdelta : coordinateLaplacian χ x = 0 := by
    rw [coordinateLaplacian_congr_nhds hχ]
    simp [coordinateLaplacian]
  have hp (a : Fin 3) : dirPartial χ (axis a) x = 0 := by
    unfold dirPartial
    rw [hχ.fderiv_eq]
    simp
  simp [cutoffHarmonicKernel, hdelta, hp]

theorem hasCompactSupport_cutoffHarmonicKernel {χ : Position → ℝ}
    (hχc : HasCompactSupport χ) : HasCompactSupport (cutoffHarmonicKernel χ) := by
  apply hχc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x hx
  by_contra h
  exact hx (cutoffHarmonicKernel_eq_zero_of_eventually_const
    (notMem_tsupport_iff_eventuallyEq.mp h))

theorem contDiff_cutoffHarmonicKernel {χ : Position → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ =ᶠ[𝓝 (0 : Position)] fun _ => (1 : ℝ)) :
    ContDiff ℝ ∞ (cutoffHarmonicKernel χ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have he : cutoffHarmonicKernel χ =ᶠ[𝓝 (0 : Position)] fun _ => (0 : ℝ) := by
      filter_upwards [hχ0.eventually_nhds] with x hx
      exact cutoffHarmonicKernel_eq_zero_of_eventually_const hx
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hp (a : Fin 3) : ContDiffAt ℝ ∞ (dirPartial χ (axis a)) x :=
      (contDiff_partial (n := ∞) (by simpa using hχ) (axis a)).contDiffAt
    apply ContDiffAt.div_const
    apply ContDiffAt.add
    · exact (contDiffAt_coulombKernel hx).mul (contDiff_coordinateLaplacian hχ).contDiffAt
    · apply contDiffAt_const.mul
      apply ContDiffAt.sum
      intro a _
      exact (contDiffAt_coulombPartial a hx).mul (hp a)

theorem coulombPartial_bound (a : Fin 3) (x : Position) :
    ‖coulombPartial a x‖ ≤ (coulombKernel x)^2 := by
  by_cases hx : x = 0
  · subst x
    simp [coulombPartial, coulombKernel]
  · have hε : ∀ n : ℕ, ((n:ℝ)+1)⁻¹ ≠ 0 := fun n => by positivity
    have hlim : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    exact le_of_tendsto (regularizedPartial_tendsto hε hlim a hx).norm
      (Filter.Eventually.of_forall (fun n => dirPartial_regularizedKernel_bound (hε n) a hx))

theorem measurable_coulombPartial (a : Fin 3) : Measurable (coulombPartial a) := by
  exact (EuclideanSpace.proj a).continuous.measurable.neg.mul
    ((continuous_norm.measurable.pow_const (2 : ℕ)).pow_const (-3/2 : ℝ))

theorem coulombPartial_integrable_mul_compact (a : Fin 3) {φ : Position → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x => coulombPartial a x*φ x) := by
  have hb : Integrable (fun x => (coulombKernel x)^2*‖φ x‖) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_coulombKernel_sq.integrable_smul_right_of_hasCompactSupport hφ.norm hφc.norm
  apply hb.mono' ((measurable_coulombPartial a).aestronglyMeasurable.mul hφ.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => by
    change ‖coulombPartial a x*φ x‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (coulombPartial_bound a x) (norm_nonneg _))

theorem weak_harmonic_reproduction_kernel {h χ : Position → ℝ} {U : Set Position}
    (hh : Continuous h) (hharm : HasWeakLaplacian h U (fun _ => 0))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (hχone : χ 0 = 1) :
    (∫ x, cutoffHarmonicKernel χ x*h x) = h 0 := by
  have hcdelta := (contDiff_coordinateLaplacian hχ).continuous
  have hcsdelta := hasCompactSupport_coordinateLaplacian hχc
  have hcp (a : Fin 3) : Continuous (dirPartial χ (axis a)) :=
    (contDiff_partial (n := ∞) (by simpa using hχ) (axis a)).continuous
  have hcsp (a : Fin 3) := hasCompactSupport_partial hχc (axis a)
  have hiK : Integrable (fun x => coulombKernel x*(h x*coordinateLaplacian χ x)) := by
    simpa only [smul_eq_mul, Pi.mul_apply] using
      locallyIntegrable_coulombKernel.integrable_smul_right_of_hasCompactSupport
        (hh.mul hcdelta) hcsdelta.mul_left
  have hip (a : Fin 3) : Integrable (fun x => coulombPartial a x*(h x*dirPartial χ (axis a) x)) :=
    coulombPartial_integrable_mul_compact a (hh.mul (hcp a)) (hcsp a).mul_left
  have hisum : Integrable (fun x => 2*∑ a : Fin 3, coulombPartial a x*(h x*dirPartial χ (axis a) x)) :=
    (integrable_finsetSum Finset.univ (fun a _ => hip a)).const_mul 2
  have heq : (fun x => cutoffHarmonicKernel χ x*h x) = fun x =>
      (4*Real.pi)⁻¹*((coulombKernel x*(h x*coordinateLaplacian χ x))+
      2*∑ a : Fin 3, coulombPartial a x*(h x*dirPartial χ (axis a) x)) := by
    ext x
    simp only [cutoffHarmonicKernel, Fin.sum_univ_three]
    ring
  rw [heq, integral_const_mul, integral_add hiK hisum, integral_const_mul,
    integral_finsetSum _ (fun a _ => hip a), weak_harmonic_reproduction hh hharm hχ hχc hχU, hχone]
  field_simp

theorem coordinateLaplacian_sub_right (φ : Position → ℝ) (x z : Position) :
    coordinateLaplacian (fun y => φ (y-z)) x = coordinateLaplacian φ (x-z) := by
  unfold coordinateLaplacian
  apply Finset.sum_congr rfl
  intro a _
  have he : (fun t : ℝ => φ ((x+t • axis a)-z)) = fun t => φ ((x-z)+t • axis a) := by
    ext t
    congr 1
    abel
  rw [he]

theorem HasWeakLaplacian.translate {h q : Position → ℝ} {U : Set Position}
    (hh : HasWeakLaplacian h U q) (z : Position) :
    HasWeakLaplacian (fun x => h (z+x)) {x | z+x ∈ U} (fun x => q (z+x)) := by
  intro φ hφ hφc hφU
  have hc : ContDiff ℝ ∞ (fun y => φ (y-z)) := hφ.comp (contDiff_id.sub contDiff_const)
  have hcs : HasCompactSupport (fun y => φ (y-z)) :=
    hφc.comp_homeomorph (Homeomorph.subRight z)
  have hs : tsupport (fun y => φ (y-z)) ⊆ U := by
    have hsub := tsupport_comp_subset_preimage φ (show Continuous (fun y : Position => y-z) by fun_prop)
    intro y hy
    have hy' : y-z ∈ tsupport φ := hsub hy
    have hh' := hφU hy'
    change z+(y-z) ∈ U at hh'
    rw [show z+(y-z) = y by abel] at hh'
    exact hh'
  have he := hh (fun y => φ (y-z)) hc hcs hs
  simp_rw [coordinateLaplacian_sub_right] at he
  have hl := integral_add_left_eq_self (μ := volume) (fun y => h y*coordinateLaplacian φ (y-z)) z
  have hr := integral_add_left_eq_self (μ := volume) (fun y => q y*φ (y-z)) z
  simpa only [add_sub_cancel_left] using hl.trans (he.trans hr.symm)

theorem weak_harmonic_reproduction_at {h χ : Position → ℝ} {U : Set Position}
    (hh : Continuous h) (hharm : HasWeakLaplacian h U (fun _ => 0))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχone : χ 0 = 1)
    {z : Position} (hχU : ∀ x ∈ tsupport χ, z+x ∈ U) :
    (∫ x, cutoffHarmonicKernel χ (x-z)*h x) = h z := by
  have he := weak_harmonic_reproduction_kernel
    (hh.comp (show Continuous (fun x : Position => z+x) by fun_prop))
    (hharm.translate z) hχ hχc hχU hχone
  have hl := integral_add_left_eq_self (μ := volume) (fun x => cutoffHarmonicKernel χ (x-z)*h x) z
  simp only [add_sub_cancel_left] at hl
  simpa only [Function.comp_apply, add_zero] using hl.symm.trans he

theorem harmonic_value_bound {h χ : Position → ℝ} {U W : Set Position} {M : ℝ}
    (hh : Continuous h) (hharm : HasWeakLaplacian h U (fun _ => 0))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχone : χ 0 = 1)
    (hW : IsCompact W) (hM : ∀ x, ‖cutoffHarmonicKernel χ x‖ ≤ M)
    {z : Position} (hχU : ∀ x ∈ tsupport χ, z+x ∈ U)
    (hχW : ∀ x ∈ tsupport χ, z+x ∈ W) :
    ‖h z‖ ≤ M*(∫ x in W, ‖h x‖) := by
  have hzero : ∀ x, x ∉ W → cutoffHarmonicKernel χ (x-z)*h x = 0 := by
    intro x hx
    have hh' : x-z ∉ tsupport χ := by
      intro hm
      have he := hχW (x-z) hm
      rw [show z+(x-z)=x by abel] at he
      exact hx he
    rw [cutoffHarmonicKernel_eq_zero_of_eventually_const
      (notMem_tsupport_iff_eventuallyEq.mp hh'), zero_mul]
  rw [← weak_harmonic_reproduction_at hh hharm hχ hχc hχone hχU,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hi : IntegrableOn (fun x => M * ‖h x‖) W volume :=
    (hh.norm.continuousOn.integrableOn_compact hW).const_mul M
  have hb := norm_integral_le_of_norm_le
    (f := fun x => cutoffHarmonicKernel χ (x-z)*h x) hi
    (Filter.Eventually.of_forall (fun x => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hM (x-z)) (norm_nonneg _)))
  simpa only [integral_const_mul] using hb

theorem harmonic_difference_bound {h χ : Position → ℝ} {U W : Set Position} {L : NNReal}
    (hh : Continuous h) (hharm : HasWeakLaplacian h U (fun _ => 0))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχ0 : χ =ᶠ[𝓝 (0 : Position)] fun _ => (1 : ℝ)) (hW : IsCompact W)
    (hL : LipschitzWith L (cutoffHarmonicKernel χ))
    {z z' : Position} (hχU : ∀ x ∈ tsupport χ, z+x ∈ U)
    (hχU' : ∀ x ∈ tsupport χ, z'+x ∈ U)
    (hχW : ∀ x ∈ tsupport χ, z+x ∈ W)
    (hχW' : ∀ x ∈ tsupport χ, z'+x ∈ W) :
    ‖h z-h z'‖ ≤ (L:ℝ)*(∫ x in W, ‖h x‖)*‖z-z'‖ := by
  have hcQ := (contDiff_cutoffHarmonicKernel hχ hχ0).continuous
  have hi (v : Position) : IntegrableOn (fun x => cutoffHarmonicKernel χ (x-v)*h x) W :=
    ((hcQ.comp (show Continuous (fun x : Position => x-v) by fun_prop)).mul hh).continuousOn.integrableOn_compact hW
  have hrepro (v : Position) (hvU : ∀ x ∈ tsupport χ, v+x ∈ U)
      (hvW : ∀ x ∈ tsupport χ, v+x ∈ W) :
      (∫ x in W, cutoffHarmonicKernel χ (x-v)*h x) = h v := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact weak_harmonic_reproduction_at hh hharm hχ hχc hχ0.eq_of_nhds hvU
    · intro x hx
      have hh' : x-v ∉ tsupport χ := by
        intro hm
        have he := hvW (x-v) hm
        rw [show v+(x-v)=x by abel] at he
        exact hx he
      rw [cutoffHarmonicKernel_eq_zero_of_eventually_const
        (notMem_tsupport_iff_eventuallyEq.mp hh'), zero_mul]
  rw [← hrepro z hχU hχW, ← hrepro z' hχU' hχW', ← integral_sub (hi z) (hi z')]
  have hb : ∀ x, ‖cutoffHarmonicKernel χ (x-z)*h x-cutoffHarmonicKernel χ (x-z')*h x‖ ≤
      ((L:ℝ)*‖z-z'‖)*‖h x‖ := by
    intro x
    rw [← sub_mul, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have he := hL.norm_sub_le (x-z) (x-z')
    simpa only [show (x-z)-(x-z')=z'-z by abel, norm_sub_rev z' z] using he
  have hibound : IntegrableOn (fun x => ((L:ℝ)*‖z-z'‖)*‖h x‖) W volume :=
    (hh.norm.continuousOn.integrableOn_compact hW).const_mul _
  have hbound := norm_integral_le_of_norm_le hibound
    (Filter.Eventually.of_forall hb)
  rw [integral_const_mul] at hbound
  convert hbound using 1
  ring

theorem harmonic_interior_estimates {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : Position) (h : Position → ℝ), Continuous h →
      HasWeakLaplacian h (Metric.ball c (2*r)) (fun _ => 0) →
      (∀ z ∈ Metric.closedBall c r, ‖h z‖ ≤ C*(∫ x in Metric.closedBall c (2*r), ‖h x‖)) ∧
      (∀ z ∈ Metric.closedBall c r, ∀ z' ∈ Metric.closedBall c r,
        ‖h z-h z'‖ ≤ C*(∫ x in Metric.closedBall c (2*r), ‖h x‖)*‖z-z'‖) := by
  let χ : ContDiffBump (0 : Position) := ⟨r/4, r/2, by linarith, by linarith⟩
  have hχ0 : (χ : Position → ℝ) =ᶠ[𝓝 (0 : Position)] fun _ => (1 : ℝ) :=
    χ.eventuallyEq_one
  have hQ := contDiff_cutoffHarmonicKernel χ.contDiff hχ0
  have hQc := hasCompactSupport_cutoffHarmonicKernel χ.hasCompactSupport
  obtain ⟨M, hM⟩ := hQc.exists_bound_of_continuous hQ.continuous
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hQc hQ (by simp)
  let C : ℝ := max M L+1
  have hLC : (L : ℝ) ≤ C := by
    dsimp [C]
    linarith [le_max_right M (L : ℝ)]
  have hMC : M ≤ C := by
    dsimp [C]
    linarith [le_max_left M (L : ℝ)]
  have hC : 0 < C := by
    dsimp [C]
    linarith [le_max_right M (L : ℝ), L.coe_nonneg]
  refine ⟨C, hC, ?_⟩
  intro c h hh hharm
  have hs {z : Position} (hz : z ∈ Metric.closedBall c r) :
      ∀ x ∈ tsupport (χ : Position → ℝ), z+x ∈ Metric.ball c (2*r) := by
    intro x hx
    rw [χ.tsupport_eq] at hx
    have hx' : ‖x‖ ≤ r/2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hz' : ‖z-c‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    rw [Metric.mem_ball, dist_eq_norm, show z+x-c = (z-c)+x by abel]
    exact lt_of_le_of_lt ((norm_add_le _ _).trans (add_le_add hz' hx')) (by linarith)
  have hsW {z : Position} (hz : z ∈ Metric.closedBall c r) :
      ∀ x ∈ tsupport (χ : Position → ℝ), z+x ∈ Metric.closedBall c (2*r) :=
    fun x hx => Metric.ball_subset_closedBall (hs hz x hx)
  have hI : 0 ≤ ∫ x in Metric.closedBall c (2*r), ‖h x‖ := integral_nonneg (fun _ => norm_nonneg _)
  constructor
  · intro z hz
    exact (harmonic_value_bound hh hharm χ.contDiff χ.hasCompactSupport hχ0.eq_of_nhds
      (isCompact_closedBall c (2*r)) hM (hs hz) (hsW hz)).trans (mul_le_mul_of_nonneg_right hMC hI)
  · intro z hz z' hz'
    exact (harmonic_difference_bound hh hharm χ.contDiff χ.hasCompactSupport hχ0
      (isCompact_closedBall c (2*r)) hL (hs hz) (hs hz') (hsW hz) (hsW hz')).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLC hI) (norm_nonneg _))

theorem HasWeakLaplacian.congrOn {h g q : Position → ℝ} {U : Set Position}
    (hh : HasWeakLaplacian h U q) (he : Set.EqOn h g U) : HasWeakLaplacian g U q := by
  intro φ hφ hφc hφU
  calc
    (∫ x, g x*coordinateLaplacian φ x) = ∫ x, h x*coordinateLaplacian φ x := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      change g x*coordinateLaplacian φ x = h x*coordinateLaplacian φ x
      by_cases hx : x ∈ tsupport φ
      · rw [he (hφU hx)]
      · simp only [coordinateLaplacian_eq_zero_of_notMem_tsupport hx, mul_zero]
    _ = _ := hh φ hφ hφc hφU

theorem harmonic_interior_estimates_local {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : Position) (h : Position → ℝ),
      ContinuousOn h (Metric.ball c (3*r)) →
      HasWeakLaplacian h (Metric.ball c (2*r)) (fun _ => 0) →
      (∀ z ∈ Metric.closedBall c r, ‖h z‖ ≤ C*(∫ x in Metric.closedBall c (2*r), ‖h x‖)) ∧
      (∀ z ∈ Metric.closedBall c r, ∀ z' ∈ Metric.closedBall c r,
        ‖h z-h z'‖ ≤ C*(∫ x in Metric.closedBall c (2*r), ‖h x‖)*‖z-z'‖) := by
  obtain ⟨C, hC, hest⟩ := harmonic_interior_estimates hr
  refine ⟨C, hC, ?_⟩
  intro c h hh hharm
  let η : ContDiffBump c := ⟨2*r, 5*r/2, by positivity, by linarith⟩
  let g : Position → ℝ := fun x => η x*h x
  have hgOn : ContinuousOn g (Metric.ball c (3*r)) := η.continuous.continuousOn.mul hh
  have hg : Continuous g := hgOn.continuous_of_tsupport_subset Metric.isOpen_ball (by
    intro x hx
    have hx' : x ∈ tsupport (η : Position → ℝ) :=
      closure_mono (Function.support_mul_subset_left _ _) hx
    rw [η.tsupport_eq] at hx'
    have hd : dist x c ≤ 5*r/2 := hx'
    exact lt_of_le_of_lt hd (by linarith))
  have he : Set.EqOn g h (Metric.closedBall c (2*r)) := by
    intro x hx
    dsimp [g]
    rw [η.one_of_mem_closedBall hx, one_mul]
  have hgarm : HasWeakLaplacian g (Metric.ball c (2*r)) (fun _ => 0) :=
    hharm.congrOn (fun x hx => (he (Metric.ball_subset_closedBall hx)).symm)
  have hI : (∫ x in Metric.closedBall c (2*r), ‖g x‖) =
      ∫ x in Metric.closedBall c (2*r), ‖h x‖ := by
    apply setIntegral_congr_fun measurableSet_closedBall
    intro x hx
    change ‖g x‖ = ‖h x‖
    rw [he hx]
  have hes {z : Position} (hz : z ∈ Metric.closedBall c r) : g z = h z :=
    he (Metric.closedBall_subset_closedBall (by linarith) hz)
  obtain ⟨hval, hdiff⟩ := hest c g hg hgarm
  constructor
  · intro z hz
    simpa only [hes hz, hI] using hval z hz
  · intro z hz z' hz'
    simpa only [hes hz, hes hz', hI] using hdiff z hz z' hz'

end NeutralAtom
end

end
end

end OAI
