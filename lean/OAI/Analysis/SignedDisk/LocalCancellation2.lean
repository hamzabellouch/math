import OAI.Analysis.SignedDisk.LocalCancellation1

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real

noncomputable section

namespace SignedDisk

namespace LocalCancellation

lemma integrable_bounded_pairing {b F : ℂ → ℂ} (hb : Integrable b)
    (hF : AEStronglyMeasurable F) {M : ℝ} (hM : ∀ y, ‖F y‖ ≤ M) :
    Integrable (fun y => F y*b y) := by
  apply (hb.norm.const_mul M).mono' (hF.mul hb.aestronglyMeasurable)
  filter_upwards with y
  change ‖F y * b y‖ ≤ M * ‖b y‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)

lemma position_bound {F : ℂ → ℂ} (hF : ∀ y, ‖F y‖ ≤ 1) (x : ℂ)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ R) :
    ∀ y, ‖star (y-x)*F y‖ ≤ R := by
  intro y
  by_cases hy : F y = 0
  · simpa only [hy, mul_zero, norm_zero] using hR0
  · rw [norm_mul, norm_star]
    simpa only [mul_one] using mul_le_mul (hR y hy) (hF y) (norm_nonneg _) hR0

variable {ι : Type*} [Fintype ι]

/-- The decisive corrected active increment, prior to substitution of the dyadic powers.
The zero moment is the exact one furnished by two balanced kernels, not a bound. -/
lemma corrected_increment_bound {Cs α δ ρ : ℝ} (b : ι → ErrorPiece Cs) (hCs : 0 ≤ Cs)
    (hα : α ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hρ : 0 ≤ ρ)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) {D : Set ℂ} (hD : MeasurableSet D)
    (hFb : ∀ y, ‖F y‖ ≤ 1) (hFD : ∀ y, F y ≠ 0 → y ∈ D) (x z : ℂ)
    (hz : (1 : ℝ)/2 ≤ ‖z-x‖) (hD3 : ∀ y ∈ D, ‖y-x‖ ≤ 3)
    (hzero : ∑ d, ∫ y, star (y-x)*F y*(b d).density y = 0) :
    ‖∑ d, ∫ y, F y*(b d).density y‖ ≤
      2*ρ*coarseMass b δ univ+7*coarseMass b δ (D \ Metric.ball z ρ)+
      ((L : ℝ)+2*(3*(L : ℝ)+1))*Cs*δ^(2*(1-α))*errorPrice b α := by
  classical
  have hnorm : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ (3 : ℝ) := fun y hy => hD3 y (hFD y hy)
  have hH : ‖(star (z-x))⁻¹‖ ≤ (2 : ℝ) := by
    rw [norm_inv, norm_star]
    have hn : 0 < ‖z-x‖ := by linarith
    rw [inv_eq_one_div, div_le_iff₀ hn]
    linarith
  have hcorr : LipschitzWith (L+2*(3*L+1)) (fun y => correction x z y*F y) :=
    corrected_lipschitz (M := 1) (R := 3) (H := 2) hF hFb x z hnorm hH
  have he (d : ι) : (∫ y, correction x z y*F y*(b d).density y) =
      (∫ y, F y*(b d).density y) - (star (z-x))⁻¹*(∫ y, star (y-x)*F y*(b d).density y) := by
    have hf := integrable_bounded_pairing (b d).integrable hF.continuous.aestronglyMeasurable hFb
    have hm : Integrable (fun y => star (y-x)*F y*(b d).density y) :=
      integrable_bounded_pairing (b d).integrable
        ((by fun_prop : Continuous (fun y : ℂ => star (y-x))).mul hF.continuous).aestronglyMeasurable
        (position_bound hFb x (by norm_num) hnorm)
    have hid : (fun y => correction x z y*F y*(b d).density y) =
        fun y => F y*(b d).density y - (star (z-x))⁻¹*(star (y-x)*F y*(b d).density y) := by
      funext y
      simp only [correction, div_eq_mul_inv]
      ring
    rw [hid, integral_sub hf (hm.const_mul _), integral_const_mul]
  have hall : (∑ d, ∫ y, correction x z y*F y*(b d).density y) =
      ∑ d, ∫ y, F y*(b d).density y := by
    simp_rw [he]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hzero, mul_zero, sub_zero]
  rw [← hall]
  have hsplit : (∑ d, ∫ y, correction x z y*F y*(b d).density y) =
      (∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), ∫ y, correction x z y*F y*(b d).density y)+
      (∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2), ∫ y, correction x z y*F y*(b d).density y) := by
    simpa only [not_le] using (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun d => δ^2 ≤ (b d).size) (fun d => ∫ y, correction x z y*F y*(b d).density y)).symm
  rw [hsplit]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · calc
      _ ≤ ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size),
          ‖∫ y, correction x z y*F y*(b d).density y‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size),
          (2*ρ*(∫ y, ‖(b d).density y‖)+7*(∫ y in D \ Metric.ball z ρ, ‖(b d).density y‖)) :=
        Finset.sum_le_sum (fun d _ => corrected_pairing_cap (b d).integrable hD hFb hFD x z hρ hz hD3)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        simp only [coarseMass, Measure.restrict_univ]
  · exact fine_pairing_bound b hCs hα hδ hδ1 hcorr

end LocalCancellation

namespace DiskKernels

lemma kernel_nonneg {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x y : ℂ) :
    0 ≤ kernel k x y := tail_nonneg k _

lemma kernel_le_one {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x y : ℂ) :
    kernel k x y ≤ 1 := tail_le_one k _

lemma complex_kernel_lipschitz {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x : ℂ) :
    LipschitzWith M (fun y => (kernel k x y : ℂ)) := by
  simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitzWith.comp (kernel_lipschitz k x)

lemma complex_kernel_bound {a b : ℝ} {M : ℝ≥0} (k : RadiusDensity a b M) (x y : ℂ) :
    ‖(kernel k x y : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg k x y)] using kernel_le_one k x y

lemma difference_bound {a b c d : ℝ} {M N : ℝ≥0}
    (k : RadiusDensity a b M) (l : RadiusDensity c d N) (x y : ℂ) :
    ‖((kernel l x y : ℂ) - kernel k x y)‖ ≤ 1 := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [kernel_nonneg k x y, kernel_nonneg l x y, kernel_le_one k x y, kernel_le_one l x y]

lemma difference_support {r δ ε : ℝ} {M N : ℝ≥0}
    (k : RadiusDensity (r-δ) (r+δ) M) (l : RadiusDensity (r-ε) (r+ε) N)
    (hεδ : ε ≤ δ) (x y : ℂ) (h : (kernel l x y : ℂ) - kernel k x y ≠ 0) :
    |‖y-x‖-r| ≤ δ := by
  by_cases hlo : ‖y-x‖ < r-δ
  · have hk : kernel k x y = 1 := kernel_one k x (by simpa only [Metric.mem_ball, dist_eq_norm] using hlo)
    have hl : kernel l x y = 1 := kernel_one l x (by
      simp only [Metric.mem_ball, dist_eq_norm]
      linarith)
    exact False.elim (h (by simp only [hk, hl, sub_self]))
  · by_cases hup : r+δ ≤ ‖y-x‖
    · have hk : kernel k x y = 0 := kernel_zero k x (by
        simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hup)
      have hl : kernel l x y = 0 := kernel_zero l x (by
        simp only [Metric.mem_ball, dist_eq_norm, not_lt]
        linarith)
      exact False.elim (h (by simp only [hk, hl, sub_self]))
    · rw [abs_le]
      constructor <;> linarith

/-- At every point away from the boundary circle, all such mixtures tend to
    the actual sharp disk. No convergence of the chosen radius densities is assumed. -/
lemma tendsto_kernel {r : ℝ} {δ : ℕ → ℝ} {M : ℕ → ℝ≥0}
    (k : ∀ n, RadiusDensity (r-δ n) (r+δ n) (M n))
    (hδ : Tendsto δ atTop (𝓝 0)) (x y : ℂ) (hy : ‖y-x‖ ≠ r) :
    Tendsto (fun n => kernel (k n) x y) atTop
      (𝓝 ((Metric.ball x r).indicator (fun _ => (1 : ℝ)) y)) := by
  by_cases h : ‖y-x‖ < r
  · have he : ∀ᶠ n in atTop, kernel (k n) x y = 1 := by
      filter_upwards [hδ.eventually_lt_const (sub_pos.mpr h)] with n hn
      exact kernel_one (k n) x (by
        simp only [Metric.mem_ball, dist_eq_norm]
        linarith)
    have hmem : y ∈ Metric.ball x r := by simpa only [Metric.mem_ball, dist_eq_norm] using h
    rw [indicator_of_mem hmem]
    exact tendsto_const_nhds.congr' (he.mono fun _ hn => hn.symm)
  · have hh : r < ‖y-x‖ := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hy)
    have he : ∀ᶠ n in atTop, kernel (k n) x y = 0 := by
      filter_upwards [hδ.eventually_lt_const (sub_pos.mpr hh)] with n hn
      exact kernel_zero (k n) x (by
        simp only [Metric.mem_ball, dist_eq_norm, not_lt]
        linarith)
    have hmem : y ∉ Metric.ball x r := by simpa only [Metric.mem_ball, dist_eq_norm] using h
    rw [indicator_of_notMem hmem]
    exact tendsto_const_nhds.congr' (he.mono fun _ hn => hn.symm)

/-- Dominated convergence of an arbitrary sequence of mixtures against each
    actual absolutely continuous finite vector measure. -/
lemma tendsto_kernel_pairing {r : ℝ} {δ : ℕ → ℝ} {M : ℕ → ℝ≥0}
    (k : ∀ n, RadiusDensity (r-δ n) (r+δ n) (M n))
    (hδ : Tendsto δ atTop (𝓝 0)) (x : ℂ) {b : ℂ → ℂ} (hb : Integrable b) :
    Tendsto (fun n => ∫ y, (kernel (k n) x y : ℂ)*b y) atTop
      (𝓝 (∫ y in Metric.ball x r, b y)) := by
  rw [← integral_indicator measurableSet_ball]
  apply tendsto_integral_of_dominated_convergence (fun y => ‖b y‖)
  · intro n
    exact (complex_kernel_lipschitz (k n) x).continuous.aestronglyMeasurable.mul hb.aestronglyMeasurable
  · exact hb.norm
  · intro n
    filter_upwards with y
    change ‖(kernel (k n) x y : ℂ)*b y‖ ≤ ‖b y‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (complex_kernel_bound (k n) x y)
  · have hcircle : ∀ᵐ y : ℂ, ‖y-x‖ ≠ r := by
      simpa only [Metric.mem_sphere, dist_eq_norm] using (measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume x r))
    filter_upwards [hcircle] with y hy
    have h := (Complex.continuous_ofReal.tendsto _).comp (tendsto_kernel k hδ x y hy)
    have hm := h.mul_const (b y)
    convert! hm using 1
    by_cases hmem : y ∈ Metric.ball x r
    · simp only [indicator_of_mem hmem, Complex.ofReal_one, one_mul]
    · simp only [indicator_of_notMem hmem, Complex.ofReal_zero, zero_mul]

end DiskKernels

namespace LocalCancellation
open DiskGeometry

variable {ι : Type*} [Fintype ι]

theorem size_step {Cs α δ ρ U : ℝ} (b : ι → ErrorPiece Cs)
    (hCs : 0 ≤ Cs) (hα : α ≤ 1) (hδ : 0 < δ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδρ : δ ≤ ρ^2/1600) (hU : 0 < U) :
    ∃ E : Set ℂ, MeasurableSet E ∧
      volume E ≤
        (ENNReal.ofReal U)⁻¹ ^ 2 *
          (ENNReal.ofReal (156*δ/ρ)*ENNReal.ofReal (coarseMass b δ univ)*ENNReal.ofReal (coarseMass b δ univ)) +
        (ENNReal.ofReal U)⁻¹ *
          ((ENNReal.ofReal (6*Real.pi)*ENNReal.ofReal (2*(200*δ/ρ^2)))*ENNReal.ofReal (coarseMass b δ univ)) ∧
      ∀ x ∉ E, ∀ r ∈ Icc (1 : ℝ) 2, ∀ (L : ℝ≥0) (F : ℂ → ℂ),
        LipschitzWith L F → (∀ y, ‖F y‖ ≤ 1) →
        (∀ y, F y ≠ 0 → y ∈ thinShell x r δ) →
        (U ≤ coarseMass b δ (thinShell x r δ) →
          (∑ d, ∫ y, star (y-x)*F y*(b d).density y) = 0) →
        ‖∑ d, ∫ y, F y*(b d).density y‖ ≤
          2*ρ*coarseMass b δ univ+14*U+
            ((L : ℝ)+2*(3*(L : ℝ)+1))*Cs*δ^(2*(1-α))*errorPrice b α := by
  obtain ⟨E, hE, hEv, hcap⟩ := shell_concentration (coarseMeasure b δ) (0 : Measure ℂ)
    hρ hρ1 hδ hδρ (le_refl 0) hU
  refine ⟨E, hE, ?_, ?_⟩
  · simpa only [coarseMeasure_apply b δ MeasurableSet.univ, zero_div, add_zero, mul_one] using hEv
  · intro x hx r hr L F hF hFb hFD hzero
    have hδ1 : δ ≤ 1 := by nlinarith [sq_nonneg (ρ-1)]
    have hδq : δ ≤ 1/4 := by nlinarith [sq_nonneg (ρ-1)]
    have hM0 : 0 ≤ coarseMass b δ univ := by
      rw [coarseMass_univ]
      exact Finset.sum_nonneg (fun d _ => (b d).mass_nonneg)
    have hf0 : 0 ≤ Cs*δ^(2*(1-α))*errorPrice b α :=
      mul_nonneg (mul_nonneg hCs (Real.rpow_nonneg hδ.le _)) (errorPrice_nonneg b α)
    by_cases hactive : U ≤ coarseMass b δ (thinShell x r δ)
    · have hact : ENNReal.ofReal U ≤ coarseMeasure b δ (thinShell x r δ) := by
        rw [coarseMeasure_apply b δ (measurableSet_thinShell x r δ)]
        exact ENNReal.ofReal_le_ofReal hactive
      obtain ⟨z, hz, hzc⟩ := hcap x hx r hr hact (by simp)
      have hzc' : coarseMass b δ (thinShell x r δ \ Metric.ball z ρ) ≤ 2*U := by
        rw [zero_add, coarseMeasure_apply b δ ((measurableSet_thinShell x r δ).diff measurableSet_ball)] at hzc
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hzc
      have hzbound : 1/2 ≤ ‖z-x‖ := by
        simpa only [norm_sub_rev] using (shell_center_bounds hr hδq hz).1
      have hD3 : ∀ y ∈ thinShell x r δ, ‖y-x‖ ≤ 3 := by
        intro y hy
        simpa only [norm_sub_rev] using (shell_center_bounds hr hδq hy).2
      have hc := corrected_increment_bound b hCs hα hδ.le hδ1 hρ.le hF
        (measurableSet_thinShell x r δ) hFb hFD x z hzbound hD3 (hzero hactive)
      nlinarith
    · have hi := increment_bound b hCs hα hδ.le hδ1 hF
        (measurableSet_thinShell x r δ) hFb hFD
      have hx0 : 0 ≤ 2*ρ*coarseMass b δ univ := by positivity
      have hL : (L : ℝ) ≤ (L : ℝ)+2*(3*(L : ℝ)+1) := by linarith [L.coe_nonneg]
      have hh := mul_le_mul_of_nonneg_right hL hf0
      nlinarith

end LocalCancellation

namespace DiskGeometry

lemma thinShell_eq_diff {x : ℂ} {r δ : ℝ} :
    thinShell x r δ = Metric.closedBall x (r+δ) \ Metric.ball x (r-δ) := by
  ext y
  simp only [thinShell, mem_ofPred_eq, abs_le, Set.mem_sdiff, Metric.mem_closedBall,
    Metric.mem_ball, dist_eq_norm, not_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- Exact area of an annulus, including the inner and outer circles. -/
lemma volume_thinShell (x : ℂ) {r δ : ℝ} (hδ : 0 ≤ δ) (hr : δ ≤ r) :
    volume (thinShell x r δ) = ENNReal.ofReal (4*Real.pi*r*δ) := by
  have hi : 0 ≤ r-δ := sub_nonneg.mpr hr
  have ho : 0 ≤ r+δ := by linarith
  rw [thinShell_eq_diff, measure_sdiff (fun y hy => Metric.ball_subset_closedBall
    (Metric.ball_subset_ball (by linarith) hy)) measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne,
    Complex.volume_closedBall, Complex.volume_ball]
  rw [← ENNReal.ofReal_pow ho, ← ENNReal.ofReal_pow hi]
  rw [← (ENNReal.ofReal_coe_nnreal : ENNReal.ofReal (NNReal.pi : ℝ) = (NNReal.pi : ℝ≥0∞))]
  change ENNReal.ofReal ((r+δ)^2) * ENNReal.ofReal Real.pi -
    ENNReal.ofReal ((r-δ)^2) * ENNReal.ofReal Real.pi = ENNReal.ofReal (4*Real.pi*r*δ)
  rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _),
    ← ENNReal.ofReal_sub _ (mul_nonneg (sq_nonneg _) Real.pi_pos.le)]
  congr 1
  ring

lemma measurableSet_shellPairs (r δ : ℝ) :
    MeasurableSet {p : ℂ × ℂ | p.2 ∈ thinShell p.1 r δ} := by
  exact measurableSet_le (by fun_prop : Measurable (fun p : ℂ × ℂ => |‖p.2-p.1‖-r|)) measurable_const

def shellMass (ν : Measure ℂ) (r δ : ℝ) (x : ℂ) : ℝ≥0∞ := ν (thinShell x r δ)

lemma measurable_shellMass (ν : Measure ℂ) [IsFiniteMeasure ν] (r δ : ℝ) :
    Measurable (shellMass ν r δ) :=
  measurable_measure_prodMk_left (measurableSet_shellPairs r δ)

lemma shell_symm (x y : ℂ) (r δ : ℝ) : y ∈ thinShell x r δ ↔ x ∈ thinShell y r δ := by
  simp only [thinShell, mem_ofPred_eq, norm_sub_rev x y]

/-- The integrated shell mass is its exact area times the total input mass. -/
lemma lintegral_shellMass (ν : Measure ℂ) [IsFiniteMeasure ν] {r δ : ℝ}
    (hδ : 0 ≤ δ) (hr : δ ≤ r) :
    (∫⁻ x, shellMass ν r δ x) = ENNReal.ofReal (4*Real.pi*r*δ)*ν univ := by
  let A : Set (ℂ × ℂ) := {p | p.2 ∈ thinShell p.1 r δ}
  have hA : MeasurableSet A := measurableSet_shellPairs r δ
  have he (x : ℂ) : shellMass ν r δ x = ∫⁻ y, A.indicator 1 (x,y) ∂ν := by
    rw [show (fun y : ℂ => A.indicator 1 (x,y)) = (thinShell x r δ).indicator 1 by
      ext y; exact (indicator_comp_right (fun y : ℂ => (x,y))).symm]
    exact (lintegral_indicator_one (measurableSet_thinShell x r δ)).symm
  simp_rw [he]
  rw [lintegral_lintegral_swap (f := fun x y : ℂ => A.indicator 1 (x,y))
    (measurable_const.indicator hA).aemeasurable]
  have hei (y : ℂ) : (fun x : ℂ => A.indicator (1 : ℂ × ℂ → ℝ≥0∞) (x,y)) =
      (thinShell y r δ).indicator 1 := by
    ext x
    by_cases h : y ∈ thinShell x r δ
    · rw [indicator_of_mem (show (x,y) ∈ A from h), indicator_of_mem ((shell_symm x y r δ).mp h)]
      rfl
    · rw [indicator_of_notMem (show (x,y) ∉ A from h), indicator_of_notMem (fun hx => h ((shell_symm x y r δ).mpr hx))]
  simp_rw [hei, lintegral_indicator_one (measurableSet_thinShell _ r δ), volume_thinShell _ hδ hr]
  exact lintegral_const _

lemma shellMass_exception (ν : Measure ℂ) [IsFiniteMeasure ν] {r δ U : ℝ}
    (hδ : 0 ≤ δ) (hr : δ ≤ r) (hU : 0 < U) :
    MeasurableSet {x | ENNReal.ofReal U ≤ shellMass ν r δ x} ∧
    volume {x | ENNReal.ofReal U ≤ shellMass ν r δ x} ≤
      ENNReal.ofReal (4*Real.pi*r*δ)*ν univ / ENNReal.ofReal U := by
  refine ⟨measurableSet_le measurable_const (measurable_shellMass ν r δ), ?_⟩
  have h := meas_ge_le_lintegral_div (μ := (volume : Measure ℂ))
    (measurable_shellMass ν r δ).aemeasurable (ENNReal.ofReal_pos.mpr hU).ne' ENNReal.ofReal_ne_top
  rwa [lintegral_shellMass ν hδ hr] at h

/-- A shell whose radius is sufficiently close to an endpoint is contained
    in the endpoint annulus; this covers forced endpoint radii as well. -/
lemma thinShell_subset_endpoint {x : ℂ} {r a δ : ℝ} (hra : |r-a| ≤ δ) :
    thinShell x r δ ⊆ thinShell x a (2*δ) := by
  intro y hy
  change |‖y-x‖-r| ≤ δ at hy
  change |‖y-x‖-a| ≤ 2*δ
  calc
    _ = |(‖y-x‖-r)+(r-a)| := by congr 1; ring
    _ ≤ |‖y-x‖-r|+|r-a| := abs_add_le _ _
    _ ≤ 2*δ := by linarith

end DiskGeometry

namespace DiskScales

def width (δ : ℝ) (n : ℕ) : ℝ := δ*(1/2 : ℝ)^n

lemma width_pos {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : 0 < width δ n := by
  unfold width
  positivity

lemma width_le {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) : width δ n ≤ δ := by
  unfold width
  exact mul_le_of_le_one_right hδ (pow_le_one₀ (by norm_num) (by norm_num))

lemma width_succ (δ : ℝ) (n : ℕ) : width δ (n+1) = width δ n / 2 := by
  simp only [width, pow_succ]
  ring

lemma width_antitone {δ : ℝ} (hδ : 0 ≤ δ) : Antitone (width δ) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [width_succ]
  have : 0 ≤ width δ n := mul_nonneg hδ (pow_nonneg (by norm_num) _)
  linarith

lemma tendsto_width (δ : ℝ) : Tendsto (width δ) atTop (𝓝 0) := by
  change Tendsto (fun n => δ*(1/2 : ℝ)^n) atTop (𝓝 0)
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)).const_mul δ

lemma width_rpow {δ : ℝ} (hδ : 0 ≤ δ) (p : ℝ) (n : ℕ) :
    (width δ n)^p = δ^p*((1/2 : ℝ)^p)^n := by
  rw [width, Real.mul_rpow hδ (pow_nonneg (by norm_num) n)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    mul_comm (n : ℝ) p, Real.rpow_mul (by norm_num), Real.rpow_natCast]

lemma ratio_norm_lt {p : ℝ} (hp : 0 < p) : ‖(1/2 : ℝ)^p‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
  exact Real.rpow_lt_one (by norm_num) (by norm_num) hp

lemma summable_width_rpow {δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 < p) :
    Summable (fun n => (width δ n)^p) := by
  simp_rw [width_rpow hδ]
  exact (summable_geometric_of_norm_lt_one (ratio_norm_lt hp)).mul_left _

lemma tsum_width_rpow {δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 < p) :
    (∑' n, (width δ n)^p) = δ^p / (1-(1/2 : ℝ)^p) := by
  simp_rw [width_rpow hδ]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (ratio_norm_lt hp)]
  rfl

lemma scaled_increment {Cs A t δ M L : ℝ} (hCs : 0 ≤ Cs) (hA : 0 ≤ A)
    (hAt : A ≤ t) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : M ≤ A*δ^(-(1/50 : ℝ))) (hL : L ≤ 648/δ) :
    2*δ^(1/5 : ℝ)*M+14*(t*δ^(1/10 : ℝ))+
      (L+2*(3*L+1))*Cs*δ^(2*(1-(1/100 : ℝ)))*A ≤
      (16+4538*Cs)*t*δ^(1/10 : ℝ) := by
  have ht : 0 ≤ t := hA.trans hAt
  have hc : L+2*(3*L+1) ≤ 4538/δ := by
    have hh : L*δ ≤ 648 := (le_div_iff₀ hδ).mp hL
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  have he1 : δ^(1/5 : ℝ)*δ^(-(1/50 : ℝ)) = δ^(9/50 : ℝ) := by
    rw [← Real.rpow_add hδ]
    norm_num
  have he2 : δ⁻¹*δ^(2*(1-(1/100 : ℝ))) = δ^(49/50 : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hδ]
    norm_num
  have hb1 : δ^(9/50 : ℝ) ≤ δ^(1/10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
  have hb2 : δ^(49/50 : ℝ) ≤ δ^(1/10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
  have hm : 2*δ^(1/5 : ℝ)*M ≤ 2*t*δ^(1/10 : ℝ) := by
    calc
      _ ≤ 2*δ^(1/5 : ℝ)*(A*δ^(-(1/50 : ℝ))) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      _ = 2*A*δ^(9/50 : ℝ) := by rw [← he1]; ring
      _ ≤ 2*t*δ^(1/10 : ℝ) := mul_le_mul (by linarith) hb1
        (Real.rpow_nonneg hδ.le _) (by positivity)
  have hf : (L+2*(3*L+1))*Cs*δ^(2*(1-(1/100 : ℝ)))*A ≤
      4538*Cs*t*δ^(1/10 : ℝ) := by
    calc
      _ ≤ (4538/δ)*Cs*δ^(2*(1-(1/100 : ℝ)))*A := by gcongr
      _ = 4538*Cs*A*δ^(49/50 : ℝ) := by rw [← he2]; ring
      _ ≤ 4538*Cs*t*δ^(1/10 : ℝ) := mul_le_mul (by gcongr) hb2
        (Real.rpow_nonneg hδ.le _) (by positivity)
  nlinarith

/-- A single small width works for both shell geometry and every smaller width. -/
lemma exists_admissible_width : ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1/4 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → δ ≤ (δ^(1/5 : ℝ))^2/1600 := by
  have ht : Tendsto (fun δ : ℝ => δ^(3/5 : ℝ)) (𝓝 0) (𝓝 0) := by
    simpa using (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3/5)).tendsto 0
  have hev := ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1/1600)
  obtain ⟨l,u,hu,hs⟩ := mem_nhds_iff_exists_Ioo_subset.mp hev
  let d := min (u/2) (1/4)
  have hd : 0 < d := lt_min (by linarith [hu.2]) (by norm_num)
  refine ⟨d, hd, min_le_right _ _, fun δ hδ hδd => ?_⟩
  have hdltu : d < u := lt_of_le_of_lt (min_le_left _ _) (by linarith [hu.2])
  have hp : δ^(3/5 : ℝ) < 1/1600 := hs ⟨lt_trans hu.1 hδ, lt_of_le_of_lt hδd hdltu⟩
  have he : δ = δ^(3/5 : ℝ)*(δ^(1/5 : ℝ))^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
    norm_num
  calc
    δ = δ^(3/5 : ℝ)*(δ^(1/5 : ℝ))^2 := he
    _ ≤ (δ^(1/5 : ℝ))^2/1600 :=
      (mul_le_mul_of_nonneg_right hp.le (sq_nonneg _)).trans_eq (by ring)

end DiskScales

end SignedDisk

end

end OAI
