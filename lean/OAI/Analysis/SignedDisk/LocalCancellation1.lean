import OAI.Analysis.SignedDisk.DiskKernels1

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal

noncomputable section

namespace SignedDisk

namespace LocalCancellation

lemma integrable_lip_mul {b F : ℂ → ℂ} (hb : Integrable b)
    {L : ℝ≥0} (hF : LipschitzWith L F) (z : ℂ) {s : ℝ}
    (hsupp : ∀ᵐ y, b y ≠ 0 → ‖y-z‖ ≤ s) : Integrable (fun y => F y * b y) := by
  have hbound : ∀ᵐ y, ‖(F y - F z) * b y‖ ≤ ((L : ℝ) * s) * ‖b y‖ := by
    filter_upwards [hsupp] with y hy
    by_cases hby : b y = 0
    · simp [hby]
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        ((hF.norm_sub_le y z).trans (mul_le_mul_of_nonneg_left (hy hby) L.coe_nonneg))
        (norm_nonneg _)
  have hdiff : Integrable (fun y => (F y - F z) * b y) :=
    (hb.norm.smul ((L : ℝ) * s)).mono'
      ((hF.continuous.sub continuous_const).aestronglyMeasurable.mul hb.aestronglyMeasurable) hbound
  have h := hdiff.add (hb.const_mul (F z))
  change Integrable (fun y => (F y-F z)*b y + F z * b y) at h
  simpa only [← add_mul, sub_add_cancel] using h

/-- Cancellation against the actual integrable complex error density. -/
lemma lip_cancellation {b F : ℂ → ℂ} (hb : Integrable b) (hzero : ∫ y, b y = 0)
    {L : ℝ≥0} (hF : LipschitzWith L F) (z : ℂ) {s : ℝ}
    (hsupp : ∀ᵐ y, b y ≠ 0 → ‖y-z‖ ≤ s) :
    ‖∫ y, F y * b y‖ ≤ (L : ℝ) * s * ∫ y, ‖b y‖ := by
  have hprod := integrable_lip_mul hb hF z hsupp
  have he : (∫ y, (F y - F z) * b y) = ∫ y, F y * b y := by
    simp_rw [sub_mul]
    rw [integral_sub hprod (hb.const_mul (F z)), integral_const_mul, hzero, mul_zero, sub_zero]
  rw [← he]
  calc
    ‖∫ y, (F y-F z) * b y‖ ≤ ∫ y, ((L : ℝ) * s) * ‖b y‖ := by
      apply norm_integral_le_of_norm_le (hb.norm.smul ((L : ℝ) * s))
      filter_upwards [hsupp] with y hy
      by_cases hby : b y = 0
      · simp [hby]
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          ((hF.norm_sub_le y z).trans (mul_le_mul_of_nonneg_left (hy hby) L.coe_nonneg))
          (norm_nonneg _)
    _ = (L : ℝ) * s * ∫ y, ‖b y‖ := integral_const_mul _ _

lemma bounded_pairing {b F : ℂ → ℂ} (hb : Integrable b) {M : ℝ}
    (hF : ∀ y, ‖F y‖ ≤ M) : ‖∫ y, F y * b y‖ ≤ M * ∫ y, ‖b y‖ := by
  calc
    ‖∫ y, F y * b y‖ ≤ ∫ y, M * ‖b y‖ := by
      apply norm_integral_le_of_norm_le (hb.norm.const_mul M)
      exact Eventually.of_forall (fun y => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hF y) (norm_nonneg _))
    _ = M * ∫ y, ‖b y‖ := integral_const_mul _ _

lemma min_one_le_rpow {a α : ℝ} (ha : 0 ≤ a) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    min 1 a ≤ a ^ α := by
  by_cases ha1 : a ≤ 1
  · rw [min_eq_right ha1]
    by_cases hz : a = 0
    · rw [hz]
      exact Real.rpow_nonneg (by norm_num) _
    · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne ha (Ne.symm hz)) ha1 hα1
  · rw [min_eq_left (le_of_not_ge ha1)]
    exact Real.one_le_rpow (le_of_not_ge ha1) hα0

structure ErrorPiece (Cs : ℝ) where
  density : ℂ → ℂ
  integrable : Integrable density
  size : ℝ
  size_pos : 0 < size
  size_le_one : size ≤ 1
  center : ℂ
  zero_mass : size < 1 → ∫ y, density y = 0
  support : size < 1 → ∀ᵐ y, density y ≠ 0 → ‖y-center‖ ≤ Cs * size

def ErrorPiece.mass {Cs : ℝ} (b : ErrorPiece Cs) : ℝ := ∫ y, ‖b.density y‖

lemma ErrorPiece.mass_nonneg {Cs : ℝ} (b : ErrorPiece Cs) : 0 ≤ b.mass :=
  integral_nonneg (fun _ => norm_nonneg _)

/-- The single-piece interpolation discount, with no smoothness assumed on the density. -/
lemma piece_discount {Cs α δ C : ℝ} (b : ErrorPiece Cs)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : 1 ≤ C) {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F)
    (hFb : ∀ y, ‖F y‖ ≤ 1) (hLC : (L : ℝ) * Cs ≤ C / δ) :
    ‖∫ y, F y * b.density y‖ ≤ C * (b.size / δ) ^ α * b.mass := by
  have hr : ‖∫ y, F y * b.density y‖ ≤ b.mass := by
    convert! bounded_pairing b.integrable hFb using 1
    simp only [one_mul, ErrorPiece.mass]
  have hCm : 0 ≤ C * b.mass := mul_nonneg (by linarith) b.mass_nonneg
  have hm : ‖∫ y, F y * b.density y‖ ≤ C * min 1 (b.size/δ) * b.mass := by
    by_cases hs : b.size < 1
    · have hl := lip_cancellation b.integrable (b.zero_mass hs) hF b.center (b.support hs)
      have hl' : ‖∫ y, F y * b.density y‖ ≤ C * (b.size/δ) * b.mass := by
        have hh := mul_le_mul_of_nonneg_right hLC (mul_nonneg b.size_pos.le b.mass_nonneg)
        calc
          _ ≤ (L : ℝ) * (Cs * b.size) * b.mass := hl
          _ ≤ C * (b.size/δ) * b.mass := by convert! hh using 1 <;> ring
      have hr' : ‖∫ y, F y * b.density y‖ ≤ C * 1 * b.mass := by nlinarith [b.mass_nonneg]
      by_cases hh : 1 ≤ b.size/δ
      · simpa only [min_eq_left hh] using hr'
      · simpa only [min_eq_right (le_of_not_ge hh)] using hl'
    · have hs1 : b.size = 1 := le_antisymm b.size_le_one (le_of_not_gt hs)
      have hh : 1 ≤ b.size / δ := by rw [hs1]; exact (one_le_div hδ).mpr hδ1
      rw [min_eq_left hh]
      nlinarith [b.mass_nonneg]
  calc
    _ ≤ C * min 1 (b.size/δ) * b.mass := hm
    _ ≤ C * (b.size/δ)^α * b.mass := by
      nlinarith [mul_le_mul_of_nonneg_left
        (min_one_le_rpow (div_nonneg b.size_pos.le hδ.le) hα0 hα1) hCm]

/-- Multiplication by the position keeps a bounded-support Lipschitz test Lipschitz. -/
lemma position_lipschitz {F : ℂ → ℂ} {L M R : ℝ≥0} (hF : LipschitzWith L F)
    (hM : ∀ y, ‖F y‖ ≤ M) (x : ℂ)
    (hR : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ R) :
    LipschitzWith (R*L+M) (fun y => star (y-x) * F y) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [dist_eq_norm, dist_eq_norm]
  change ‖star (y-x)*F y - star (z-x)*F z‖ ≤ ((R : ℝ)*(L : ℝ)+(M : ℝ))*‖y-z‖
  by_cases hz : F z = 0
  · rw [hz, mul_zero, sub_zero]
    by_cases hy : F y = 0
    · simp only [hy, mul_zero, norm_zero]
      positivity
    · have hFy : ‖F y‖ ≤ (L : ℝ)*‖y-z‖ := by simpa only [hz, sub_zero] using hF.norm_sub_le y z
      rw [norm_mul, norm_star]
      have hh := mul_le_mul (hR y hy) hFy (norm_nonneg _) R.coe_nonneg
      nlinarith [mul_nonneg M.coe_nonneg (norm_nonneg (y-z))]
  · have he : star (y-x)*F y-star (z-x)*F z =
        star (z-x)*(F y-F z)+star (y-z)*F y := by
      simp only [star_sub]
      ring
    rw [he]
    calc
      _ ≤ ‖star (z-x)*(F y-F z)‖+‖star (y-z)*F y‖ := norm_add_le _ _
      _ = ‖z-x‖*‖F y-F z‖+‖y-z‖*‖F y‖ := by rw [norm_mul, norm_mul, norm_star, norm_star]
      _ ≤ (R : ℝ)*((L : ℝ)*‖y-z‖)+‖y-z‖*(M : ℝ) :=
        add_le_add (mul_le_mul (hR z hz) (hF.norm_sub_le y z) (norm_nonneg _) R.coe_nonneg)
          (mul_le_mul_of_nonneg_left (hM y) (norm_nonneg _))
      _ = _ := by ring

def correction (x z y : ℂ) : ℂ := 1 - star (y-x) / star (z-x)

lemma correction_eq {x z y : ℂ} (hz : z ≠ x) :
    correction x z y = star (z-y) / star (z-x) := by
  have hzx : star (z-x) ≠ 0 := star_ne_zero.mpr (sub_ne_zero.mpr hz)
  have he : star (z-x)-star (y-x) = star (z-y) := by simp only [star_sub]; ring
  calc
    correction x z y = (star (z-x)-star (y-x))/star (z-x) := by
      rw [sub_div, div_self hzx]
      rfl
    _ = star (z-y)/star (z-x) := by rw [he]

lemma norm_correction {x z y : ℂ} (hz : z ≠ x) :
    ‖correction x z y‖ = ‖y-z‖ / ‖z-x‖ := by
  rw [correction_eq hz, norm_div, norm_star, norm_star, norm_sub_rev z y]

lemma correction_cap_bound {x z y : ℂ} {ρ : ℝ}
    (hz : (1 : ℝ)/2 ≤ ‖z-x‖) (hy : ‖y-z‖ ≤ ρ) :
    ‖correction x z y‖ ≤ 2*ρ := by
  have hzx : 0 < ‖z-x‖ := by linarith
  have hne : z ≠ x := sub_ne_zero.mp (norm_pos_iff.mp hzx)
  rw [norm_correction hne]
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hy
  apply (div_le_iff₀ hzx).mpr
  nlinarith

lemma correction_bounded {x z y : ℂ} (hz : (1 : ℝ)/2 ≤ ‖z-x‖)
    (hy : ‖y-x‖ ≤ 3) : ‖correction x z y‖ ≤ 7 := by
  have hzx : 0 < ‖z-x‖ := by linarith
  calc
    ‖correction x z y‖ ≤ 1+‖y-x‖/‖z-x‖ := by
      simpa only [correction, norm_one, norm_div, norm_star] using norm_sub_le (1 : ℂ) (star (y-x)/star (z-x))
    _ ≤ 7 := by
      have : ‖y-x‖/‖z-x‖ ≤ 6 := (div_le_iff₀ hzx).mpr (by linarith)
      linarith

/-- Global Lipschitz control of the corrected increment test. -/
lemma corrected_lipschitz {F : ℂ → ℂ} {L M R H : ℝ≥0} (hF : LipschitzWith L F)
    (hM : ∀ y, ‖F y‖ ≤ M) (x z : ℂ)
    (hR : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ R) (hH : ‖(star (z-x))⁻¹‖ ≤ H) :
    LipschitzWith (L+H*(R*L+M)) (fun y => correction x z y * F y) := by
  have hp := position_lipschitz hF hM x hR
  apply LipschitzWith.of_dist_le_mul
  intro y w
  have he : correction x z y*F y-correction x z w*F w =
      (F y-F w)-(star (z-x))⁻¹*(star (y-x)*F y-star (w-x)*F w) := by
    simp only [correction, div_eq_mul_inv]
    ring
  rw [dist_eq_norm, he, dist_eq_norm]
  calc
    _ ≤ ‖F y-F w‖+‖(star (z-x))⁻¹*(star (y-x)*F y-star (w-x)*F w)‖ := norm_sub_le _ _
    _ ≤ (L : ℝ)*‖y-w‖+(H : ℝ)*(((R : ℝ)*(L : ℝ)+(M : ℝ))*‖y-w‖) := by
      apply add_le_add (hF.norm_sub_le y w)
      rw [norm_mul]
      exact mul_le_mul hH (hp.norm_sub_le y w) (norm_nonneg _) H.coe_nonneg
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul]; ring

variable {ι : Type*} [Fintype ι]

def errorPrice {Cs : ℝ} (b : ι → ErrorPiece Cs) (α : ℝ) : ℝ :=
  ∑ d, (b d).size ^ α * (b d).mass

lemma errorPrice_nonneg {Cs : ℝ} (b : ι → ErrorPiece Cs) (α : ℝ) :
    0 ≤ errorPrice b α := Finset.sum_nonneg (fun d _ =>
  mul_nonneg (Real.rpow_nonneg (b d).size_pos.le _) (b d).mass_nonneg)

lemma square_rpow {δ : ℝ} (hδ : 0 ≤ δ) (α : ℝ) :
    (δ^2)^α = δ^(2*α) := by
  rw [Real.rpow_mul hδ, Real.rpow_two]

lemma coarse_mass_mul_le {Cs α δ : ℝ} (b : ι → ErrorPiece Cs) (hα : 0 ≤ α)
    (hδ : 0 ≤ δ) :
    δ^(2*α) * (∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), (b d).mass) ≤
      errorPrice b α := by
  classical
  rw [Finset.mul_sum]
  have hp : δ^(2*α) = (δ^2)^α := (square_rpow hδ α).symm
  calc
    _ ≤ ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), (b d).size^α*(b d).mass := by
      apply Finset.sum_le_sum
      intro d hd
      rw [hp]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (sq_nonneg δ) (Finset.mem_filter.mp hd).2 hα) (b d).mass_nonneg
    _ ≤ errorPrice b α := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun d _ _ => mul_nonneg (Real.rpow_nonneg (b d).size_pos.le _) (b d).mass_nonneg)

lemma fine_size_sum_le {Cs α δ : ℝ} (b : ι → ErrorPiece Cs) (hα : α ≤ 1)
    (hδ : 0 ≤ δ) :
    (∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2), (b d).size*(b d).mass) ≤
      δ^(2*(1-α))*errorPrice b α := by
  classical
  calc
    _ ≤ ∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2),
        δ^(2*(1-α))*((b d).size^α*(b d).mass) := by
      apply Finset.sum_le_sum
      intro d hd
      have hs : (b d).size < δ^2 := (Finset.mem_filter.mp hd).2
      have he : (b d).size = (b d).size^α*(b d).size^(1-α) := by
        rw [← Real.rpow_add (b d).size_pos]
        simp
      have hh := Real.rpow_le_rpow (b d).size_pos.le hs.le (sub_nonneg.mpr hα)
      rw [square_rpow hδ] at hh
      calc
        _ = ((b d).size^α*(b d).size^(1-α))*(b d).mass := congrArg (fun v => v*(b d).mass) he
        _ = (b d).size^(1-α)*((b d).size^α*(b d).mass) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hh
          (mul_nonneg (Real.rpow_nonneg (b d).size_pos.le _) (b d).mass_nonneg)
    _ = δ^(2*(1-α)) * (∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2),
        (b d).size^α*(b d).mass) := (Finset.mul_sum ..).symm
    _ ≤ δ^(2*(1-α))*errorPrice b α := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun d _ _ => mul_nonneg (Real.rpow_nonneg (b d).size_pos.le _) (b d).mass_nonneg))
      (Real.rpow_nonneg hδ _)

lemma total_pairing_discount {Cs α δ C : ℝ} (b : ι → ErrorPiece Cs)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : 1 ≤ C) {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F)
    (hFb : ∀ y, ‖F y‖ ≤ 1) (hLC : (L : ℝ)*Cs ≤ C/δ) :
    ‖∑ d, ∫ y, F y*(b d).density y‖ ≤ C/δ^α*errorPrice b α := by
  calc
    _ ≤ ∑ d, ‖∫ y, F y*(b d).density y‖ := norm_sum_le _ _
    _ ≤ ∑ d, C*((b d).size/δ)^α*(b d).mass := Finset.sum_le_sum
      (fun d _ => piece_discount (b d) hα0 hα1 hδ hδ1 hC hF hFb hLC)
    _ = C/δ^α*errorPrice b α := by
      rw [errorPrice, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [Real.div_rpow (b d).size_pos.le hδ.le]
      ring

/-- All fine errors together retain the stronger, summable power of the width. -/
lemma fine_pairing_bound {Cs α δ : ℝ} (b : ι → ErrorPiece Cs) (hCs : 0 ≤ Cs)
    (hα : α ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) :
    ‖∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2), ∫ y, F y*(b d).density y‖ ≤
      (L : ℝ)*Cs*δ^(2*(1-α))*errorPrice b α := by
  classical
  calc
    _ ≤ ∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2), ‖∫ y, F y*(b d).density y‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2),
        (L : ℝ)*Cs*((b d).size*(b d).mass) := by
      apply Finset.sum_le_sum
      intro d hd
      have hs : (b d).size < 1 := lt_of_lt_of_le (Finset.mem_filter.mp hd).2 (by nlinarith)
      have hh := lip_cancellation (b d).integrable ((b d).zero_mass hs) hF (b d).center ((b d).support hs)
      convert! hh using 1
      dsimp only [ErrorPiece.mass]
      ring
    _ = (L : ℝ)*Cs*(∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2),
        (b d).size*(b d).mass) := (Finset.mul_sum ..).symm
    _ ≤ (L : ℝ)*Cs*(δ^(2*(1-α))*errorPrice b α) :=
      mul_le_mul_of_nonneg_left (fine_size_sum_le b hα hδ) (mul_nonneg L.coe_nonneg hCs)
    _ = _ := by ring

end LocalCancellation

open MeasureTheory Set Filter
open scoped Topology NNReal Real

namespace LocalCancellation

/-- Norm total-variation measure of an actual complex density. -/
def densityMeasure (b : ℂ → ℂ) : Measure ℂ := volume.withDensity (fun y => ENNReal.ofReal ‖b y‖)

lemma densityMeasure_apply {b : ℂ → ℂ} (hb : Integrable b) {D : Set ℂ}
    (hD : MeasurableSet D) : densityMeasure b D = ENNReal.ofReal (∫ y in D, ‖b y‖) := by
  rw [densityMeasure, withDensity_apply _ hD]
  exact (ofReal_integral_eq_lintegral_ofReal hb.integrableOn.norm
    (Eventually.of_forall (fun _ => norm_nonneg _))).symm

lemma densityMeasure_univ {b : ℂ → ℂ} (hb : Integrable b) :
    densityMeasure b univ = ENNReal.ofReal (∫ y, ‖b y‖) := by
  rw [densityMeasure_apply hb MeasurableSet.univ, Measure.restrict_univ]

lemma densityMeasure_finite {b : ℂ → ℂ} (hb : Integrable b) : IsFiniteMeasure (densityMeasure b) := by
  constructor
  rw [densityMeasure_univ hb]
  exact ENNReal.ofReal_lt_top

/-- A cap decomposition bound, with all integrals over genuine densities. -/
lemma pairing_majorant {b F : ℂ → ℂ} (hb : Integrable b) {A : Set ℂ}
    (hA : MeasurableSet A) (c d : ℝ)
    (hF : ∀ y, ‖F y‖ ≤ c + d*A.indicator (fun _ => (1 : ℝ)) y) :
    ‖∫ y, F y*b y‖ ≤ c*(∫ y, ‖b y‖)+d*(∫ y in A, ‖b y‖) := by
  have hi : Integrable (fun y => c*‖b y‖+d*A.indicator (fun y => ‖b y‖) y) :=
    (hb.norm.const_mul c).add ((hb.norm.indicator hA).const_mul d)
  calc
    _ ≤ ∫ y, c*‖b y‖+d*A.indicator (fun y => ‖b y‖) y := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards with y
      rw [norm_mul]
      have hh := mul_le_mul_of_nonneg_right (hF y) (norm_nonneg (b y))
      convert! hh using 1
      by_cases hy : y ∈ A
      · simp only [Set.indicator_of_mem hy, mul_one]
        ring
      · simp only [Set.indicator_of_notMem hy, mul_zero, add_zero]
    _ = _ := by
      rw [integral_add (hb.norm.const_mul c) ((hb.norm.indicator hA).const_mul d),
        integral_const_mul, integral_const_mul, integral_indicator hA]

/-- Cancellation of an exact complex moment allows an off-center correction. -/
lemma moment_correction {b F : ℂ → ℂ} (x z : ℂ)
    (hF : Integrable (fun y => F y*b y))
    (hM : Integrable (fun y => star (y-x)*F y*b y))
    (hzero : ∫ y, star (y-x)*F y*b y = 0) :
    (∫ y, F y*b y) = ∫ y, (1-star (y-x)/star (z-x))*F y*b y := by
  have he : (fun y => (1-star (y-x)/star (z-x))*F y*b y) =
      fun y => F y*b y-(star (z-x))⁻¹*(star (y-x)*F y*b y) := by
    funext y
    simp only [div_eq_mul_inv]
    ring
  rw [he, integral_sub hF (hM.const_mul _), integral_const_mul, hzero, mul_zero, sub_zero]

lemma corrected_pairing_cap {b F : ℂ → ℂ} (hb : Integrable b) {D : Set ℂ}
    (hD : MeasurableSet D) (hFb : ∀ y, ‖F y‖ ≤ 1)
    (hFD : ∀ y, F y ≠ 0 → y ∈ D) (x z : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hz : (1 : ℝ)/2 ≤ ‖z-x‖) (hD3 : ∀ y ∈ D, ‖y-x‖ ≤ 3) :
    ‖∫ y, correction x z y*F y*b y‖ ≤
      2*ρ*(∫ y, ‖b y‖)+7*(∫ y in D \ Metric.ball z ρ, ‖b y‖) := by
  apply pairing_majorant hb (hD.diff measurableSet_ball) (2*ρ) 7
  intro y
  by_cases hFy : F y = 0
  · simp only [hFy, mul_zero, norm_zero]
    exact add_nonneg (mul_nonneg (by norm_num) hρ)
      (mul_nonneg (by norm_num) (Set.indicator_nonneg (fun _ _ => zero_le_one) y))
  · have hyD := hFD y hFy
    by_cases hyB : y ∈ Metric.ball z ρ
    · have hc := correction_cap_bound hz (show ‖y-z‖ ≤ ρ from by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hyB).le)
      rw [Set.indicator_of_notMem (show y ∉ D \ Metric.ball z ρ from fun h => h.2 hyB), mul_zero, add_zero]
      rw [norm_mul]
      simpa only [mul_one] using mul_le_mul hc (hFb y) (norm_nonneg _) (mul_nonneg (by norm_num) hρ)
    · rw [Set.indicator_of_mem (show y ∈ D \ Metric.ball z ρ from ⟨hyD,hyB⟩), mul_one]
      have hc := correction_bounded hz (hD3 y hyD)
      rw [norm_mul]
      have hh := mul_le_mul hc (hFb y) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 7)
      nlinarith

lemma supported_pairing {b F : ℂ → ℂ} (hb : Integrable b) {D : Set ℂ}
    (hD : MeasurableSet D) (hFb : ∀ y, ‖F y‖ ≤ 1)
    (hFD : ∀ y, F y ≠ 0 → y ∈ D) :
    ‖∫ y, F y*b y‖ ≤ ∫ y in D, ‖b y‖ := by
  have hh := pairing_majorant hb hD 0 1 (show ∀ y, ‖F y‖ ≤ 0+1*D.indicator (fun _ => (1 : ℝ)) y from by
    intro y
    by_cases hy : y ∈ D
    · simpa only [Set.indicator_of_mem hy, mul_one, zero_add] using hFb y
    · have hf : F y = 0 := by by_contra h; exact hy (hFD y h)
      simp only [hf, norm_zero, Set.indicator_of_notMem hy, mul_zero, zero_add, le_refl])
  simpa only [zero_mul, one_mul, zero_add] using hh

variable {ι : Type*} [Fintype ι]

def coarseMeasure {Cs : ℝ} (b : ι → ErrorPiece Cs) (δ : ℝ) : Measure ℂ :=
  ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), densityMeasure (b d).density

def coarseMass {Cs : ℝ} (b : ι → ErrorPiece Cs) (δ : ℝ) (D : Set ℂ) : ℝ :=
  ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), ∫ y in D, ‖(b d).density y‖

lemma coarseMass_nonneg {Cs : ℝ} (b : ι → ErrorPiece Cs) (δ : ℝ) (D : Set ℂ) :
    0 ≤ coarseMass b δ D := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => norm_nonneg _))

lemma coarseMeasure_apply {Cs : ℝ} (b : ι → ErrorPiece Cs) (δ : ℝ) {D : Set ℂ}
    (hD : MeasurableSet D) : coarseMeasure b δ D = ENNReal.ofReal (coarseMass b δ D) := by
  classical
  simp only [coarseMeasure, Measure.finsetSum_apply, densityMeasure_apply (b _).integrable hD,
    coarseMass]
  rw [ENNReal.ofReal_sum_of_nonneg (fun d _ => integral_nonneg (fun _ => norm_nonneg _))]

instance coarseMeasure_finite {Cs : ℝ} (b : ι → ErrorPiece Cs) (δ : ℝ) :
    IsFiniteMeasure (coarseMeasure b δ) := by
  constructor
  rw [coarseMeasure_apply b δ MeasurableSet.univ]
  exact ENNReal.ofReal_lt_top

lemma coarseMass_univ {Cs : ℝ} (b : ι → ErrorPiece Cs) (δ : ℝ) :
    coarseMass b δ univ = ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), (b d).mass := by
  simp only [coarseMass, ErrorPiece.mass, Measure.restrict_univ]

lemma coarseMass_bound {Cs α δ : ℝ} (b : ι → ErrorPiece Cs) (hα : 0 ≤ α)
    (hδ : 0 < δ) : coarseMass b δ univ ≤ errorPrice b α / δ^(2*α) := by
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hδ _), mul_comm, coarseMass_univ]
  exact coarse_mass_mul_le b hα hδ.le

/-- The uncorrected increment costs only shell mass plus the fine-error discount. -/
lemma increment_bound {Cs α δ : ℝ} (b : ι → ErrorPiece Cs) (hCs : 0 ≤ Cs)
    (hα : α ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) {D : Set ℂ} (hD : MeasurableSet D)
    (hFb : ∀ y, ‖F y‖ ≤ 1) (hFD : ∀ y, F y ≠ 0 → y ∈ D) :
    ‖∑ d, ∫ y, F y*(b d).density y‖ ≤
      coarseMass b δ D+(L : ℝ)*Cs*δ^(2*(1-α))*errorPrice b α := by
  classical
  have he : (∑ d, ∫ y, F y*(b d).density y) =
      (∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), ∫ y, F y*(b d).density y)+
      (∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2), ∫ y, F y*(b d).density y) := by
    simpa only [not_le] using (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun d => δ^2 ≤ (b d).size) (fun d => ∫ y, F y*(b d).density y)).symm
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum (fun d _ => supported_pairing (b d).integrable hD hFb hFD)
  · exact fine_pairing_bound b hCs hα hδ hδ1 hF

end LocalCancellation

end SignedDisk

end

end OAI
