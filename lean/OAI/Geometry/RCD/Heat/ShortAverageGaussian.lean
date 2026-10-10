import OAI.Geometry.RCD.Heat.GaussianScaleAbsorption
import OAI.Geometry.RCD.Heat.AveragedHeatSource

namespace OAI

/-! # Gaussian bounds for an averaged kernel below the averaging scale -/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- A pointwise bound on a finite averaging set is preserved by averaging. -/
theorem kernelAverage_le_uniform {t : ℝ} (ht : 0 < t) (s : Set X)
    (hs : MeasurableSet s) (hfinite : μ s ≠ ∞) (hvol : 0 < μ.real s) (z : X) {B : ℝ}
    (hbound : ∀ y ∈ s, ker t y z ≤ B) : kernelAverage μ ker t s z ≤ B := by
  have hi : IntegrableOn (fun y => ker t y z) s μ := by
    apply (hk.integrable t ht z).integrableOn.congr
    exact Eventually.of_forall fun y => hk.symmetric t ht z y
  have h := integral_mono_ae hi (integrableOn_const hfinite (C := B))
    (by filter_upwards [ae_restrict_mem hs] with y hy; exact hbound y hy)
  have hm := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hvol.le)
  change (μ.real s)⁻¹ * (∫ y in s, ker t y z ∂μ) ≤ B
  apply hm.trans_eq
  simp only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ]
  field_simp [show (μ s).toReal ≠ 0 from ne_of_gt hvol]

include hk in
/-- The short-time averaged kernel has Gaussian decay at the averaging
radius. Its constants depend only on the displayed geometric bounds. -/
theorem exists_short_average_gaussian (n : ℕ) {A V Cg D : ℝ}
    (hA : 0 ≤ A) (hV : 0 < V) (hCg : 0 ≤ Cg) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r t : ℝ) (x q z : X),
      0 < r → 0 < t → t ≤ r ^ 2 → μ (ball q r) ≠ ∞ →
      V * r ^ n ≤ μ.real (ball q r) → dist x q ≤ A * r →
      (∀ y ∈ ball q r, ker t y z ≤
        Cg * (Real.sqrt t)⁻¹ ^ n * Real.exp (-(dist y z) ^ 2 / (D * t))) →
      kernelAverage μ ker t (ball q r) z ≤
        C * r⁻¹ ^ n * Real.exp (-(dist x z) ^ 2 / (8 * D * r ^ 2)) := by
  obtain ⟨C₀, hC₀, habsorb⟩ := exists_gaussian_short_time_bound n
    (show 0 < 4 * D by positivity)
  let L := (2 * (A + 1)) ^ 2 / (8 * D)
  let Cnear := V⁻¹ * Real.exp L
  let C := max Cnear (Cg * C₀)
  have hCnear : 0 < Cnear := mul_pos (inv_pos.mpr hV) (Real.exp_pos _)
  have hC : 0 < C := hCnear.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro r t x q z hr ht htr hfinite hvolume hcenter hgauss
  have hvol : 0 < μ.real (ball q r) := (mul_pos hV (pow_pos hr n)).trans_le hvolume
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hrpow : 0 < r ^ n := pow_pos hr n
  have hD8 : 0 < 8 * D * r ^ 2 := by positivity
  by_cases hnear : dist x z ≤ 2 * (A + 1) * r
  · have hratio : (μ.real (ball q r))⁻¹ ≤ V⁻¹ * r⁻¹ ^ n := by
      have hi := one_div_le_one_div_of_le (mul_pos hV hrpow) hvolume
      simpa only [one_div, mul_inv_rev, inv_pow, mul_comm] using hi
    have hdist : (dist x z) ^ 2 / (8 * D * r ^ 2) ≤ L := by
      have hsq : (dist x z) ^ 2 ≤ (2 * (A + 1) * r) ^ 2 :=
        (sq_le_sq₀ dist_nonneg (by positivity)).mpr hnear
      apply (div_le_iff₀ hD8).mpr
      dsimp only [L]
      have he : ((2 * (A + 1)) ^ 2 / (8 * D)) * (8 * D * r ^ 2) =
          (2 * (A + 1) * r) ^ 2 := by field_simp
      rwa [he]
    have hexp : 1 ≤ Real.exp L * Real.exp (-(dist x z) ^ 2 / (8 * D * r ^ 2)) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      simp only [neg_div]
      linarith
    calc
      _ ≤ (μ.real (ball q r))⁻¹ := (kernelAverage_bounds μ hQ hk ht (ball q r) z).2
      _ ≤ V⁻¹ * r⁻¹ ^ n := hratio
      _ ≤ (V⁻¹ * r⁻¹ ^ n) *
          (Real.exp L * Real.exp (-(dist x z) ^ 2 / (8 * D * r ^ 2))) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp
          (mul_nonneg (inv_pos.mpr hV).le (pow_nonneg (inv_pos.mpr hr).le n))
      _ = Cnear * r⁻¹ ^ n * Real.exp (-(dist x z) ^ 2 / (8 * D * r ^ 2)) := by
        dsimp only [Cnear]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (Real.exp_pos _).le
  · have hfar : r ≤ dist x z := by
      have ha : 2 ≤ 2 * (A + 1) := by linarith
      have hm := mul_le_mul_of_nonneg_right ha hr.le
      linarith
    apply kernelAverage_le_uniform μ hQ hk ht (ball q r) measurableSet_ball hfinite hvol z
    intro y hy
    have hyq : dist q y < r := by simpa only [mem_ball, dist_comm] using hy
    have htri := dist_triangle x q z
    have htri' := dist_triangle q y z
    have hd : dist x z / 2 ≤ dist y z := by linarith
    have hsquare : (dist x z / 2) ^ 2 ≤ (dist y z) ^ 2 :=
      (sq_le_sq₀ (by positivity) dist_nonneg).mpr hd
    have hfrac := div_le_div_of_nonneg_right hsquare (mul_pos hD ht).le
    have he : (dist x z / 2) ^ 2 / (D * t) = (dist x z) ^ 2 / ((4 * D) * t) := by
      field_simp; ring
    rw [he] at hfrac
    have hkbound := (hgauss y hy).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by
        simpa only [neg_div] using neg_le_neg hfrac))
      (mul_nonneg hCg (pow_nonneg (inv_pos.mpr hs).le n)))
    have htime := mul_le_mul_of_nonneg_left (habsorb r t (dist x z) hr ht htr hfar) hCg
    have hmax := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right Cnear (Cg * C₀)) (pow_nonneg (inv_pos.mpr hr).le n))
      (Real.exp_pos (-(dist x z) ^ 2 / (8 * D * r ^ 2))).le
    have htime' : Cg * (Real.sqrt t)⁻¹ ^ n *
        Real.exp (-(dist x z) ^ 2 / ((4 * D) * t)) ≤
          (Cg * C₀) * r⁻¹ ^ n * Real.exp (-(dist x z) ^ 2 / (8 * D * r ^ 2)) := by
      norm_num [← mul_assoc] at htime ⊢
      exact htime
    exact hkbound.trans (by simpa only [neg_div] using htime'.trans hmax)

end RegularPointCoordinates

end

end OAI
