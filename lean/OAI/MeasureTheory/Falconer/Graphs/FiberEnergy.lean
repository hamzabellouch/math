import OAI.MeasureTheory.Falconer.Fourier.FourierEnergy
import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem density_energy_holder (μ : Measure V) [SFinite μ]
    (h : V → ℝ≥0∞) (hh : Measurable h) {p q u : ℝ} (hpq : p.HolderConjugate q)
    (hnorm : (∫⁻ x, (h x)^q ∂μ) = 1) :
    rieszEnergyOn (μ.withDensity h) u ≤ (rieszEnergyOn μ (u*p))^(1/p) := by
  let K : V × V → ℝ≥0∞ := fun z => (edist z.1 z.2)^(-u)
  let H : V × V → ℝ≥0∞ := fun z => h z.1*h z.2
  have hK : Measurable K := by dsimp [K]; fun_prop
  have hH : Measurable H := by dsimp [H]; fun_prop
  have he : rieszEnergyOn (μ.withDensity h) u = ∫⁻ z : V × V, (K*H) z ∂μ.prod μ := by
    rw [rieszEnergyOn, prod_withDensity hh hh,
      lintegral_withDensity_eq_lintegral_mul _ hH hK]
    apply lintegral_congr
    intro z
    exact mul_comm _ _
  have hp : (∫⁻ z : V × V, (K z)^p ∂μ.prod μ) = rieszEnergyOn μ (u*p) := by
    apply lintegral_congr
    intro z
    dsimp [K]
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  have hq : (∫⁻ z : V × V, (H z)^q ∂μ.prod μ) = 1 := by
    simp_rw [H, ENNReal.mul_rpow_of_nonneg _ _ hpq.symm.nonneg]
    rw [lintegral_prod_mul (f := fun x => h x^q) (g := fun x => h x^q)
      (by fun_prop) (by fun_prop),hnorm,mul_one]
  have hb := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.prod μ) hpq
    hK.aemeasurable hH.aemeasurable
  simpa only [← he,hp,hq,ENNReal.one_rpow,mul_one] using hb

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
theorem finiteMeasure_normalized_density (μ : Measure V) [IsFiniteMeasure μ]
    (h : V → ℝ≥0∞) (hh : Measurable h) {p q : ℝ} (hpq : p.HolderConjugate q)
    (hnorm : (∫⁻ x, (h x)^q ∂μ) = 1) : IsFiniteMeasure (μ.withDensity h) := by
  have hb := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    (f := fun _ => 1) (g := h) measurable_const.aemeasurable hh.aemeasurable
  simp only [Pi.mul_apply,one_mul,ENNReal.one_rpow,lintegral_const,hnorm,mul_one] at hb
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  exact hb.trans_lt (ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hpq.nonneg) (measure_ne_top _ _))

theorem bounded_riesz_kernel {d D u t : ℝ} (hd : 0 ≤ d) (hD : 0 < D)
    (hdD : d ≤ D) (hu : 0 < u) (hut : u < t) :
    (ENNReal.ofReal d)^(-u) ≤ ENNReal.ofReal (D^(t-u)) * (ENNReal.ofReal d)^(-t) := by
  rcases eq_or_lt_of_le hd with hz | hp
  · subst d
    rw [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by linarith),
      ENNReal.zero_rpow_of_neg (by linarith), ENNReal.mul_top
        (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hD _)).ne']
  · rw [ENNReal.ofReal_rpow_of_pos hp, ENNReal.ofReal_rpow_of_pos hp,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _)]
    apply ENNReal.ofReal_le_ofReal
    calc
      d^(-u) = d^(t-u)*d^(-t) := by rw [← Real.rpow_add hp]; congr 1; ring
      _ ≤ D^(t-u)*d^(-t) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hp.le hdD (sub_pos.mpr hut).le) (Real.rpow_nonneg hp.le _)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
theorem bounded_riesz_energy (μ : Measure V) [SFinite μ] {D u t : ℝ}
    (hD : 0 < D) (hu : 0 < u) (hut : u < t)
    (hdiam : ∀ᵐ z : V × V ∂μ.prod μ, dist z.1 z.2 ≤ D) :
    rieszEnergyOn μ u ≤ ENNReal.ofReal (D^(t-u)) * rieszEnergyOn μ t := by
  rw [rieszEnergyOn,rieszEnergyOn,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hdiam] with z hz
  rw [edist_dist]
  exact bounded_riesz_kernel dist_nonneg hD hz hu hut

theorem density_energy_of_diameter (μ : Measure V) [SFinite μ]
    (h : V → ℝ≥0∞) (hh : Measurable h) {D p q u t : ℝ}
    (hpq : p.HolderConjugate q) (hu : 0 < u) (hD : 0 < D) (hupt : u*p < t)
    (hnorm : (∫⁻ x, (h x)^q ∂μ) = 1)
    (hdiam : ∀ᵐ z : V × V ∂μ.prod μ, dist z.1 z.2 ≤ D) :
    rieszEnergyOn (μ.withDensity h) u ≤
      (ENNReal.ofReal (D^(t-u*p)) * rieszEnergyOn μ t)^(1/p) := by
  exact (density_energy_holder μ h hh hpq hnorm).trans
    (ENNReal.rpow_le_rpow (bounded_riesz_energy μ hD (mul_pos hu hpq.pos) hupt hdiam)
      (one_div_nonneg.mpr hpq.nonneg))

end PlanarFalconer

end OAI
