import Mathlib
import OAI.Geometry.PrescribedPotential.AnalyticSupport
import OAI.Geometry.PrescribedRicci.KahlerChartGradient
import OAI.Geometry.PrescribedRicci.KahlerChartLp

namespace OAI

/-! Kahler Sobolev Local. -/

section

 
noncomputable section
open Matrix Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped ContDiff Classical NNReal ENNReal
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ}

lemma coordinates_finrank : Module.finrank ℝ (Coordinates d) = 2*d := by
  simp [Coordinates, Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]

lemma critical_exponent (hd : 2 ≤ d) :
    ∃ q : ℝ≥0, 2 < q ∧ (q:ℝ)⁻¹ = (2:ℝ)⁻¹ - ((2*d:ℕ):ℝ)⁻¹ := by
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hp : 0 < (d:ℝ)-1 := by linarith
  let q : ℝ≥0 := ⟨2*(d:ℝ)/((d:ℝ)-1), (div_pos (by positivity) hp).le⟩
  refine ⟨q, ?_, ?_⟩
  · change (2:ℝ) < 2*(d:ℝ)/((d:ℝ)-1)
    apply (lt_div_iff₀ hp).2
    linarith
  · change (2*(d:ℝ)/((d:ℝ)-1))⁻¹ = _
    push_cast
    field_simp

lemma lpNorm_two_sq {E : Type*} [NormedAddCommGroup E]
    {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} {f : Y → E}
    (hf : AEStronglyMeasurable f μ) :
    (lpNorm f 2 μ) ^ 2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [show (2:ℝ≥0∞) = ((2:ℝ≥0):ℝ≥0∞) by norm_num,
    lpNorm_nnreal_eq_integral_norm_rpow (by norm_num : (2:ℝ≥0) ≠ 0) hf]
  simp only [NNReal.coe_ofNat, Real.rpow_two]
  simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (x := ∫ x, ‖f x‖^2 ∂μ) (n := 2)
    (MeasureTheory.integral_nonneg (fun x => sq_nonneg ‖f x‖)) (by norm_num)

lemma euclidean_sobolev_sq {q : ℝ≥0} (hd : 0 < d)
    (he : (q:ℝ)⁻¹ = (2:ℝ)⁻¹ - ((2*d:ℕ):ℝ)⁻¹)
    {u : Coordinates d → ℝ} (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    (lpNorm u q volume)^2 ≤
      ((eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Coordinates d)) 2 : ℝ≥0):ℝ)^2 *
      ∫ z, ‖fderiv ℝ u z‖^2 := by
  have hn : 0 < Module.finrank ℝ (Coordinates d) := by rw [coordinates_finrank]; omega
  have he' : (q:ℝ)⁻¹ = (((2:ℝ≥0):ℝ))⁻¹ - (Module.finrank ℝ (Coordinates d) : ℝ)⁻¹ := by
    simpa only [coordinates_finrank, NNReal.coe_ofNat] using he
  have hD := hu.continuous_fderiv (by simp)
  have hm : MemLp (fderiv ℝ u) 2 volume := hD.memLp_of_hasCompactSupport (huc.fderiv ℝ)
  have hh := eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure (Coordinates d))
    (hu.of_le (by simp)) huc (by norm_num : (1:ℝ≥0) ≤ 2) hn he'
  have hhR := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hm.eLpNorm_ne_top) hh
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal,
    toReal_eLpNorm, toReal_eLpNorm] at hhR
  have hsq := (sq_le_sq₀ lpNorm_nonneg (mul_nonneg (NNReal.coe_nonneg _) lpNorm_nonneg)).mpr hhR
  rw [mul_pow, lpNorm_two_sq hm.aestronglyMeasurable] at hsq
  exact hsq

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {A : ComplexAtlas d X}

lemma chart_sobolev (g : KaehlerMetric A) (i : Fin A.count)
    {K : Set X} (hK : IsCompact K) (hs : K ⊆ (A.chart i).source)
    {q : ℝ≥0} (hq : 2 < q) (hd : 0 < d)
    (he : (q:ℝ)⁻¹ = (2:ℝ)⁻¹ - ((2*d:ℕ):ℝ)⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ ψ : SmoothRealFunction A, tsupport ψ.value ⊆ K →
      (lpNorm ψ.value q g.volumeMeasure)^2 ≤ C * g.integral (g.energy ψ ψ).value := by
  obtain ⟨b,hb,hbnd⟩ := g.chart_lpNorm_bound i hK hs
  obtain ⟨a,ha,habnd⟩ := g.chart_gradient_L2_bound i hK hs
  let S : ℝ := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Coordinates d)) 2
  let B : ℝ := b ^ (q:ℝ)⁻¹
  have hB : 0 ≤ B := Real.rpow_nonneg hb.le _
  have hcoef : 0 ≤ B^2*S^2*a := mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) ha.le
  refine ⟨1+B^2*S^2*a,by linarith,fun ψ hψ => ?_⟩
  have hq0 : 0 < q := lt_trans (by norm_num) hq
  have hl := hbnd ψ hψ q hq0
  have hls := (sq_le_sq₀ lpNorm_nonneg (mul_nonneg hB lpNorm_nonneg)).mpr hl
  obtain ⟨hu,huc,_⟩ := ψ.localized_smooth_compact i (hψ.trans hs)
  have hsobo := euclidean_sobolev_sq hd he hu huc
  have hgr := habnd ψ hψ
  have hEn := g.integral_nonneg (g.energy_nonneg ψ)
  calc
    _ ≤ B^2 * (lpNorm (ψ.localized i) q volume)^2 := by simpa only [mul_pow] using hls
    _ ≤ B^2 * (S^2 * ∫ z, ‖fderiv ℝ (ψ.localized i) z‖^2) :=
      mul_le_mul_of_nonneg_left hsobo (sq_nonneg _)
    _ = (B^2*S^2) * ∫ z, ‖fderiv ℝ (ψ.localized i) z‖^2 := by ring
    _ ≤ (B^2*S^2) * (a*g.integral (g.energy ψ ψ).value) :=
      mul_le_mul_of_nonneg_left hgr (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ ≤ _ := by nlinarith

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
