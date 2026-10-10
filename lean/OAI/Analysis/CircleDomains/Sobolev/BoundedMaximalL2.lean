import OAI.Analysis.DiskMaximal.MaximalEstimates
import OAI.Analysis.CircleDomains.Topology.PlanarMaximalInput
import OAI.Analysis.CircleDomains.Sobolev.MonotoneL2Limit

namespace OAI

/-! The Vitali/interpolation estimate, specialized to bounded,
integrable planar inputs. The representative dominates every ball average. -/
open Set Function Filter MeasureTheory Metric DiskMaximalTools
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

theorem bounded_maximal_L2 {f : ℂ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f) (hf2 : MemLp f 2 volume)
    {B : ℝ} (hB : ∀ x, f x ≤ B) :
    ∃ m : ℂ → ℝ, Measurable m ∧ (∀ x, 0 ≤ m x) ∧ MemLp m 2 volume ∧
      (∫ x, m x^2) ≤ 200*(∫ x, f x^2) ∧
      (∀ x r, 0 < r → (∫ y in ball x r, f y) ≤ volume.real (ball x r)*m x) ∧
      ∀ x, ENNReal.ofReal (m x) = rationalMaximal (volume.withDensity (fun y => ENNReal.ofReal (f y))) x := by
  let ν := volume.withDensity (fun x => ENNReal.ofReal (f x))
  have hfin : (∫⁻ x, ENNReal.ofReal (f x)) < ∞ :=
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ hf0)).mp hfi.hasFiniteIntegral
  have : IsFiniteMeasure ν := ⟨by
    change volume.withDensity (fun x => ENNReal.ofReal (f x)) univ < ∞
    simpa only [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using hfin⟩
  have hbound (x : ℂ) : rationalMaximal ν x ≤ ENNReal.ofReal B :=
    rationalMaximal_le_of_density_le (fun y => ENNReal.ofReal_le_ofReal (hB y)) x
  have hne (x : ℂ) : rationalMaximal ν x ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound x)
  let m := fun x => (rationalMaximal ν x).toReal
  have hm : Measurable m := (measurable_rationalMaximal ν).ennreal_toReal
  have hm0 (x : ℂ) : 0 ≤ m x := ENNReal.toReal_nonneg
  have hme (x : ℂ) : ENNReal.ofReal (m x) = rationalMaximal ν x :=
    ENNReal.ofReal_toReal (hne x)
  have hs := strong_rationalMaximal hf hf0 (p := 2) (by norm_num)
  norm_num only [Real.rpow_two, sub_self, sub_zero, Real.rpow_one, mul_one,
    div_one, Nat.cast_ofNat] at hs
  change (∫⁻ x, ENNReal.ofReal (m x^2)) ≤ ENNReal.ofReal (200:ℝ) *
    (∫⁻ x, ENNReal.ofReal (f x^2)) at hs
  have hfi2 := hf2.integrable_sq
  have he : (∫⁻ x, ENNReal.ofReal (f x^2)) = ENNReal.ofReal (∫ x, f x^2) :=
    (ofReal_integral_eq_lintegral_ofReal hfi2 (ae_of_all _ (fun x => sq_nonneg (f x)))).symm
  rw [he, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 200)] at hs
  have hmi : Integrable (fun x => m x^2) :=
    ⟨(hm.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x => sq_nonneg (m x)))).mpr
        (hs.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨m, hm, hm0, (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hmi, ?_, ?_, hme⟩
  · rw [← ofReal_integral_eq_lintegral_ofReal hmi (ae_of_all _ (fun x => sq_nonneg (m x)))] at hs
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num)
      (integral_nonneg (fun x => sq_nonneg (f x))))).mp hs
  · intro x r hr
    have hav := disk_average_le_rationalMaximal_exact ν x hr
    have hv : volume (ball x r) ≠ 0 := measure_ball_pos volume x hr |>.ne'
    have hh := (ENNReal.div_le_iff hv measure_ball_lt_top.ne).mp hav
    have hint : IntegrableOn f (ball x r) volume := hfi.integrableOn
    have hi : ENNReal.ofReal (∫ y in ball x r, f y) = ν (ball x r) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hf0),
        withDensity_apply _ measurableSet_ball]
    rw [← hme x, ← hi] at hh
    have hvol : ENNReal.ofReal (volume.real (ball x r)) = volume (ball x r) :=
      ENNReal.ofReal_toReal measure_ball_lt_top.ne
    rw [← hvol, ← ENNReal.ofReal_mul (hm0 x)] at hh
    have := (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (hm0 x) measureReal_nonneg)).mp hh
    simpa only [mul_comm] using this

end CircleDomainRigidity

end

end OAI
