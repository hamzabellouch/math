import OAI.Geometry.RCD.Transport.SobolevPlanDerivative
import OAI.Geometry.RCD.Heat.HeatOffDiagonalL2

namespace OAI

/-! # Quantitative variation of Sobolev representatives along compressed paths -/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates

private theorem ac_variation_sq_le {f G : ℝ → ℝ} {D : ℝ}
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hG : MemLp G 2 (volume.restrict (Icc (0:ℝ) 1)))
    (hb : ∀ᵐ t : ℝ, t∈Ioo (0:ℝ) 1 → |deriv f t|≤D*G t) :
    (∫ t in Icc (0:ℝ) 1, |deriv f t|)^2≤D^2*∫ t in Icc (0:ℝ) 1, (G t)^2 := by
  let ν := volume.restrict (Icc (0:ℝ) 1)
  have hdf : Integrable (deriv f) ν :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hf.intervalIntegrable_deriv
  have hb' : ∀ᵐ t ∂ν, |deriv f t|≤D*G t := by
    rw [show ν=volume.restrict (Ioo (0:ℝ) 1) from restrict_Ioo_eq_restrict_Icc.symm]
    filter_upwards [ae_restrict_of_ae hb,ae_restrict_mem measurableSet_Ioo] with t ht hs
    exact ht hs
  have hI : (∫ t, |deriv f t| ∂ν)≤D*(∫ t, G t ∂ν) := by
    have hh := integral_mono_ae hdf.abs ((hG.integrable (by norm_num)).const_mul D) hb'
    simpa only [integral_const_mul] using hh
  have hm : ν.real univ=1 := by
    simp only [ν,Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,sub_zero,
      ENNReal.ofReal_one,ENNReal.toReal_one]
  have hcs : (∫ t, G t ∂ν)^2≤∫ t, (G t)^2 ∂ν := by
    have hh := integral_mul_sq_le_integral_sq ν G (fun _ => 1) hG (memLp_const (1:ℝ))
    simpa only [mul_one,one_pow,integral_const,smul_eq_mul,hm,sq_abs] using hh
  have hs := mul_self_le_mul_self (integral_nonneg (fun _ => abs_nonneg _)) hI
  have hh := mul_le_mul_of_nonneg_left hcs (sq_nonneg D)
  calc
    _≤(D*(∫ t, G t ∂ν))^2 := by simpa only [← pow_two] using hs
    _=D^2*(∫ t, G t ∂ν)^2 := mul_pow _ _ _
    _≤_ := hh

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem IsRelaxedSlope.testPlan_ae_sobolev_variation (μ : Measure X)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C≠∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G) :
    ∀ᵐ γ ∂π, ∃ f : ℝ → ℝ,
      AbsolutelyContinuousOnInterval f 0 1 ∧ f 0=u (γ 0) ∧ f 1=u (γ 1) ∧
      (f =ᵐ[volume.restrict (Icc (0:ℝ) 1)] fun t => u (geodesicExtension γ t)) ∧
      (∫ t in Icc (0:ℝ) 1, |deriv f t|)^2≤
        (dist (γ 0) (γ 1))^2*(∫ t in Icc (0:ℝ) 1, (G (geodesicExtension γ t))^2) := by
  let : IsFiniteMeasure (testPlanMeasure π) := by unfold testPlanMeasure; infer_instance
  have hmem := testPlanMeasure_eval_memLp μ π hC hcomp G
  have hsq := (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).mp hmem
  have hinner := hsq.prod_left_ae
  have hmi := (hmem.integrable (by norm_num : (1:ℝ≥0∞)≤2)).prod_left_ae
  filter_upwards [hG.testPlan_ae_sobolev_derivative μ π hgeo hC hcomp hD,hinner,hmi]
    with γ hf hsqγ hmγ
  obtain ⟨f,hf,h0,h1,heq,hderiv⟩ := hf
  refine ⟨f,hf,h0,h1,heq,?_⟩
  apply ac_variation_sq_le hf
  · exact (memLp_two_iff_integrable_sq hmγ.aestronglyMeasurable).mpr hsqγ
  · exact hderiv.mono (fun _ ht hs => (ht hs).2)

end RegularPointCoordinates

end

end OAI
