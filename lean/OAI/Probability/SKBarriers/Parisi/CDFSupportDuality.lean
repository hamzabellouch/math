import Mathlib
import OAI.Probability.SKBarriers.Scalar.SignedCDFTransport

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem supported_probability_ae (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1) :
    ∀ᵐ x ∂(μ : Measure ℝ), x∈Icc (0:ℝ) 1 := by
  rw [ae_iff]
  change (μ : Measure ℝ) (Icc (0:ℝ) 1)ᶜ=0
  rw [measure_compl measurableSet_Icc (by simp [hμ]),hμ,measure_univ,tsub_self]

theorem integral_unitCDF_probability (μ : ProbabilityMeasure ℝ) (s c : ℝ) :
    (∫ t, unitCDF t s*c ∂(μ : Measure ℝ))=cdf (μ : Measure ℝ) s*c := by
  have E : (fun t => unitCDF t s*c)=(Iic s).indicator (fun _ => c) := by
    funext t
    simp only [unitCDF,indicator_apply,mem_Iic]
    split_ifs <;> simp
  rw [E,integral_indicator measurableSet_Iic,setIntegral_const,cdf_eq_real,smul_eq_mul]

theorem supported_cdf_integral_duality (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc (0:ℝ) 1)) :
    (∫ s in Icc (0:ℝ) 1, cdf (μ : Measure ℝ) s*g s)=
      ∫ q, (∫ s in q..1, g s) ∂(μ : Measure ℝ) := by
  have E : (fun p : ℝ×ℝ => unitCDF p.1 p.2*g p.2)=
      {p : ℝ×ℝ | p.1≤p.2}.indicator (fun p => g p.2) := by
    funext p
    simp only [unitCDF,indicator_apply,mem_ofPred_eq]
    split_ifs <;> simp
  have HI : Integrable (fun p : ℝ×ℝ => unitCDF p.1 p.2*g p.2)
      ((μ : Measure ℝ).prod (volume.restrict (Icc (0:ℝ) 1))) := by
    rw [E]
    exact (hg.comp_snd (μ : Measure ℝ)).indicator (measurableSet_le measurable_fst measurable_snd)
  have H := integral_integral_swap (f:=fun q s => unitCDF q s*g s) HI
  simp_rw [integral_unitCDF_probability] at H
  rw [← H]
  apply integral_congr_ae
  filter_upwards [supported_probability_ae μ hμ] with q hq
  exact unitCDF_mul_integral q hq g

end SK.Analytic

end
end

end OAI
