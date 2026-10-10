import OAI.Analysis.FreeEntropy.GaussianCorrection

namespace OAI

universe u1

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace FiniteEntropySeparation
 theorem integral_le_of_liminf_tests {Ω : Type u1} [MeasurableSpace Ω] (ν : Measure Ω)
    (F : Ω → ℝ) (g : ℕ → Ω → ℝ) (hF : Integrable F ν) (hF0 : 0≤ᵐ[ν] F)
    (hg : ∀k,Integrable (g k) ν) (hg0 : ∀k,0≤ᵐ[ν] g k)
    (hl : ∀ᵐs ∂ν,ENNReal.ofReal (F s) ≤ liminf (fun k => ENNReal.ofReal (g k s)) atTop)
    {C : ℝ} (hC : ∀ᶠk in atTop,(∫s,g k s ∂ν) ≤ C) : (∫s,F s ∂ν) ≤ C := by
  have hc : 0≤C := by
    obtain ⟨k,hk⟩ := hC.exists
    exact (integral_nonneg_of_ae (hg0 k)).trans hk
  apply (ENNReal.ofReal_le_ofReal_iff hc).mp
  rw [ofReal_integral_eq_lintegral_ofReal hF hF0]
  apply (lintegral_mono_ae hl).trans
  apply (lintegral_liminf_le' (fun k => ENNReal.measurable_ofReal.comp_aemeasurable (hg k).aestronglyMeasurable.aemeasurable)).trans
  apply liminf_le_of_frequently_le'
  apply Eventually.frequently
  filter_upwards [hC] with k hk
  simp only [Function.comp_apply]
  rw [← ofReal_integral_eq_lintegral_ofReal (hg k) (hg0 k)]
  exact ENNReal.ofReal_le_ofReal hk
variable {n : ℕ} {D : ℕ → ℕ} (hD : ∀k,0<D k)
  (μ : (k:ℕ) → Measure (MatrixCoordinates n (D k))) [∀k,IsProbabilityMeasure (μ k)]
  (K : ℕ → ℝ) (hK : ∀k,0≤K k) (hμ : ∀k,∀ᵐa ∂μ k,‖a‖≤K k)
include hD hK hμ
 theorem matrixFlow_limit_bound (F : ℝ → ℝ) {a t β L : ℝ}
    (ha : 0<a) (hat : a≤t) (hF : IntervalIntegrable F volume a t)
    (hF0 : ∀s∈Ioc a t,0≤F s)
    (hl : ∀s∈Ioc a t,ENNReal.ofReal (F s) ≤ liminf (fun k => ENNReal.ofReal (normalizedMatrixFisher (μ k) s)) atTop)
    (hinit : ∀k,β≤normalizedMatrixEntropy (μ k) a)
    (hterm : ∀ε : ℝ,0<ε → ∀ᶠk in atTop,normalizedMatrixEntropy (μ k) t ≤ L+ε) :
    β+(1/2:ℝ)*(∫s in a..t,F s) ≤ L := by
  have ht : 0<t := ha.trans_le hat
  apply le_of_forall_pos_le_add
  intro ε hε
  have hg k := normalizedMatrixFisher_intervalIntegrable (hD k) (μ k) (hK k) (hμ k) ha ht
  have hbound : ∀ᶠk in atTop,(∫s in Ioc a t,normalizedMatrixFisher (μ k) s) ≤ 2*(L+ε-β) := by
    filter_upwards [hterm ε hε] with k hk
    have he := normalizedMatrixEntropy_flow (hD k) (μ k) (hK k) (hμ k) ha ht
    rw [intervalIntegral.integral_of_le hat] at he
    linarith [hinit k]
  have hf := integral_le_of_liminf_tests (volume.restrict (Ioc a t)) F
    (fun k => normalizedMatrixFisher (μ k)) hF.1
    ((ae_restrict_mem measurableSet_Ioc).mono (fun _ hs => hF0 _ hs))
    (fun k => (hg k).1)
    (fun k => (ae_restrict_mem measurableSet_Ioc).mono (fun s hs => normalizedMatrixFisher_nonneg (hD k) (μ k) (ha.trans hs.1)))
    ((ae_restrict_mem measurableSet_Ioc).mono (fun _ hs => hl _ hs)) hbound
  rw [intervalIntegral.integral_of_le hat]
  linarith
end FiniteEntropySeparation

end

end OAI
