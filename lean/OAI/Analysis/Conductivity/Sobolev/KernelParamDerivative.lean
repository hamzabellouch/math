import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory
open scoped Convolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [BorelSpace E]

theorem convolution_param_hasDerivAt [FiniteDimensional ℝ E]
    [Measure.IsAddHaarMeasure (volume : Measure E)] {f : E → ℝ} (hf : LocallyIntegrable f)
    {K : ℝ → E → ℝ} {S : Set ℝ} {C : Set E} (hS : IsOpen S) (hC : IsCompact C)
    (hK : ContDiffOn ℝ 1 (Function.uncurry K) (S ×ˢ univ))
    (hzero : ∀ s y, s∈S → y∉C → K s y=0)
    {s : ℝ} (hs : s∈S) {D : E → ℝ} (hD : ∀ y, HasDerivAt (fun r => K r y) (D y) s)
    (x : E) :
    HasDerivAt (fun r => (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] K r) x)
      ((f ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] D) x) s := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  let J : E → (ℝ × E →L[ℝ] ℝ) := fun y => fderiv ℝ (Function.uncurry K) (s,y)
  have hJ : Continuous J := by
    apply (hK.continuousOn_fderiv_of_isOpen (hS.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id)
    intro y
    exact ⟨hs,mem_univ _⟩
  have hJzero {y : E} (hy : y∉C) : J y=0 := by
    apply (hasFDerivAt_zero_of_eventually_const 0 ?_).fderiv
    have he : S ×ˢ Cᶜ ∈ 𝓝 (s,y) :=
      (hS.prod hC.isClosed.isOpen_compl).mem_nhds ⟨hs,hy⟩
    filter_upwards [he] with z hz
    exact hzero z.1 z.2 hz.1 hz.2
  have hJc : HasCompactSupport J :=
    HasCompactSupport.of_support_subset_isCompact hC (by
      intro y hy
      by_contra hn
      exact hy (hJzero hn))
  have hi : Integrable (fun y => L.precompR (ℝ × E) (f y) (J (x-y))) :=
    hJc.convolutionExists_right (L.precompR (ℝ × E)) hf hJ x
  have hdiff := hasFDerivAt_convolution_right_with_param L hS hC hzero hf hK (s,x) hs
  have hcurve := ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  have hout := hdiff.comp_hasDerivAt s hcurve
  have hJval (y : E) : J y (1,0)=D y := by
    have ha : DifferentiableAt ℝ (Function.uncurry K) (s,y) := (hK.contDiffAt ((hS.prod isOpen_univ).mem_nhds ⟨hs,mem_univ y⟩)).differentiableAt (by norm_num)
    have he := ha.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s y))
    exact (he.unique (hD y))
  convert hout using 1 <;> try rfl
  change (∫ y, f y*D (x-y))=(∫ y, L.precompR (ℝ × E) (f y) (J (x-y))) (1,0)
  rw [ContinuousLinearMap.integral_apply hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by simp [L,hJval])
end ScalarConductivity

end

end OAI
