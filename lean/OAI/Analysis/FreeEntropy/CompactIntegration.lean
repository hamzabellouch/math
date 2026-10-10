import OAI.Analysis.FreeEntropy.GaussianDifferential

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace FiniteEntropySeparation
variable {E : Type u1} {F : Type u2} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
 omit [NormedSpace ℝ E] [BorelSpace E] [NormedSpace ℝ F] in
 theorem integrable_of_compact_ae (μ : Measure E) [IsFiniteMeasure μ] {K : Set E} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ,x∈K) {f : E → F} (hm : AEStronglyMeasurable f μ) (hf : ContinuousOn f K) : Integrable f μ := by
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hf
  apply (integrable_const C).mono' hm
  filter_upwards [hμ] with x hx
  exact hC x hx
 theorem hasDerivAt_integral_compact {E : Type u1} {F : Type u2}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [SecondCountableTopology E] (μ : Measure E) [IsFiniteMeasure μ] {K : Set E} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ,x∈K) (f f' : ℝ → E → F) {a b t : ℝ} (ha : a<t) (hb : t<b)
    (hf : ∀s∈Icc a b,Continuous (f s)) (hf' : ∀s∈Icc a b,Continuous (f' s))
    (hc : ContinuousOn (fun z : ℝ × E => f' z.1 z.2) (Icc a b ×ˢ K))
    (hd : ∀s∈Icc a b,∀x∈K,HasDerivAt (fun u => f u x) (f' s x) s) :
    Integrable (f' t) μ ∧ HasDerivAt (fun u => ∫ x,f u x ∂μ) (∫ x,f' t x ∂μ) t := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hc
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Icc a b) (bound := fun _ => C) (Icc_mem_nhds ha hb)
  · filter_upwards [Icc_mem_nhds ha hb] with s hs
    exact (hf s hs).aestronglyMeasurable
  · exact integrable_of_compact_ae μ hK hμ (hf t ⟨ha.le,hb.le⟩).aestronglyMeasurable (hf t ⟨ha.le,hb.le⟩).continuousOn
  · exact (hf' t ⟨ha.le,hb.le⟩).aestronglyMeasurable
  · filter_upwards [hμ] with x hx s hs
    exact hC (s,x) ⟨hs,hx⟩
  · exact integrable_const _
  · filter_upwards [hμ] with x hx s hs
    exact hd s hs x hx
end FiniteEntropySeparation

end

end OAI
