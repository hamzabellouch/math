import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientStar

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)

def constantCauchy : D →⋆ₐ[ℂ] T.cauchySequenceAlgebra hadd where
  toFun x := ⟨⟨fun _ => x,memℓp_infty ⟨‖x‖,by rintro _ ⟨k,rfl⟩; exact le_rfl⟩⟩,
    T.isMetricCauchy_const x⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def quotientEmbedding : D →⋆ₐ[ℂ] T.CauchyQuotient hadd :=
  ({ T.cauchyQuotientMap hadd with map_star' := T.cauchyQuotientMap_star hadd } :
    T.cauchySequenceAlgebra hadd →⋆ₐ[ℂ] T.CauchyQuotient hadd).comp (T.constantCauchy hadd)

lemma quotientEmbedding_injective (hf : ∀ a : Positive D, a.1 ≠ 0 → 0 < T a) :
    Function.Injective (T.quotientEmbedding hadd) := by
  intro x y hxy
  have hc : (T.nullSequenceIdeal hadd).ringCon (T.constantCauchy hadd x) (T.constantCauchy hadd y) :=
    (T.nullSequenceIdeal hadd).ringCon.eq.mp hxy
  rw [T.nullSequenceIdeal_rel hadd] at hc
  change Tendsto (fun _ : ℕ => T.metricSize (x-y)) atTop (nhds 0) at hc
  have hz : T.metricSize (x-y) = 0 := tendsto_nhds_unique tendsto_const_nhds hc
  exact sub_eq_zero.mp ((T.metricSize_eq_zero_iff hf _).mp hz)
end CuntzPureness.PositiveQuasitrace

end

end OAI
