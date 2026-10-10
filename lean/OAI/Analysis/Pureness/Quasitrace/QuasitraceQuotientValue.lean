import OAI.Analysis.Pureness.Quasitrace.QuasitraceComplexLimits
import OAI.Analysis.Pureness.Quasitrace.QuasitraceConstantEmbedding

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace UniformSpace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

def cauchyValue (u : T.cauchySequenceAlgebra hadd) : ℂ :=
  Classical.choose (T.complex_values_converge hadd hsqrt (fun k => u.1 k) u.2
    ‖u.1‖ (norm_nonneg _) (lp.norm_apply_le_norm ENNReal.top_ne_zero u.1))
lemma cauchyValue_tendsto (u : T.cauchySequenceAlgebra hadd) :
    Tendsto (fun k => T.complexValue (u.1 k)) atTop (nhds (T.cauchyValue hadd hsqrt u)) :=
  Classical.choose_spec (T.complex_values_converge hadd hsqrt (fun k => u.1 k) u.2
    ‖u.1‖ (norm_nonneg _) (lp.norm_apply_le_norm ENNReal.top_ne_zero u.1))

lemma cauchyValue_congr (u v : T.cauchySequenceAlgebra hadd)
    (huv : (T.nullSequenceIdeal hadd).ringCon u v) : T.cauchyValue hadd hsqrt u = T.cauchyValue hadd hsqrt v := by
  rw [T.nullSequenceIdeal_rel hadd] at huv
  exact T.complex_values_same_limit hadd hsqrt (fun k => u.1 k) (fun k => v.1 k) u.2 v.2 huv
    (max ‖u.1‖ ‖v.1‖) (le_max_of_le_left (norm_nonneg _))
    (fun k => (lp.norm_apply_le_norm ENNReal.top_ne_zero u.1 k).trans (le_max_left _ _))
    (fun k => (lp.norm_apply_le_norm ENNReal.top_ne_zero v.1 k).trans (le_max_right _ _))
    _ _ (T.cauchyValue_tendsto hadd hsqrt u) (T.cauchyValue_tendsto hadd hsqrt v)

def quotientValue : T.CauchyQuotient hadd → ℂ :=
  Quotient.lift (T.cauchyValue hadd hsqrt) (T.cauchyValue_congr hadd hsqrt)

lemma quotientValue_map (u : T.cauchySequenceAlgebra hadd) :
    T.quotientValue hadd hsqrt (T.cauchyQuotientMap hadd u) = T.cauchyValue hadd hsqrt u := rfl
lemma quotientValue_embedding (x : D) :
    T.quotientValue hadd hsqrt (T.quotientEmbedding hadd x) = T.complexValue x := by
  change T.cauchyValue hadd hsqrt (T.constantCauchy hadd x) = T.complexValue x
  exact tendsto_nhds_unique (T.cauchyValue_tendsto hadd hsqrt (T.constantCauchy hadd x)) tendsto_const_nhds

lemma cauchyValue_polar (u : T.cauchySequenceAlgebra hadd) :
    T.cauchyValue hadd hsqrt (star u*u) = T.cauchyValue hadd hsqrt (u*star u) := by
  have h1 := T.cauchyValue_tendsto hadd hsqrt (star u*u)
  have h2 := T.cauchyValue_tendsto hadd hsqrt (u*star u)
  have he : (fun k => T.complexValue ((star u*u).1 k)) =
      (fun k => T.complexValue ((u*star u).1 k)) := by
    funext k
    simpa using T.complexValue_polar (u.1 k)
  rw [he] at h1
  exact tendsto_nhds_unique h1 h2

lemma quotientValue_polar (x : T.CauchyQuotient hadd) :
    T.quotientValue hadd hsqrt (star x*x) = T.quotientValue hadd hsqrt (x*star x) := by
  obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective hadd x
  rw [← T.cauchyQuotientMap_star,← map_mul,← map_mul,T.quotientValue_map,T.quotientValue_map]
  exact T.cauchyValue_polar hadd hsqrt u

lemma quotientValue_square_nonneg (x : T.CauchyQuotient hadd) :
    0 ≤ T.quotientValue hadd hsqrt (star x*x) := by
  obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective hadd x
  rw [← T.cauchyQuotientMap_star,← map_mul,T.quotientValue_map]
  apply ge_of_tendsto (T.cauchyValue_tendsto hadd hsqrt (star u*u))
  exact Eventually.of_forall (fun k => by simpa using T.complexValue_square_nonneg (u.1 k))
end CuntzPureness.PositiveQuasitrace

end

end OAI
