import OAI.Analysis.Pureness.Quasitrace.QuasitraceProportionalMetric

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal
variable {D E : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
  [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E] [Nontrivial E]
variable (T : CuntzPureness.PositiveQuasitrace D) (U : CuntzPureness.PositiveQuasitrace E)
variable (ht : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hu : ∀ x y, U.metricSize (x+y) ≤ U.metricSize x+U.metricSize y)
variable (φ : D →⋆ₙₐ[ℂ] E) (c : ℝ≥0)
variable (hφ : ∀ a, U (Positive.map φ a) = (c : ℝ)*T a)

def proportionalCauchyFunctor : T.cauchySequenceAlgebra ht →⋆ₙₐ[ℂ] U.cauchySequenceAlgebra hu where
  toFun u := ⟨⟨fun n => φ (u.1 n),memℓp_infty ⟨‖u.1‖,by
    rintro _ ⟨n,rfl⟩
    exact (NonUnitalStarAlgHom.norm_apply_le φ _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero u.1 n)⟩⟩,by
      change U.IsMetricCauchy (fun n => φ (u.1 n))
      have hc : T.IsMetricCauchy (fun n => u.1 n) := u.2
      exact T.isMetricCauchy_map_proportional U φ c hφ hc⟩
  map_zero' := by apply Subtype.ext; apply lp.ext; funext n; exact _root_.map_zero φ
  map_add' u v := by apply Subtype.ext; apply lp.ext; funext n; exact map_add φ _ _
  map_mul' u v := by apply Subtype.ext; apply lp.ext; funext n; exact map_mul φ _ _
  map_smul' c u := by apply Subtype.ext; apply lp.ext; funext n; exact _root_.map_smul φ c _
  map_star' u := by apply Subtype.ext; apply lp.ext; funext n; exact map_star φ _

lemma proportionalCauchyFunctor_rel (u v : T.cauchySequenceAlgebra ht)
    (h : (T.nullSequenceIdeal ht).ringCon u v) :
    (U.nullSequenceIdeal hu).ringCon (T.proportionalCauchyFunctor U ht hu φ c hφ u)
      (T.proportionalCauchyFunctor U ht hu φ c hφ v) := by
  rw [T.nullSequenceIdeal_rel ht] at h
  rw [U.nullSequenceIdeal_rel hu]
  change Tendsto (fun n => U.metricSize (φ (u.1 n)-φ (v.1 n))) atTop (nhds 0)
  simpa only [IsMetricNull,map_sub] using T.isMetricNull_map_proportional U φ c hφ h

def proportionalQuotientFunctor : T.CauchyQuotient ht →⋆ₙₐ[ℂ] U.CauchyQuotient hu where
  toFun := Quotient.map' (T.proportionalCauchyFunctor U ht hu φ c hφ)
    (T.proportionalCauchyFunctor_rel U ht hu φ c hφ)
  map_zero' := by
    change U.cauchyQuotientMap hu (T.proportionalCauchyFunctor U ht hu φ c hφ 0)=0
    rw [_root_.map_zero,_root_.map_zero]
  map_add' x y := by
    obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective ht x
    obtain ⟨v,rfl⟩ := T.cauchyQuotientMap_surjective ht y
    change U.cauchyQuotientMap hu (T.proportionalCauchyFunctor U ht hu φ c hφ (u+v))=
      U.cauchyQuotientMap hu (T.proportionalCauchyFunctor U ht hu φ c hφ u)+
        U.cauchyQuotientMap hu (T.proportionalCauchyFunctor U ht hu φ c hφ v)
    exact (congrArg (U.cauchyQuotientMap hu) (_root_.map_add (T.proportionalCauchyFunctor U ht hu φ c hφ) u v)).trans
      ((U.cauchyQuotientMap hu).map_add _ _)
  map_mul' x y := by
    obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective ht x
    obtain ⟨v,rfl⟩ := T.cauchyQuotientMap_surjective ht y
    change U.cauchyQuotientMap hu (T.proportionalCauchyFunctor U ht hu φ c hφ (u*v))=_
    rw [map_mul,map_mul]; rfl
  map_smul' r x := by
    obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective ht x
    change U.cauchyQuotientMap hu (T.proportionalCauchyFunctor U ht hu φ c hφ (r • u))=
      r • U.cauchyQuotientMap hu (T.proportionalCauchyFunctor U ht hu φ c hφ u)
    exact (congrArg (U.cauchyQuotientMap hu) (_root_.map_smul (T.proportionalCauchyFunctor U ht hu φ c hφ) r u)).trans
      ((U.cauchyQuotientMap hu).toLinearMap.map_smul r _)
  map_star' x := by
    obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective ht x
    change U.cauchyQuotientMap hu (T.proportionalCauchyFunctor U ht hu φ c hφ (star u))=_
    rw [map_star,U.cauchyQuotientMap_star]; rfl

lemma proportionalQuotientFunctor_map (u : T.cauchySequenceAlgebra ht) :
    T.proportionalQuotientFunctor U ht hu φ c hφ (T.cauchyQuotientMap ht u)=
      U.cauchyQuotientMap hu (T.proportionalCauchyFunctor U ht hu φ c hφ u) := rfl

lemma proportionalQuotientFunctor_embedding (x : D) :
    T.proportionalQuotientFunctor U ht hu φ c hφ (T.quotientEmbedding ht x)=U.quotientEmbedding hu (φ x) := rfl

variable (hst : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))
variable (hsu : ∀ a b : Positive E, Real.sqrt (U (Positive.add a b)) ≤ Real.sqrt (U a)+Real.sqrt (U b))

lemma proportionalQuotientFunctor_value (x : T.CauchyQuotient ht) :
    U.quotientValue hu hsu (T.proportionalQuotientFunctor U ht hu φ c hφ x) =
      (c : ℂ)*T.quotientValue ht hst x := by
  obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective ht x
  rw [T.proportionalQuotientFunctor_map,U.quotientValue_map,T.quotientValue_map]
  have hv := U.cauchyValue_tendsto hu hsu (T.proportionalCauchyFunctor U ht hu φ c hφ u)
  change Tendsto (fun n => U.complexValue (φ (u.1 n))) atTop _ at hv
  simp only [T.complexValue_map_proportional U φ c hφ] at hv
  exact tendsto_nhds_unique hv ((T.cauchyValue_tendsto ht hst u).const_mul (c : ℂ))

include hφ in
lemma proportionalQuotientFunctor_injective (hc : 0 < c) :
    Function.Injective (T.proportionalQuotientFunctor U ht hu φ c hφ) := by
  intro x y hxy
  obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective ht x
  obtain ⟨v,rfl⟩ := T.cauchyQuotientMap_surjective ht y
  apply Quotient.sound
  have hh := Quotient.exact hxy
  change (T.nullSequenceIdeal ht).ringCon u v
  change (U.nullSequenceIdeal hu).ringCon
    (T.proportionalCauchyFunctor U ht hu φ c hφ u)
    (T.proportionalCauchyFunctor U ht hu φ c hφ v) at hh
  rw [T.nullSequenceIdeal_rel ht]
  rw [U.nullSequenceIdeal_rel hu] at hh
  apply (T.isMetricNull_map_proportional_iff U φ c hφ hc _).mp
  change U.IsMetricNull (fun n => φ (u.1 n)-φ (v.1 n)) at hh
  simpa only [map_sub] using hh

lemma proportionalQuotientFunctor_isometry (hc : 0 < c) :
    Isometry (T.proportionalQuotientFunctor U ht hu φ c hφ) :=
  NonUnitalStarAlgHom.isometry _ (T.proportionalQuotientFunctor_injective U ht hu φ c hφ hc)
end CuntzPureness.PositiveQuasitrace

end

end OAI
