import OAI.Analysis.Pureness.States.QuotientGenuineQuasitrace

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D E : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
  [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E] [Nontrivial E]
variable (T : CuntzPureness.PositiveQuasitrace D) (U : CuntzPureness.PositiveQuasitrace E)
variable (ht : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hu : ∀ x y, U.metricSize (x+y) ≤ U.metricSize x+U.metricSize y)
variable (φ : D →⋆ₙₐ[ℂ] E) (hφ : ∀ a, U (Positive.map φ a)=T a)

omit [Nontrivial D] [Nontrivial E] in
include hφ in
lemma metricSize_map_of_positive_compatible (x : D) : U.metricSize (φ x)=T.metricSize x := by
  unfold metricSize
  congr 1
  have he : Positive.starMul (φ x)=Positive.map φ (Positive.starMul x) := by
    apply Subtype.ext
    change star (φ x)*φ x=φ (star x*x)
    rw [map_mul,map_star]
  rw [he,hφ]

omit [Nontrivial D] [Nontrivial E] in
include hφ in
lemma distance_map_of_positive_compatible (x y : D) : U.distance (φ x) (φ y)=T.distance x y := by
  unfold distance
  rw [← map_sub,T.metricSize_map_of_positive_compatible U φ hφ]

def cauchySequenceFunctor : T.cauchySequenceAlgebra ht →⋆ₙₐ[ℂ] U.cauchySequenceAlgebra hu where
  toFun u := ⟨⟨fun n => φ (u.1 n),memℓp_infty ⟨‖u.1‖,by
    rintro _ ⟨n,rfl⟩
    exact (NonUnitalStarAlgHom.norm_apply_le φ _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero u.1 n)⟩⟩,by
      change U.IsMetricCauchy (fun n => φ (u.1 n))
      have hc : T.IsMetricCauchy (fun n => u.1 n) := u.2
      simpa only [IsMetricCauchy,T.distance_map_of_positive_compatible U φ hφ] using hc⟩
  map_zero' := by apply Subtype.ext; apply lp.ext; funext n; exact _root_.map_zero φ
  map_add' u v := by apply Subtype.ext; apply lp.ext; funext n; exact map_add φ _ _
  map_mul' u v := by apply Subtype.ext; apply lp.ext; funext n; exact map_mul φ _ _
  map_smul' c u := by apply Subtype.ext; apply lp.ext; funext n; exact _root_.map_smul φ c _
  map_star' u := by apply Subtype.ext; apply lp.ext; funext n; exact map_star φ _

lemma cauchySequenceFunctor_rel (u v : T.cauchySequenceAlgebra ht)
    (h : (T.nullSequenceIdeal ht).ringCon u v) :
    (U.nullSequenceIdeal hu).ringCon (T.cauchySequenceFunctor U ht hu φ hφ u)
      (T.cauchySequenceFunctor U ht hu φ hφ v) := by
  rw [T.nullSequenceIdeal_rel ht] at h
  rw [U.nullSequenceIdeal_rel hu]
  change Tendsto (fun n => U.metricSize (φ (u.1 n)-φ (v.1 n))) atTop (nhds 0)
  simpa only [IsMetricNull,← map_sub,T.metricSize_map_of_positive_compatible U φ hφ] using h

def quotientFunctor : T.CauchyQuotient ht →⋆ₙₐ[ℂ] U.CauchyQuotient hu where
  toFun := Quotient.map' (T.cauchySequenceFunctor U ht hu φ hφ)
    (T.cauchySequenceFunctor_rel U ht hu φ hφ)
  map_zero' := by
    change U.cauchyQuotientMap hu (T.cauchySequenceFunctor U ht hu φ hφ 0)=0
    rw [_root_.map_zero,_root_.map_zero]
  map_add' x y := by
    obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective ht x
    obtain ⟨v,rfl⟩ := T.cauchyQuotientMap_surjective ht y
    change U.cauchyQuotientMap hu (T.cauchySequenceFunctor U ht hu φ hφ (u+v))=
      U.cauchyQuotientMap hu (T.cauchySequenceFunctor U ht hu φ hφ u)+
        U.cauchyQuotientMap hu (T.cauchySequenceFunctor U ht hu φ hφ v)
    exact (congrArg (U.cauchyQuotientMap hu) (_root_.map_add (T.cauchySequenceFunctor U ht hu φ hφ) u v)).trans
      ((U.cauchyQuotientMap hu).map_add _ _)
  map_mul' x y := by
    obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective ht x
    obtain ⟨v,rfl⟩ := T.cauchyQuotientMap_surjective ht y
    change U.cauchyQuotientMap hu (T.cauchySequenceFunctor U ht hu φ hφ (u*v))=_
    rw [map_mul,map_mul]; rfl
  map_smul' c x := by
    obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective ht x
    change U.cauchyQuotientMap hu (T.cauchySequenceFunctor U ht hu φ hφ (c • u))=
      c • U.cauchyQuotientMap hu (T.cauchySequenceFunctor U ht hu φ hφ u)
    exact (congrArg (U.cauchyQuotientMap hu) (_root_.map_smul (T.cauchySequenceFunctor U ht hu φ hφ) c u)).trans
      ((U.cauchyQuotientMap hu).toLinearMap.map_smul c _)
  map_star' x := by
    obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective ht x
    change U.cauchyQuotientMap hu (T.cauchySequenceFunctor U ht hu φ hφ (star u))=_
    rw [map_star,U.cauchyQuotientMap_star]; rfl

lemma quotientFunctor_map (u : T.cauchySequenceAlgebra ht) :
    T.quotientFunctor U ht hu φ hφ (T.cauchyQuotientMap ht u)=
      U.cauchyQuotientMap hu (T.cauchySequenceFunctor U ht hu φ hφ u) := rfl

lemma quotientFunctor_embedding (x : D) :
    T.quotientFunctor U ht hu φ hφ (T.quotientEmbedding ht x)=U.quotientEmbedding hu (φ x) := rfl

variable (hst : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))
variable (hsu : ∀ a b : Positive E, Real.sqrt (U (Positive.add a b)) ≤ Real.sqrt (U a)+Real.sqrt (U b))

lemma quotientFunctor_value (x : T.CauchyQuotient ht) :
    U.quotientValue hu hsu (T.quotientFunctor U ht hu φ hφ x)=T.quotientValue ht hst x := by
  obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective ht x
  rw [T.quotientFunctor_map,U.quotientValue_map,T.quotientValue_map]
  have hv := U.cauchyValue_tendsto hu hsu (T.cauchySequenceFunctor U ht hu φ hφ u)
  change Tendsto (fun n => U.complexValue (φ (u.1 n))) atTop _ at hv
  simp only [U.complexValue_map T φ hφ] at hv
  exact tendsto_nhds_unique hv (T.cauchyValue_tendsto ht hst u)

lemma quotientFunctor_metricSize (x : T.CauchyQuotient ht) :
    U.quotientMetricSize hu hsu (T.quotientFunctor U ht hu φ hφ x)=T.quotientMetricSize ht hst x := by
  unfold quotientMetricSize
  rw [← map_star,← map_mul,T.quotientFunctor_value U ht hu φ hφ hst hsu]

lemma quotientFunctor_distance (x y : T.CauchyQuotient ht) :
    U.quotientDistance hu hsu (T.quotientFunctor U ht hu φ hφ x) (T.quotientFunctor U ht hu φ hφ y)=
      T.quotientDistance ht hst x y := by
  unfold quotientDistance
  rw [← map_sub,T.quotientFunctor_metricSize U ht hu φ hφ hst hsu]

include hst hsu in
lemma quotientFunctor_injective : Function.Injective (T.quotientFunctor U ht hu φ hφ) := by
  intro x y hxy
  apply (T.quotientDistance_eq_zero_iff ht hst x y).mp
  rw [← T.quotientFunctor_distance U ht hu φ hφ hst hsu,hxy,U.quotientDistance_self]

include hst hsu in
lemma quotientFunctor_isometry : Isometry (T.quotientFunctor U ht hu φ hφ) :=
  NonUnitalStarAlgHom.isometry _ (T.quotientFunctor_injective U ht hu φ hφ hst hsu)
end CuntzPureness.PositiveQuasitrace

end

end OAI
