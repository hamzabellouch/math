import OAI.Analysis.Pureness.States.QuotientGenuineQuasitrace

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (ht : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hs : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotientPositiveQuasitrace_metricSize (x : T.CauchyQuotient ht) :
    (T.quotientPositiveQuasitrace ht hs).metricSize x = T.quotientMetricSize ht hs x := rfl

lemma quotientPositiveQuasitrace_metricSize_add (x y : T.CauchyQuotient ht) :
    (T.quotientPositiveQuasitrace ht hs).metricSize (x+y) ≤
      (T.quotientPositiveQuasitrace ht hs).metricSize x +
        (T.quotientPositiveQuasitrace ht hs).metricSize y :=
  T.quotientMetricSize_add ht hs x y

lemma quotientPositiveQuasitrace_sqrt_add (a b : Positive (T.CauchyQuotient ht)) :
    Real.sqrt ((T.quotientPositiveQuasitrace ht hs) (Positive.add a b)) ≤
      Real.sqrt ((T.quotientPositiveQuasitrace ht hs) a) +
        Real.sqrt ((T.quotientPositiveQuasitrace ht hs) b) := by
  obtain ⟨u,hu⟩ := T.exists_positive_quotient_representative ht a
  obtain ⟨v,hv⟩ := T.exists_positive_quotient_representative ht b
  have hlim (w : Positive (T.cauchySequenceAlgebra ht)) :
      Tendsto (fun n => Real.sqrt (T (Positive.map
        (T.cauchySequenceEval ht n).toNonUnitalStarAlgHom w))) atTop
        (nhds (Real.sqrt (T.quotientValue ht hs (T.cauchyQuotientMap ht w.1)).re)) := by
    have he (n : ℕ) :
        T (Positive.map (T.cauchySequenceEval ht n).toNonUnitalStarAlgHom w) =
          (T.complexValue (w.1.1 n)).re := by
      exact (congrArg Complex.re (T.complexValue_positive
        (Positive.map (T.cauchySequenceEval ht n).toNonUnitalStarAlgHom w))).symm
    simp only [he,T.quotientValue_map]
    exact (Real.continuous_sqrt.tendsto _).comp
      ((Complex.continuous_re.tendsto _).comp (T.cauchyValue_tendsto ht hs w.1))
  have h := le_of_tendsto_of_tendsto (hlim (Positive.add u v)) ((hlim u).add (hlim v))
    (Filter.Eventually.of_forall (fun n => hs
      (Positive.map (T.cauchySequenceEval ht n).toNonUnitalStarAlgHom u)
      (Positive.map (T.cauchySequenceEval ht n).toNonUnitalStarAlgHom v)))
  change Real.sqrt (T.quotientValue ht hs (T.cauchyQuotientMap ht (u.1+v.1))).re ≤
    Real.sqrt (T.quotientValue ht hs (T.cauchyQuotientMap ht u.1)).re +
      Real.sqrt (T.quotientValue ht hs (T.cauchyQuotientMap ht v.1)).re at h
  have he : T.cauchyQuotientMap ht (u.1+v.1) =
      T.cauchyQuotientMap ht u.1 + T.cauchyQuotientMap ht v.1 :=
    (T.cauchyQuotientMap ht).map_add u.1 v.1
  rw [he,hu,hv] at h
  exact h
end CuntzPureness.PositiveQuasitrace

end

end OAI
