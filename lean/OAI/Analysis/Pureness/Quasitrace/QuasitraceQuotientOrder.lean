import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientCFC
import OAI.Analysis.Pureness.Traces.RootFunctoriality

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

instance cauchyQuotientPartialOrder : PartialOrder (T.CauchyQuotient hadd) := CStarAlgebra.spectralOrder _
instance cauchyQuotientStarOrderedRing : StarOrderedRing (T.CauchyQuotient hadd) := CStarAlgebra.spectralOrderedRing _

lemma exists_positive_quotient_representative (x : Positive (T.CauchyQuotient hadd)) :
    ∃ u : Positive (T.cauchySequenceAlgebra hadd), T.cauchyQuotientMap hadd u.1 = x.1 := by
  obtain ⟨v,hv⟩ := T.cauchyQuotientMap_surjective hadd (CFC.sqrt x.1)
  refine ⟨⟨star v*v,star_mul_self_nonneg v⟩,?_⟩
  rw [map_mul,T.cauchyQuotientMap_star,hv,(CFC.sqrt_nonneg x.1).isSelfAdjoint.star_eq,
    CFC.sqrt_mul_sqrt_self x.1 x.2]

lemma quotientValue_nonneg (x : Positive (T.CauchyQuotient hadd)) : 0 ≤ T.quotientValue hadd hsqrt x.1 := by
  have h := T.quotientValue_square_nonneg hadd hsqrt (CFC.sqrt x.1)
  rwa [(CFC.sqrt_nonneg x.1).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self x.1 x.2] at h

lemma cauchyValue_positive_mono {u v : Positive (T.cauchySequenceAlgebra hadd)} (huv : u ≤ v) :
    T.cauchyValue hadd hsqrt u.1 ≤ T.cauchyValue hadd hsqrt v.1 := by
  apply le_of_tendsto_of_tendsto (T.cauchyValue_tendsto hadd hsqrt u.1) (T.cauchyValue_tendsto hadd hsqrt v.1)
  apply Eventually.of_forall
  intro k
  have hu := starAlgHom_positive (T.cauchySequenceEval hadd k) u.1 u.2
  have hv := starAlgHom_positive (T.cauchySequenceEval hadd k) v.1 v.2
  have hd := starAlgHom_positive (T.cauchySequenceEval hadd k) (v.1-u.1) (sub_nonneg.mpr huv)
  have hle : (u.1.1 k) ≤ (v.1.1 k) := sub_nonneg.mp hd
  have he1 := T.complexValue_positive (⟨u.1.1 k,hu⟩ : Positive D)
  have he2 := T.complexValue_positive (⟨v.1.1 k,hv⟩ : Positive D)
  calc
    _ = ((T (⟨u.1.1 k,hu⟩ : Positive D) : ℝ) : ℂ) := he1
    _ ≤ ((T (⟨v.1.1 k,hv⟩ : Positive D) : ℝ) : ℂ) := by
      exact_mod_cast T.monotone (show (⟨u.1.1 k,hu⟩ : Positive D) ≤ ⟨v.1.1 k,hv⟩ from hle)
    _ = _ := he2.symm

lemma quotientValue_positive_mono {x y : Positive (T.CauchyQuotient hadd)} (hxy : x ≤ y) :
    T.quotientValue hadd hsqrt x.1 ≤ T.quotientValue hadd hsqrt y.1 := by
  obtain ⟨u,hu⟩ := T.exists_positive_quotient_representative hadd x
  obtain ⟨v,hv⟩ := T.exists_positive_quotient_representative hadd ⟨y.1-x.1,sub_nonneg.mpr hxy⟩
  have hv' : T.cauchyQuotientMap hadd v.1 = y.1-x.1 := hv
  have hs : T.cauchyQuotientMap hadd (u.1+v.1) = y.1 := by
    calc
      _ = T.cauchyQuotientMap hadd u.1+T.cauchyQuotientMap hadd v.1 :=
        (T.cauchyQuotientMap hadd).map_add u.1 v.1
      _ = y.1 := by rw [hu,hv']; abel
  rw [← hu,← hs,T.quotientValue_map,T.quotientValue_map]
  exact T.cauchyValue_positive_mono hadd hsqrt
    (u := u) (v := Positive.add u v) (by change u.1 ≤ u.1+v.1; exact le_add_of_nonneg_right v.2)
end CuntzPureness.PositiveQuasitrace

end

end OAI
