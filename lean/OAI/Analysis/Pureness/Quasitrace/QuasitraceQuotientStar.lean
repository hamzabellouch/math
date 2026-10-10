import OAI.Analysis.Pureness.Quasitrace.QuasitraceNullIdeal

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)

lemma nullSequenceIdeal_rel (u v : T.cauchySequenceAlgebra hadd) :
    (T.nullSequenceIdeal hadd).ringCon u v ↔ T.IsMetricNull (fun k => u.1 k-v.1 k) := by
  rw [TwoSidedIdeal.rel_iff,nullSequenceIdeal_mem]
  rfl

lemma nullSequenceIdeal_rel_star (u v : T.cauchySequenceAlgebra hadd)
    (huv : (T.nullSequenceIdeal hadd).ringCon u v) :
    (T.nullSequenceIdeal hadd).ringCon (star u) (star v) := by
  rw [T.nullSequenceIdeal_rel hadd] at huv ⊢
  have h := T.isMetricNull_star huv
  simpa [IsMetricNull,star_sub] using h

instance cauchyQuotientStar : Star (T.CauchyQuotient hadd) where
  star := Quotient.map' star (T.nullSequenceIdeal_rel_star hadd)

lemma cauchyQuotientMap_star (u : T.cauchySequenceAlgebra hadd) :
    T.cauchyQuotientMap hadd (star u) = star (T.cauchyQuotientMap hadd u) := rfl

instance cauchyQuotientStarRing : StarRing (T.CauchyQuotient hadd) where
  star_involutive x := by
    obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective hadd x
    rw [← T.cauchyQuotientMap_star,← T.cauchyQuotientMap_star,star_star]
  star_mul x y := by
    obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective hadd x
    obtain ⟨v,rfl⟩ := T.cauchyQuotientMap_surjective hadd y
    rw [← map_mul,← T.cauchyQuotientMap_star,star_mul,map_mul,
      T.cauchyQuotientMap_star,T.cauchyQuotientMap_star]
  star_add x y := by
    obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective hadd x
    obtain ⟨v,rfl⟩ := T.cauchyQuotientMap_surjective hadd y
    rw [← map_add,← T.cauchyQuotientMap_star,star_add,map_add,
      T.cauchyQuotientMap_star,T.cauchyQuotientMap_star]

instance cauchyQuotientStarModule : StarModule ℂ (T.CauchyQuotient hadd) where
  star_smul c x := by
    obtain ⟨u,rfl⟩ := T.cauchyQuotientMap_surjective hadd x
    rw [← _root_.map_smul,← T.cauchyQuotientMap_star,star_smul,_root_.map_smul,T.cauchyQuotientMap_star]
end CuntzPureness.PositiveQuasitrace

end

end OAI
