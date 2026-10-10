import Mathlib
import OAI.Probability.Ballisticity.Estimates.SharedConditionedPairLawFst
import OAI.Probability.Ballisticity.Crossings.HitWord
import OAI.Probability.Ballisticity.Estimates.NormalizedRestrictionContact
import OAI.Probability.Ballisticity.Crossings.CrossTranslation

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma normalized_shared_restrict {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) (x y : Lattice d) :
    normalizedMeasure ((sharedPairLaw ν x y).restrict (NoDrop ℓ x ×ˢ NoDrop ℓ y)) =
      sharedConditionedPairLaw ν ℓ x y := by
  unfold normalizedMeasure sharedConditionedPairLaw
  rw [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,← sharedNoDropMass_eq]

lemma normalized_independent_restrict {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) :
    normalizedMeasure (((annealedFrom ν x).prod (annealedFrom ν y)).restrict
      (NoDrop ℓ x ×ˢ NoDrop ℓ y)) = (conditionedFrom ν ℓ x).prod (conditionedFrom ν ℓ y) := by
  unfold normalizedMeasure conditionedFrom
  rw [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,Measure.prod_prod,
    annealedFrom_noDrop,annealedFrom_noDrop,Measure.prod_smul_left,Measure.prod_smul_right,
    smul_smul,Measure.prod_restrict,ENNReal.mul_inv]
  · exact Or.inr (measure_ne_top _ _)
  · exact Or.inl (measure_ne_top _ _)

lemma hitWordsEvent_subset_hit {d : ℕ} (x y : Lattice d) (S T : Set (Lattice d))
    (E : Set (HitWord x S T × HitWord y S T)) :
    hitWordsEvent x y S T E ⊆ Hit S T ×ˢ Hit S T := by
  intro P hP
  obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hP
  obtain ⟨_,hcy⟩ := Set.mem_iUnion.mp hw
  exact ⟨Set.mem_iUnion.mpr ⟨w.1.val.length,hitWord_prefix x S T w.1 hcy.1⟩,
    Set.mem_iUnion.mpr ⟨w.2.val.length,hitWord_prefix y S T w.2 hcy.2⟩⟩

theorem conditioned_prefix_comparison {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (x y : Lattice d)
    (hxy : dot (realPosition x) ℓ = dot (realPosition y) ℓ) (H : ℝ)
    (E : Set (HitWord x (Strip ℓ x H) (Upper ℓ x H) × HitWord y (Strip ℓ x H) (Upper ℓ x H))) :
    sharedConditionedPairLaw ν ℓ x y (hitWordsEvent x y (Strip ℓ x H) (Upper ℓ x H) E) ≤
      ((conditionedFrom ν ℓ x).prod (conditionedFrom ν ℓ y))
        (hitWordsEvent x y (Strip ℓ x H) (Upper ℓ x H) E) +
      sharedConditionedPairLaw ν ℓ x y (PrefixContact (Strip ℓ x H)) +
      (sharedNoDropMass ν ℓ x y)⁻¹ *
        ((annealedLaw ν (NoDrop ℓ 0))^2-sharedNoDropMass ν ℓ x y +
          2*annealedLaw ν (Cross ℓ 0 H \ NoDrop ℓ 0)) := by
  have hs : Strip ℓ x H = Strip ℓ y H := by unfold Strip; rw [hxy]
  have ht : Upper ℓ x H = Upper ℓ y H := by unfold Upper; rw [hxy]
  have hsub : hitWordsEvent x y (Strip ℓ x H) (Upper ℓ x H) E ⊆ Cross ℓ x H ×ˢ Cross ℓ y H := by
    intro P hP
    have hh := hitWordsEvent_subset_hit x y _ _ E hP
    rw [cross_eq_hit,cross_eq_hit]
    exact ⟨hh.1,by simpa only [hs,ht] using hh.2⟩
  have hmass : ((annealedFrom ν x).prod (annealedFrom ν y)) (NoDrop ℓ x ×ˢ NoDrop ℓ y) =
      (annealedLaw ν (NoDrop ℓ 0))^2 := by
    rw [Measure.prod_prod,annealedFrom_noDrop,annealedFrom_noDrop,pow_two]
  have hh := normalized_restriction_contact_le (sharedPairLaw ν x y)
    ((annealedFrom ν x).prod (annealedFrom ν y))
    (NoDrop ℓ x ×ˢ NoDrop ℓ y) (PrefixContact (Strip ℓ x H))
    (hitWordsEvent x y (Strip ℓ x H) (Upper ℓ x H) E) (Cross ℓ x H ×ˢ Cross ℓ y H)
    (measurableSet_prefixContact _) (measurableSet_hitWordsEvent _ _ _ _ _) hsub
    (sharedNoDropMass ν ℓ x y)
    ((annealedLaw ν (NoDrop ℓ 0))^2-sharedNoDropMass ν ℓ x y)
    (2*annealedLaw ν (Cross ℓ 0 H \ NoDrop ℓ 0))
    (sharedNoDropMass_pos ν hue ℓ hℓ htrans x y)
    (le_of_eq (sharedNoDropMass_eq ν ℓ x y))
    (by rw [hmass,← sharedNoDropMass_eq]; exact le_add_tsub)
    (independent_cross_noDrop_error_bound ν ℓ x y H)
    (raw_prefix_off_contact_equal ν x y _ _ (disjoint_strip_upper ℓ x H) E)
  simpa only [normalized_shared_restrict,normalized_independent_restrict] using hh

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
