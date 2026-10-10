import Mathlib
import OAI.Probability.Ballisticity.Estimates.SurvivingLane

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
namespace DirectionalTransience

theorem shared_conditioned_contact_bound {d : ℕ} (ν : Measure (Row d))
    (ℓ : Vector d) (x y : Lattice d) (hxy : dot (realPosition x) ℓ = dot (realPosition y) ℓ)
    (T A B : Set (Lattice d)) (hAB : Disjoint A B) :
    let U := {z | dot (realPosition x) ℓ ≤ dot (realPosition z) ℓ}
    sharedConditionedPairLaw ν ℓ x y (PrefixContact (U \ T)) ≤
      2 * (sharedConditionedPairLaw ν ℓ x y (Prod.fst ⁻¹' (SurvivingLane U T A)ᶜ) +
        sharedConditionedPairLaw ν ℓ x y (Prod.snd ⁻¹' (SurvivingLane U T B)ᶜ)) := by
  let U := {z | dot (realPosition x) ℓ ≤ dot (realPosition z) ℓ}
  have hx : NoDrop ℓ x = Stay U := rfl
  have hy : NoDrop ℓ y = Stay U := by unfold NoDrop Stay U; rw [← hxy]; rfl
  have hA := measurableSet_survivingLane U T A
  have hB := measurableSet_survivingLane U T B
  change _ ≤ 2*(_+_)
  rw [sharedConditionedPairLaw,Measure.smul_apply,Measure.restrict_apply (measurableSet_prefixContact _)]
  rw [Measure.smul_apply,Measure.restrict_apply (hA.compl.preimage measurable_fst),
    Measure.smul_apply,Measure.restrict_apply (hB.compl.preimage measurable_snd),hx,hy]
  have heA : Prod.fst ⁻¹' (SurvivingLane U T A)ᶜ ∩ (Stay U ×ˢ Stay U) =
      (Stay U \ SurvivingLane U T A) ×ˢ Stay U := by ext Z; change (¬_ ∧ _ ∧ _) ↔ ((_ ∧ ¬_) ∧ _); tauto
  have heB : Prod.snd ⁻¹' (SurvivingLane U T B)ᶜ ∩ (Stay U ×ˢ Stay U) =
      Stay U ×ˢ (Stay U \ SurvivingLane U T B) := by ext Z; change (¬_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ ¬_); tauto
  rw [heA,heB]
  simp only [smul_eq_mul]
  calc
    _ ≤ (sharedNoDropMass ν ℓ x y)⁻¹ * (2*(sharedPairLaw ν x y
        ((Stay U \ SurvivingLane U T A) ×ˢ Stay U) + sharedPairLaw ν x y
        (Stay U ×ˢ (Stay U \ SurvivingLane U T B)))) :=
      mul_le_mul_right (shared_pair_contact_bound ν x y U T A B hAB) _
    _ = _ := by ring

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
