import OAI.Probability.ContinuumTransition.GrandDomination

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem measurableSet_generalConfigurations {D : Set Space} (hD : MeasurableSet D)
    (ι : Type) [Fintype ι] : MeasurableSet {x : ι → Space | ∀ i, x i ∈ D} := by
  convert MeasurableSet.iInter (fun i : ι => hD.preimage
    (measurable_pi_apply i : Measurable (fun x : ι → Space => x i))) using 1
  ext x
  simp

theorem GrandFinite.of_le_on {F G : ConfigFamily} {D : Set Space} (hD : MeasurableSet D)
    (hG : GrandFinite G D) (hm : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (h0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hFG : ∀ (ι : Type) [Fintype ι] (x : ι → Space), (∀ i, x i ∈ D) → F ι x ≤ G ι x) :
    GrandFinite F D := by
  have hi (ι : Type) [Fintype ι] : IntegrableOn (F ι) {x | ∀ i, x i ∈ D} := by
    apply (hG.integrable ι).mono' (hm ι).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (measurableSet_generalConfigurations hD ι)] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (h0 ι x)] using hFG ι x hx
  refine ⟨fun ι _ => hi ι, ?_⟩
  apply Summable.of_nonneg_of_le (familyTerm_nonneg F D h0) _ hG.summable
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact setIntegral_mono_on (hi (Fin n)) (hG.integrable (Fin n))
    (measurableSet_generalConfigurations hD (Fin n)) (hFG (Fin n))

end ContinuumTemperature
end

end OAI
