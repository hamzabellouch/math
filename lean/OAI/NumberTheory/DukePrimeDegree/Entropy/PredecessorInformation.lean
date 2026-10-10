import OAI.NumberTheory.DukePrimeDegree.Entropy.PredecessorSymbols
import OAI.NumberTheory.DukePrimeDegree.Entropy.FiniteFactorInformation
import OAI.NumberTheory.DukePrimeDegree.Entropy.BilateralConditionalSupport
import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableBoundaryEntropy

namespace OAI

/-! # Integrable countable information from finite predecessor symbols -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem conditionalInformation_eq_of_fiber_equiv
    {Y S α β : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace S] [MeasurableEq S]
    [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (F : Y → S) (hF : Measurable F)
    (P : Y → α) (hP : Measurable P) (B : Y → β) (hB : Measurable B)
    (hequiv : ∀ x y, F x=F y → (P x=P y ↔ B x=B y)) :
    conditionalInformation μ P (MeasurableSpace.comap F inferInstance) =ᵐ[μ]
      conditionalInformation μ B (MeasurableSpace.comap F inferInstance) := by
  have hp (a : α) :
      (fun x => (condDistrib id F μ (F x)).real {y | P y=a}) =ᵐ[μ]
        μ[({y | P y=a}.indicator (fun _ => (1:ℝ))) |
          MeasurableSpace.comap F inferInstance] := by
    simpa only [Set.preimage_id] using condDistrib_ae_eq_condExp (μ := μ)
      (X := F) (Y := (id : Y → Y)) (s := {y | P y=a}) hF measurable_id
        (hP (measurableSet_singleton a))
  have hb (b : β) :
      (fun x => (condDistrib id F μ (F x)).real {y | B y=b}) =ᵐ[μ]
        μ[({y | B y=b}.indicator (fun _ => (1:ℝ))) |
          MeasurableSpace.comap F inferInstance] := by
    simpa only [Set.preimage_id] using condDistrib_ae_eq_condExp (μ := μ)
      (X := F) (Y := (id : Y → Y)) (s := {y | B y=b}) hF measurable_id
        (hB (measurableSet_singleton b))
  have hfib : ∀ᵐ x ∂μ, ∀ᵐ y ∂condDistrib id F μ (F x), F y=F x :=
    ae_of_ae_map hF.aemeasurable (ae_condDistrib_self_fiber μ F hF)
  filter_upwards [ae_all_iff.mpr hp,ae_all_iff.mpr hb,hfib] with x hxP hxB hxF
  unfold conditionalInformation
  rw [←hxP (P x),←hxB (B x)]
  have hm : (condDistrib id F μ (F x)) {y | P y=P x} =
      (condDistrib id F μ (F x)) {y | B y=B x} := by
    apply measure_congr
    filter_upwards [hxF] with y hy
    exact propext (hequiv y x hy)
  rw [show (condDistrib id F μ (F x)).real {y | P y=P x} =
      (condDistrib id F μ (F x)).real {y | B y=B x} from
        congrArg ENNReal.toReal hm]

theorem finite_predecessors_information_integrable
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (T : Y → Y) (hT : Measurable T) (Q : Y → ℕ) (hQ : Measurable Q)
    (hfinite : UniformFinitePredecessors T Q) :
    Integrable (conditionalInformation μ Q (MeasurableSpace.comap (Q ∘ T) inferInstance)) μ ∧
      ∃ M : ℕ, (∫ x, conditionalInformation μ Q
        (MeasurableSpace.comap (Q ∘ T) inferInstance) x ∂μ) ≤ Real.log (M+1) := by
  obtain ⟨M,B,decode,hB,href,hdecode⟩ :=
    exists_finite_predecessor_observation T hT Q hQ hfinite
  let F := Q ∘ T
  have hF : Measurable F := hQ.comp hT
  have heq := conditionalInformation_eq_of_fiber_equiv μ F hF Q hQ B hB
    (fun x y hxy => ⟨fun h => href x y h hxy,fun hb => by
      rw [←hdecode x,←hdecode y]
      change decode (F x) (B x)=decode (F y) (B y)
      rw [hxy,hb]⟩)
  have hI := conditionalInformation_fintype_integrable_integral
    (MeasurableSpace.comap F inferInstance) μ B hB hF.comap_le
  refine ⟨hI.1.congr heq.symm,M,?_⟩
  rw [integral_congr_ae heq,hI.2]
  have hle := conditional_countable_le_observationEntropy μ B
    (fun b => hB (measurableSet_singleton b)) F hF
  have hcard := finiteShannon_le_log_card
    (fun b => measureReal_nonneg (μ := μ) (s := {x | B x=b}))
    (observation_distribution_sum μ B (fun b => hB (measurableSet_singleton b)))
  change observationEntropy μ B ≤ _ at hcard
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] at hcard
  exact hle.trans hcard

end DukePrimeDegree

end

end OAI
