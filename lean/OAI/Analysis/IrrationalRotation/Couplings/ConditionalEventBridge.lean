import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Independence.Basic

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Invariant233.ConditionalEventBridge

variable {Ω A B ι : Type*}
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
  [Countable ι]

theorem iCondIndepSet_preimage_of_condDistrib
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → A) (Y : Ω → B) (hX : Measurable X) (hY : Measurable Y)
    (s : ι → Set B) (hs : ∀ i, MeasurableSet (s i))
    (hind : ∀ᵐ x ∂μ.map X, iIndepSet s (condDistrib Y X μ x)) :
    iCondIndepSet (MeasurableSpace.comap X inferInstance) hX.comap_le
      (fun i => Y ⁻¹' s i) μ := by
  apply (iCondIndepSet_iff _ _ _ (fun i => hY (hs i)) μ).2
  intro S
  have hi : ∀ᵐ ω ∂μ, ∀ i,
      (condDistrib Y X μ (X ω)).real (s i) =
        (μ[(Y ⁻¹' s i).indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap X inferInstance]) ω :=
    ae_all_iff.mpr (fun i => condDistrib_ae_eq_condExp hX hY (hs i))
  have hinter := condDistrib_ae_eq_condExp (μ := μ) hX hY
    (MeasurableSet.biInter S.countable_toSet (fun i _ => hs i))
  have hind' := ae_of_ae_map hX.aemeasurable hind
  filter_upwards [hi, hinter, hind'] with ω hω hI hInd
  simp only [Set.preimage_iInter, Finset.mem_coe] at hI
  rw [← hI]
  have heq := congrArg ENNReal.toReal (hInd.meas_biInter S)
  simp only [ENNReal.toReal_prod] at heq
  change (condDistrib Y X μ (X ω)).real (⋂ i ∈ S, s i) = _ at heq
  rw [heq]
  simp only [Finset.prod_apply]
  exact Finset.prod_congr rfl (fun i _ => hω i)

end Invariant233.ConditionalEventBridge

end

end OAI
