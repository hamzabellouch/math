import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Independence.Basic

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ProbabilityTheory

namespace Invariant233.ConditionalDistributionEvents

variable {ι Ω X Y : Type*} [Countable ι]
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]

theorem iCondIndepSet_preimage_of_condDistrib
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (observed : Ω → X) (value : Ω → Y)
    (hobserved : Measurable observed) (hvalue : Measurable value)
    (events : ι → Set Y) (hevents : ∀ i, MeasurableSet (events i))
    (hind : ∀ᵐ x ∂μ.map observed,
      iIndepSet events (condDistrib value observed μ x)) :
    iCondIndepSet (MeasurableSpace.comap observed inferInstance) hobserved.comap_le
      (fun i => value ⁻¹' events i) μ := by
  apply (iCondIndepSet_iff _ _ _ (fun i => hvalue (hevents i)) μ).mpr
  intro S
  have hi : MeasurableSet (⋂ i ∈ S, events i) :=
    MeasurableSet.biInter S.countable_toSet (fun i _ => hevents i)
  have hfull := ae_of_ae_map hobserved.aemeasurable hind
  have heach : ∀ᵐ ω ∂μ, ∀ i,
      (condDistrib value observed μ (observed ω)).real (events i) =
        (μ⟦value ⁻¹' events i | MeasurableSpace.comap observed inferInstance⟧) ω :=
    ae_all_iff.mpr (fun i => condDistrib_ae_eq_condExp hobserved hvalue (hevents i))
  filter_upwards [hfull, heach, condDistrib_ae_eq_condExp hobserved hvalue hi]
    with ω hω heach hinter
  have hprod := (iIndepSet_iff_meas_biInter hevents).mp hω S
  have hreal := congrArg ENNReal.toReal hprod
  simp only [ENNReal.toReal_prod] at hreal
  have hpre : value ⁻¹' (⋂ i ∈ S, events i) = ⋂ i ∈ S, value ⁻¹' events i := by
    ext z
    simp
  rw [hpre] at hinter
  simp only [Finset.prod_apply]
  rw [← hinter]
  change (condDistrib value observed μ (observed ω) (⋂ i ∈ S, events i)).toReal = _
  rw [hreal]
  exact Finset.prod_congr rfl (fun i _ => heach i)

theorem iCondIndepSet_coordinate_preimage_of_condDistrib
    {Z : ι → Type*} [∀ i, MeasurableSpace (Z i)]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (observed : Ω → X) (value : Ω → Y)
    (hobserved : Measurable observed) (hvalue : Measurable value)
    (coordinate : ∀ i, Y → Z i) (hcoordinate : ∀ i, Measurable (coordinate i))
    (events : ∀ i, Set (Z i)) (hevents : ∀ i, MeasurableSet (events i))
    (hind : ∀ᵐ x ∂μ.map observed,
      iIndepFun coordinate (condDistrib value observed μ x)) :
    iCondIndepSet (MeasurableSpace.comap observed inferInstance) hobserved.comap_le
      (fun i => (fun ω => coordinate i (value ω)) ⁻¹' events i) μ := by
  apply iCondIndepSet_preimage_of_condDistrib μ observed value hobserved hvalue
    (fun i => coordinate i ⁻¹' events i) (fun i => hcoordinate i (hevents i))
  filter_upwards [hind] with x hx
  apply (iIndepSet_iff_meas_biInter (fun i => hcoordinate i (hevents i))).mpr
  intro S
  exact hx.measure_inter_preimage_eq_mul S (fun i _ => hevents i)

end Invariant233.ConditionalDistributionEvents

end

end OAI
