import OAI.Probability.SpanningForest.Definitions
import OAI.Probability.SpanningForest.BinaryLawUnique

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal Topology

namespace Problem336

def configurationCylinder (A B : Finset EdgeCode) : Set EdgeConfiguration :=
  {x | (∀ e ∈ A, x e = true) ∧ (∀ e ∈ B, x e = false)}

theorem measurableSet_configurationCylinder (A B : Finset EdgeCode) :
    MeasurableSet (configurationCylinder A B) := by
  unfold configurationCylinder
  convert (A.measurableSet_biInter fun e _ =>
    (measurable_pi_apply e) (measurableSet_singleton true)).inter
    (B.measurableSet_biInter fun e _ =>
    (measurable_pi_apply e) (measurableSet_singleton false)) using 1
  ext x
  simp

theorem HasFUSFLaw.cylinder_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {G : GraphCode} {P : Measure Ω} {Q : Measure Ω'}
    {X : Ω → EdgeConfiguration} {Y : Ω' → EdgeConfiguration}
    (hX : HasFUSFLaw G P X) (hY : HasFUSFLaw G Q Y)
    {H : ℕ → FiniteSubgraphCode} (hH : IsConnectedExhaustion G H)
    (A B : Finset EdgeCode) :
    P (X ⁻¹' configurationCylinder A B) = Q (Y ⁻¹' configurationCylinder A B) := by
  exact tendsto_nhds_unique (hX.2 H hH A B) (hY.2 H hH A B)

theorem configurationMeasure_ext {μ ν : Measure EdgeConfiguration} [IsFiniteMeasure μ]
    (h : ∀ A B : Finset EdgeCode,
      μ (configurationCylinder A B) = ν (configurationCylinder A B)) : μ = ν :=
  BinaryLaw.measure_ext_of_signed_cylinders h

theorem HasFUSFLaw.map_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {G : GraphCode} {P : Measure Ω} {Q : Measure Ω'} [IsFiniteMeasure P]
    {X : Ω → EdgeConfiguration} {Y : Ω' → EdgeConfiguration}
    (hX : HasFUSFLaw G P X) (hY : HasFUSFLaw G Q Y)
    {H : ℕ → FiniteSubgraphCode} (hH : IsConnectedExhaustion G H) :
    P.map X = Q.map Y := by
  apply configurationMeasure_ext
  intro A B
  rw [Measure.map_apply (Measurable.of_eval hX.1) (measurableSet_configurationCylinder A B),
    Measure.map_apply (Measurable.of_eval hY.1) (measurableSet_configurationCylinder A B)]
  exact hX.cylinder_eq hY hH A B

end Problem336

end

end OAI
