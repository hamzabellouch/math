import OAI.MeasureTheory.Falconer.Recursion.DescriptorMasks

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

@[fun_prop] theorem measurable_pairRadialUnit :
    Measurable (fun z : Plane × Plane => sourceRadialUnit z.2 z.1) := by
  apply Measurable.subtype_mk
  change Measurable (fun z : Plane × Plane => sourceRadialVector z.2 z.1)
  unfold sourceRadialVector
  exact Measurable.ite (isClosed_eq continuous_fst continuous_snd).measurableSet
    measurable_const (by fun_prop)

noncomputable def endpointDescriptorGood (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (d : PolicyDescriptor) : Set (Plane × UnitCircle) :=
  {z | ∀ P ∈ dyadicPaths (descriptorAnchor d),
    z.1 ∈ (Q.descendant P).carrier →
    z.2 ∈ descriptorGoodSet Q ρ m N lam sig J i P d}

theorem measurable_endpointDescriptorGood (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (d : PolicyDescriptor) :
    MeasurableSet (endpointDescriptorGood Q ρ m N lam sig J i d) := by
  simp only [endpointDescriptorGood, ofPred_forall]
  apply MeasurableSet.iInter
  intro P
  apply MeasurableSet.iInter
  intro _
  exact ((Q.descendant P).measurable.preimage measurable_fst).himp
    ((measurable_descriptorGoodSet Q ρ m N lam sig J i P d).preimage measurable_snd)

noncomputable def positiveDistanceGoodSet (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N q a t : ℕ) (lam sig : ℝ) (J i : ℕ) : Set (Plane × Plane) :=
  {z | ∀ d ∈ policyDescriptorList (fun n => m n-(n:ℝ)/(N:ℝ)) N q a t,
    (z.1, sourceRadialUnit z.2 z.1) ∈ endpointDescriptorGood Q ρ m N lam sig J i d ∧
    (z.2, sourceRadialUnit z.2 z.1) ∈ endpointDescriptorGood Q ρ m N lam sig J i d}

theorem measurable_positiveDistanceGoodSet (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N q a t : ℕ) (lam sig : ℝ) (J i : ℕ) :
    MeasurableSet (positiveDistanceGoodSet Q ρ m N q a t lam sig J i) := by
  simp only [positiveDistanceGoodSet, ofPred_forall]
  apply Finset.measurableSet_biInter
  intro d _
  exact ((measurable_endpointDescriptorGood Q ρ m N lam sig J i d).preimage
    (measurable_fst.prodMk measurable_pairRadialUnit)).inter
    ((measurable_endpointDescriptorGood Q ρ m N lam sig J i d).preimage
    (measurable_snd.prodMk measurable_pairRadialUnit))

end PlanarFalconer

end OAI
