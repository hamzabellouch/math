import OAI.Probability.FreeIsing.Conditioning.NoisyBranchConditionalLaw
import OAI.Probability.FreeIsing.Posterior.ComponentObservationRegression
import OAI.Probability.FreeIsing.Posterior.StatisticTilt

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance componentPosteriorTiltMeasurableSingletonSpin : MeasurableSingletonClass IsingSpin :=
  ⟨fun _ => trivial⟩
local instance componentPosteriorTiltNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

theorem HasFreeIsingLaw.condDistrib_componentPosterior_root
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (c : Fin d) (a : IsingSpin) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    let q := selectedPosterior P F (componentIndexVertex (c := c))
      (RootedBroadcast.branchRoot c)
    condDistrib q (fun z => z.1 (RootedBroadcast.root d)) P a =
      linearSignalTilt (P.map q) id (spinSign a * theta) := by
  let := hμ.isProbabilityMeasure
  dsimp only
  apply condDistrib_statistic_eq_tilt_of_linear_posterior
    (selectedObservationField_le hF (componentIndexVertex (c := c)))
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst)
    stronglyMeasurable_condExp.measurable integrable_condExp
  · exact hμ.selectedPosterior_root_component h0 h1 ν hF c
  · exact hμ.planted_spin_event_mass (fun _ => ν) _

theorem HasFreeIsingLaw.map_cond_componentPosterior_root
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (c : Fin d) (a : IsingSpin) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    let q := selectedPosterior P F (componentIndexVertex (c := c))
      (RootedBroadcast.branchRoot c)
    (P[|{z | z.1 (RootedBroadcast.root d) = a}]).map q =
      linearSignalTilt (P.map q) id (spinSign a * theta) := by
  let := hμ.isProbabilityMeasure
  have h := hμ.condDistrib_componentPosterior_root h0 h1 ν hF c a
  dsimp only at h ⊢
  rw [condDistrib_eq_map_cond_fiber
    (μ := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (S := fun z => z.1 (RootedBroadcast.root d))
    (Y := selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      F (componentIndexVertex (c := c)) (RootedBroadcast.branchRoot c))
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst)
    (measurable_selectedPosterior _ hF _ _) a (by
      change (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
        {z | z.1 (RootedBroadcast.root d) = a} ≠ 0
      rw [hμ.planted_spin_event_mass]
      norm_num)] at h
  exact h

theorem HasFreeIsingLaw.condDistrib_childComponentPosterior_parent
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (c e : Fin d) (a : IsingSpin) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    let q := selectedPosterior P F (childComponentIndexVertex c e)
      (prefixFlip c (RootedBroadcast.branchRoot e))
    condDistrib q (fun z => z.1 (RootedBroadcast.branchRoot c)) P a =
      linearSignalTilt (P.map q) id (spinSign a * theta) := by
  let := hμ.isProbabilityMeasure
  dsimp only
  apply condDistrib_statistic_eq_tilt_of_linear_posterior
    (selectedObservationField_le hF (childComponentIndexVertex c e))
    ((measurable_pi_apply (RootedBroadcast.branchRoot c)).comp measurable_fst)
    stronglyMeasurable_condExp.measurable integrable_condExp
  · exact hμ.selectedPosterior_parent_childComponent h0 h1 ν hF c e
  · exact hμ.planted_spin_event_mass (fun _ => ν) _

end Problem367

end

end OAI
