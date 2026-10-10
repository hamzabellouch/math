import OAI.Probability.FreeIsing.Cavity.LogOdds
import OAI.Probability.FreeIsing.Estimates.ComponentFieldRecursion

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem367

local instance : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

theorem HasFreeIsingLaw.gaussian_component_field_sub_observation_le
    {d : ℕ} (hd : 2 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (c : Fin d) :
    let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s x => (t : ℝ) * spinSign s + x
    ∀ᵐ z ∂ρ,
      |Real.artanh (selectedPosterior ρ F (componentIndexVertex (c := c))
        (RootedBroadcast.branchRoot c) z) -
      PlantedSymmetry.observation t z (RootedBroadcast.branchRoot c)| ≤
        ((d - 1 : ℕ) : ℝ) * beta := by
  classical
  filter_upwards [hμ.gaussian_component_field_recursion hd hb t c] with z hz
  rw [hz, add_sub_cancel_left]
  have hcard : Fintype.card {a : Fin d // c ≠ a} = d - 1 := by
    simp [Fintype.card_subtype_compl]
  calc
    _ ≤ ∑ a : {a : Fin d // c ≠ a},
        |cavityMessage (Real.tanh beta)
          (Real.artanh (selectedPosterior
            (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
            (fun s x => (t : ℝ) * spinSign s + x) (childComponentIndexVertex c a.1)
            (prefixFlip c (RootedBroadcast.branchRoot a.1)) z))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : {a : Fin d // c ≠ a}, beta :=
      Finset.sum_le_sum (fun _ _ => abs_cavityMessage_tanh_le hb _)
    _ = ((d - 1 : ℕ) : ℝ) * beta := by simp [hcard]

theorem HasFreeIsingLaw.gaussian_component_field_recursion_cond_spin
    {d : ℕ} (hd : 2 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (c : Fin d) (s : IsingSpin) :
    let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun a x => (t : ℝ) * spinSign a + x
    ∀ᵐ z ∂cond ρ {z | z.1 (RootedBroadcast.branchRoot c) = s},
      Real.artanh (selectedPosterior ρ F (componentIndexVertex (c := c))
        (RootedBroadcast.branchRoot c) z) =
      (t : ℝ) * spinSign s + z.2 (RootedBroadcast.branchRoot c) +
        ∑ a : {a : Fin d // c ≠ a}, cavityMessage (Real.tanh beta)
          (Real.artanh (selectedPosterior ρ F (childComponentIndexVertex c a.1)
            (prefixFlip c (RootedBroadcast.branchRoot a.1)) z)) := by
  have hm : Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
      z.1 (RootedBroadcast.branchRoot c)) :=
    (measurable_pi_apply _).comp measurable_fst
  have hset : MeasurableSet {z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) |
      z.1 (RootedBroadcast.branchRoot c) = s} := hm (measurableSet_singleton s)
  filter_upwards [cond_absolutelyContinuous.ae_le
    (hμ.gaussian_component_field_recursion hd hb t c), ae_cond_mem hset] with z hz hs
  rw [hz]
  change z.1 (RootedBroadcast.branchRoot c) = s at hs
  simp only [PlantedSymmetry.observation, hs]

end Problem367

end

end OAI
