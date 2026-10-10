import OAI.Probability.FreeIsing.Conditioning.PlantedInformation
import OAI.Probability.FreeIsing.Energy.Attenuation
import OAI.Probability.FreeIsing.Posterior.InfinitePosteriorField
import OAI.Probability.FreeIsing.Posterior.SelectedPosteriorSymmetry

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

open PlantedSymmetry

local instance componentInformationUpperNonemptyIsingSpin : Nonempty IsingSpin := ⟨.neg⟩

theorem singletonGibbsSpinMean_eq_tanh {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (v : TreeVertex d) (y : ({v} : Finset (TreeVertex d)) → ℝ) :
    FinitePosterior.fieldMean (finiteIsingEnergy beta {v})
      (fun (eta : ({v} : Finset (TreeVertex d)) → IsingSpin) w => spinSign (eta w))
      (fun eta => spinSign (eta ⟨v, by simp⟩)) y = Real.tanh (y ⟨v, by simp⟩) := by
  classical
  let r : ({v} : Finset (TreeVertex d)) := ⟨v, by simp⟩
  have hm := FinitePosterior.fieldMean_spin_mem_Ioo (finiteIsingEnergy beta {v})
    (fun (eta : ({v} : Finset (TreeVertex d)) → IsingSpin) w => spinSign (eta w))
    (fun eta => spinSign (eta r)) y
    (fun eta => by cases eta r <;> simp [spinSign])
    ⟨fun _ => .neg, rfl⟩ ⟨fun _ => .pos, rfl⟩
  have hfield := finite_tree_gibbs_field_bound {v} hb y r
  change |Real.artanh (FinitePosterior.fieldMean (finiteIsingEnergy beta {v})
    (fun eta w => spinSign (eta w)) (fun eta => spinSign (eta r)) y) - y r| ≤ _ at hfield
  simp only [inducedEdges_singleton, Finset.filter_empty, Finset.card_empty,
    Nat.cast_zero, zero_mul] at hfield
  have heq := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hfield (abs_nonneg _)))
  rw [← Real.tanh_artanh hm, heq]

theorem HasFreeIsingLaw.selected_singleton_gaussian_posterior
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    selectedPosterior (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
      (fun s z => (t : ℝ) * spinSign s + z) (fun _ : Unit => v) v =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => Real.tanh (observation t p v) := by
  classical
  have hfield : MeasurableSpace.comap (finiteObservation {v} t) inferInstance =
      selectedObservationField (fun s z => (t : ℝ) * spinSign s + z)
        (fun _ : Unit => v) := by
    change selectedObservationField (fun s z => (t : ℝ) * spinSign s + z)
      (fun w : ({v} : Finset (TreeVertex d)) => w.1) = _
    apply selectedObservationField_eq_of_range_eq
    ext w
    simp
  have hce := hμ.finiteObservation_condExp {v} (connectedFinset_singleton v) t
    (fun eta => spinSign (eta ⟨v, by simp⟩))
  rw [hfield] at hce
  filter_upwards [hce] with p hp
  change selectedPosterior _ _ _ _ p = _ at hp
  rw [hp, singletonGibbsSpinMean_eq_tanh hb]
  rfl

theorem gaussian_observation_second_moment {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (t : ℝ≥0) (v : TreeVertex d) :
    (∫ p, (observation t p v) ^ 2 ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) =
      (t : ℝ) + (t : ℝ) ^ 2 := by
  let ρ := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
  have hS : MemLp (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
      spinSign (p.1 v)) 2 ρ :=
    (PlantedInformation.spinSign_memLp μ v).comp_measurePreserving measurePreserving_fst
  have hB := centered_gaussian_moments (PlantedInformation.noise_hasLaw μ t v)
  have hind := PlantedInformation.spin_noise_indep μ t v v
  have h := integral_observation_mul_observation hS hS hB.1 hB.1 hind hind
    hB.2.1 hB.2.1 (t : ℝ)
  have hspin : (∫ p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ),
      spinSign (p.1 v) * spinSign (p.1 v) ∂ρ) = 1 := by
    have heq : (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        spinSign (p.1 v) * spinSign (p.1 v)) = fun _ => (1 : ℝ) := by
      funext p
      cases p.1 v <;> norm_num [spinSign]
    rw [heq]
    simp [ρ]
  rw [hspin] at h
  simp only [← pow_two] at h
  rw [hB.2.2] at h
  simpa only [observation, pow_two, mul_one, add_comm] using h

theorem HasFreeIsingLaw.selected_singleton_information_le
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    (∫ p, (selectedPosterior (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
      (fun s z => (t : ℝ) * spinSign s + z) (fun _ : Unit => v) v p) ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤ (t : ℝ) + (t : ℝ) ^ 2 := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let ρ := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
  have hF : Measurable (Function.uncurry
      (fun (s : IsingSpin) (z : ℝ) => (t : ℝ) * spinSign s + z)) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul _).add measurable_snd
  have hpost := integrable_selectedPosterior_abs_pow ρ hF (fun _ : Unit => v) v 2
  simp only [sq_abs] at hpost
  have hS := (PlantedInformation.spinSign_memLp μ v).comp_measurePreserving
    (measurePreserving_fst (ν := gaussianNoiseLaw (TreeVertex d) t))
  have hB := (centered_gaussian_moments (PlantedInformation.noise_hasLaw μ t v)).1
  have hobs : Integrable (fun p => (observation t p v) ^ 2) ρ :=
    ((hS.const_mul (t : ℝ)).add hB).integrable_sq
  rw [← gaussian_observation_second_moment μ t v]
  apply integral_mono_ae hpost hobs
  filter_upwards [hμ.selected_singleton_gaussian_posterior hb t v] with p hp
  rw [hp]
  have hbound := abs_tanh_le_abs_response (observation t p v)
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hbound 2

end Problem367

end

end OAI
