import OAI.GroupTheory.PolycyclicRecognition.Analysis.UniformIntervalSamples

namespace OAI

/-! # The actual successful interval parameters have subexponential volume -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

def sampledSwitchParameters {G : Type*} (f : ℕ → ℝ → G) (m : ℕ)
    (t : Fin (m + m) → ℝ) : SwitchParameters G m :=
  mapSwitchParameters f 0 m (flatSwitchSamples m t)

theorem measurePreserving_sampledSwitchParameters {G : Type*} [MeasurableSpace G]
    (f : ℕ → ℝ → G) (τ : Measure ℝ) [IsProbabilityMeasure τ]
    (σ : ℕ → Measure G) [∀ j, IsProbabilityMeasure (σ j)]
    (hf : ∀ j, MeasurePreserving (f j) τ (σ j)) (m : ℕ) :
    MeasurePreserving (sampledSwitchParameters f m)
      (Measure.pi (fun _ => τ)) (switchParameterLaw σ 0 m) :=
  (measurePreserving_mapSwitchParameters f (fun _ => τ) σ hf 0 m).comp
    (measurePreserving_flatSwitchSamples τ 0 m)

/-- The compact cube is fixed before restricting to successful parameters. -/
theorem exists_sampled_success_volume {G : Type*} [Group G] [MeasurableSpace G]
    {R : ℝ} (hR : 0 < R) (m : ℕ)
    (f : ℝ → ℕ → ℝ → G) (σ : ℝ → ℕ → Measure G)
    [∀ r j, IsProbabilityMeasure (σ r j)]
    (hf : ∀ r j, MeasurePreserving (f r j) (uniformIntervalLaw R) (σ r j))
    (x : ℝ → G) (A : ℝ → Set G) (E : ℝ → Set (SwitchParameters G m))
    (hE : ∀ r, MeasurableSet (E r))
    (hprob : HasSubexponentialLowerBound (fun r => (switchParameterLaw (σ r) 0 m (E r)).toReal))
    (hsuccess : ∀ r p, p ∈ E r → SwitchSuccessful (fun _ => A r) 0 m (x r) p) :
    ∃ F : ℝ → Set (Fin (m + m) → ℝ),
      (∀ r, MeasurableSet (F r)) ∧ (∀ r, F r ⊆ closedBall 0 R) ∧
      HasSubexponentialLowerBound (fun r => (volume (F r)).toReal) ∧
      ∀ r t, t ∈ F r → SwitchSuccessful (fun _ => A r) 0 m (x r)
        (sampledSwitchParameters (f r) m t) := by
  let _ := uniformIntervalLaw_isProbability hR
  let F := fun r => sampledSwitchParameters (f r) m ⁻¹' E r ∩ closedBall 0 R
  have hmap (r : ℝ) := measurePreserving_sampledSwitchParameters (f r)
    (uniformIntervalLaw R) (σ r) (hf r) m
  have hvol (r : ℝ) : Measure.pi (fun _ : Fin (m + m) => uniformIntervalLaw R) (F r) =
      switchParameterLaw (σ r) 0 m (E r) := by
    change Measure.pi _ (_ ∩ _) = _
    rw [measure_inter_conull (show Measure.pi (fun _ : Fin (m + m) => uniformIntervalLaw R)
        (closedBall (0 : Fin (m + m) → ℝ) R)ᶜ = 0 from
      mem_ae_iff.mp (uniformIntervalLaw_pi_ae_mem hR (m + m)))]
    exact (hmap r).measure_preimage (hE r).nullMeasurableSet
  refine ⟨F, fun r => ((hE r).preimage (hmap r).measurable).inter measurableSet_closedBall,
    fun _ => inter_subset_right, ?_, ?_⟩
  · apply subexponential_volume_of_uniform_samples hR (m + m) F (fun _ => inter_subset_right)
    simpa only [hvol] using hprob
  · intro r t ht
    exact hsuccess r _ ht.1

end PolycyclicRecognition

end

end OAI
