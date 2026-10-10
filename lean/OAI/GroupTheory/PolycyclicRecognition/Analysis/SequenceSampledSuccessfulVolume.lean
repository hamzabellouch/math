import OAI.GroupTheory.PolycyclicRecognition.Analysis.SampledSuccessfulVolume
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceUniformInterval

namespace OAI

/-! # Successful parameter volume along the profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem exists_sampled_success_volume_sequence {G : Type*} [Group G] [MeasurableSpace G]
    {R : ℝ} (hR : 0 < R) (m : ℕ)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (f : ℕ → ℕ → ℝ → G) (σ : ℕ → ℕ → Measure G)
    [∀ r j, IsProbabilityMeasure (σ r j)]
    (hf : ∀ r j, MeasurePreserving (f r j) (uniformIntervalLaw R) (σ r j))
    (x : ℕ → G) (A : ℕ → Set G) (E : ℕ → Set (SwitchParameters G m))
    (hE : ∀ r, MeasurableSet (E r))
    (hprob : HasSubexponentialLowerBoundSeq scale (fun r => (switchParameterLaw (σ r) 0 m (E r)).toReal))
    (hsuccess : ∀ r p, p ∈ E r → SwitchSuccessful (fun _ => A r) 0 m (x r) p) :
    ∃ F : ℕ → Set (Fin (m + m) → ℝ),
      (∀ r, MeasurableSet (F r)) ∧ (∀ r, F r ⊆ closedBall 0 R) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (F r)).toReal) ∧
      ∀ r t, t ∈ F r → SwitchSuccessful (fun _ => A r) 0 m (x r)
        (sampledSwitchParameters (f r) m t) := by
  let _ := uniformIntervalLaw_isProbability hR
  let F := fun r => sampledSwitchParameters (f r) m ⁻¹' E r ∩ closedBall 0 R
  have hmap (r : ℕ) := measurePreserving_sampledSwitchParameters (f r)
    (uniformIntervalLaw R) (σ r) (hf r) m
  have hvol (r : ℕ) : Measure.pi (fun _ : Fin (m + m) => uniformIntervalLaw R) (F r) =
      switchParameterLaw (σ r) 0 m (E r) := by
    change Measure.pi _ (_ ∩ _) = _
    rw [measure_inter_conull (show Measure.pi (fun _ : Fin (m + m) => uniformIntervalLaw R)
        (closedBall (0 : Fin (m + m) → ℝ) R)ᶜ = 0 from
      mem_ae_iff.mp (uniformIntervalLaw_pi_ae_mem hR (m + m)))]
    exact (hmap r).measure_preimage (hE r).nullMeasurableSet
  refine ⟨F, fun r => ((hE r).preimage (hmap r).measurable).inter measurableSet_closedBall,
    fun _ => inter_subset_right, ?_, ?_⟩
  · apply subexponential_volume_of_uniform_samples_sequence scale hscale hR (m + m) F (fun _ => inter_subset_right)
    simpa only [hvol] using hprob
  · intro r t ht
    exact hsuccess r _ ht.1

end PolycyclicRecognition

end

end OAI
