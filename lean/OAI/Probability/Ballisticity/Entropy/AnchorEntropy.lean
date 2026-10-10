import Mathlib
import OAI.Probability.Ballisticity.Stationary.ArrayMap
import OAI.Probability.Ballisticity.Estimates.TwoStopSplice

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace StoppedWindow
variable {A B F : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace F]

lemma parallel_lower_fst (μ : Measure (A × F)) [IsFiniteMeasure μ]
    (K : Kernel A B) [IsMarkovKernel K] :
    ((K ∥ₖ Kernel.id) ∘ₘ μ).fst = K ∘ₘ μ.fst := by
  ext s hs
  rw [Measure.fst_apply hs, Measure.bind_apply (measurable_fst hs) (Kernel.aemeasurable _),
    Measure.bind_apply hs K.aemeasurable, Measure.fst, lintegral_map (K.measurable_coe hs) measurable_fst]
  apply lintegral_congr
  intro p
  rw [Kernel.parallelComp_apply, Kernel.id_apply]
  rw [← Measure.map_apply measurable_fst hs, Measure.map_fst_prod, measure_univ, one_smul]

theorem parallel_lower_kl_le (μ : Measure (A × F)) [IsFiniteMeasure μ]
    (π : Measure F) [IsProbabilityMeasure π]
    (K : Kernel A B) [IsMarkovKernel K] :
    let out := (K ∥ₖ Kernel.id) ∘ₘ μ
    klDiv out (out.fst.prod π) ≤ klDiv μ (μ.fst.prod π) := by
  have h := klDiv_comp_right_le μ (μ.fst.prod π) (K ∥ₖ Kernel.id)
  rw [← Measure.prod_comp_left, ← parallel_lower_fst μ K] at h
  exact h

end StoppedWindow

noncomputable def currentStoppedProfile {d : ℕ} (e : Direction d)
    (τ : Environment d → ℕ) (ω : Environment d) : Measure (HorizontalSpace e) :=
  globalHorizontalProfile e (τ ω) ω

instance currentStoppedProfile_probability {d : ℕ} (e : Direction d)
    (τ : Environment d → ℕ) (ω : Environment d) :
    IsProbabilityMeasure (currentStoppedProfile e τ ω) := by
  unfold currentStoppedProfile
  infer_instance

lemma currentStoppedProfile_measurable {d : ℕ} (e : Direction d)
    (τ : Environment d → ℕ) (hτ : Measurable τ) :
    Measurable (currentStoppedProfile e τ) := by
  change Measurable (fun ω : Environment d => globalHorizontalProfile e (τ ω) ω)
  have h := (globalHorizontalProfile_joint_measurable e).comp (measurable_id.prodMk hτ)
  simpa only [Function.comp_def,id_eq] using h

lemma currentStoppedProfile_observable {d : ℕ} (e : Direction d)
    (τ : Environment d → ℕ)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (B : Set (Measure (HorizontalSpace e))) (hB : MeasurableSet B) :
    StoppedRowsEvent (fun n => BelowHeight (realPosition (step e)) n) τ
      (currentStoppedProfile e τ ⁻¹' B) := by
  intro n
  have he : (currentStoppedProfile e τ ⁻¹' B) ∩ {ω | τ ω=n} =
      (globalHorizontalProfile e n ⁻¹' B) ∩ {ω | τ ω=n} := by
    ext ω
    simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_ofPred_eq]
    constructor <;> rintro ⟨hb,hn⟩ <;> exact ⟨by simpa only [currentStoppedProfile,hn] using hb,hn⟩
  rw [he]
  exact (hB.preimage (globalHorizontalProfile_measurable_below e n)).inter (hτ n)

lemma currentStoppedProfile_observation {d : ℕ} (e : Direction d)
    (τ : Environment d → ℕ)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (filler ω : Environment d) :
    currentStoppedProfile e τ
      (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler ω) =
      currentStoppedProfile e τ ω := by
  ext s hs
  apply stoppedRowGraft_observable _ τ hτ
    (fun ω => currentStoppedProfile e τ ω s)
  intro B hB
  exact currentStoppedProfile_observable e τ hτ _
    (hB.preimage (Measure.measurable_coe hs))

noncomputable def currentAnchorKernel {d : ℕ} (e : Direction d)
    (τ : Environment d → ℕ) (hτ : Measurable τ) :
    Kernel (Environment d) (ℕ → HorizontalSpace e) where
  toFun ω := Measure.infinitePi (fun _ => currentStoppedProfile e τ ω)
  measurable' := AnchorSampling.measurable_infinitePi _
    (fun _ => currentStoppedProfile_measurable e τ hτ)

instance currentAnchorKernel_markov {d : ℕ} (e : Direction d)
    (τ : Environment d → ℕ) (hτ : Measurable τ) :
    IsMarkovKernel (currentAnchorKernel e τ hτ) where
  isProbabilityMeasure ω := by
    change IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => currentStoppedProfile e τ ω))
    infer_instance

lemma currentAnchorKernel_observation {d : ℕ} (e : Direction d)
    (τ : Environment d → ℕ)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (filler ω : Environment d) :
    currentAnchorKernel e τ (measurable_of_stop_events _ τ hτ)
      (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler ω) =
    currentAnchorKernel e τ (measurable_of_stop_events _ τ hτ) ω := by
  change Measure.infinitePi _ = Measure.infinitePi _
  congr 1
  funext a
  exact currentStoppedProfile_observation e τ hτ filler ω

lemma globalEpisodeAnchors_current {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (ω : Environment d) (i : ℤ) :
    ((globalEpisodeAnchors e t ht) ω).map (fun U a => U (i,a)) =
      currentAnchorKernel e (fun ω => t ω i) (ht i) ω := by
  exact Measure.map_infinitePi_infinitePi_of_inj (fun a b h => by exact (Prod.mk.inj h).2)

end DirectionalTransience

end

end OAI
