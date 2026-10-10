import Mathlib
import OAI.Probability.Ballisticity.Estimates.LocalStoppedSplice
import OAI.Probability.Ballisticity.Entropy.WindowProjectionEntropy
import OAI.Probability.Ballisticity.Entropy.AnchorEntropy
import OAI.Probability.Ballisticity.Estimates.SamplingRearrangement
import OAI.Probability.Ballisticity.Entropy.StoppedEntropySum

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

abbrev RawCurrentData {d : ℕ} (e : Direction d) :=
  ℕ × (Environment d × (ℕ → HorizontalSpace e))

noncomputable def rawCurrentWindow {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) (Q : Measure (Environment d))
    (τ σ : Environment d → ℕ) (hτ : Measurable τ) (filler : Environment d) :
    Measure (RawCurrentData e × LocalUpperField e) :=
  (((Q.compProd (currentAnchorKernel e τ hτ)).prod
    (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν))).map
    (fun p => ((τ p.1.1,
      (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler p.1.1,p.1.2)),
      localStoppedField e τ σ (p.1.1,p.2))))

lemma sampled_stoppedWindow_law {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω ≤ σ ω)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    let G := stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler
    let K := currentAnchorKernel e τ (measurable_of_stop_events _ τ hτ)
    (((Q.compProd K).prod (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν))).map
      (fun p => ((G p.1.1,p.1.2),localStoppedField e τ σ (p.1.1,p.2)))) =
      (((Kernel.id.prod K) ∥ₖ Kernel.id) ∘ₘ stoppedWindowLaw e ν Q τ σ filler) := by
  let S : ℕ → Set (Lattice d) := fun n => BelowHeight (realPosition (step e)) n
  let G := stoppedObservation S τ filler
  let K := currentAnchorKernel e τ (measurable_of_stop_events S τ hτ)
  have hG := stoppedObservation_measurable S τ hτ filler
  have hK : K.comap G hG = K := by
    ext ω : 1
    exact currentAnchorKernel_observation e τ hτ filler ω
  have h := StoppedWindow.sample_lower_map Q
    (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν)) G hG
    (localStoppedField e τ σ)
    (localStoppedField_measurable e τ σ (measurable_of_stop_events S τ hτ)
      (measurable_of_stop_events S σ hσ)) K
  rw [hK, localStoppedField_law e ν Q τ σ hτσ hτ hσ filler] at h
  exact h

lemma rawCurrentWindow_measurable {d : ℕ} (e : Direction d)
    (τ σ : Environment d → ℕ)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    Measurable (fun p : (Environment d × (ℕ → HorizontalSpace e)) × LocalUpperField e =>
      ((τ p.1.1,(stoppedObservation (fun n => BelowHeight (realPosition (step e)) n)
        τ filler p.1.1,p.1.2)),localStoppedField e τ σ (p.1.1,p.2))) := by
  let S : ℕ → Set (Lattice d) := fun n => BelowHeight (realPosition (step e)) n
  have hw : Measurable (fun p : (Environment d × (ℕ → HorizontalSpace e)) × LocalUpperField e => p.1.1) :=
    measurable_fst.comp measurable_fst
  exact ((measurable_of_stop_events S τ hτ).comp hw).prodMk
    (((stoppedObservation_measurable S τ hτ filler).comp hw).prodMk
      (measurable_snd.comp measurable_fst)) |>.prodMk
      ((localStoppedField_measurable e τ σ (measurable_of_stop_events S τ hτ)
        (measurable_of_stop_events S σ hσ)).comp (hw.prodMk measurable_snd))

theorem rawCurrentWindow_kl_le {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω ≤ σ ω)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    let μ := rawCurrentWindow e ν Q τ σ (measurable_of_stop_events _ τ hτ) filler
    klDiv μ (μ.fst.prod (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν))) ≤
      ownedWindowEntropy e ν Q τ σ filler := by
  let S : ℕ → Set (Lattice d) := fun n => BelowHeight (realPosition (step e)) n
  let G := stoppedObservation S τ filler
  let K := currentAnchorKernel e τ (measurable_of_stop_events S τ hτ)
  let π := Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν)
  let μ := stoppedWindowLaw e ν Q τ σ filler
  let μ' : Measure ((Environment d × (ℕ → HorizontalSpace e)) × LocalUpperField e) :=
    (((Kernel.id.prod K) ∥ₖ (Kernel.id : Kernel (LocalUpperField e) (LocalUpperField e))) ∘ₘ μ)
  have : IsFiniteMeasure μ := by unfold μ stoppedWindowLaw; infer_instance
  have : IsFiniteMeasure μ' := by unfold μ'; infer_instance
  let dat : Environment d × (ℕ → HorizontalSpace e) → RawCurrentData e := fun p => (τ p.1,p)
  have hdat : Measurable dat := ((measurable_of_stop_events S τ hτ).comp measurable_fst).prodMk measurable_id
  have hproj := klDiv_map_le μ' (μ'.fst.prod π) (hdat.prodMap measurable_id)
  have hfst := StoppedWindow.map_data_field_fst μ' dat hdat
    (fun (_ : Environment d × (ℕ → HorizontalSpace e)) (ξ : LocalUpperField e) => ξ) measurable_snd
  change (μ'.map (Prod.map dat id)).fst = μ'.fst.map dat at hfst
  have hout : μ'.map (Prod.map dat id) =
      rawCurrentWindow e ν Q τ σ (measurable_of_stop_events S τ hτ) filler := by
    dsimp only [μ', μ, K]
    rw [← sampled_stoppedWindow_law e ν Q τ σ hτσ hτ hσ filler]
    rw [Measure.map_map (hdat.prodMap measurable_id)]
    · congr 1
      funext p
      have ht : τ (G p.1.1) = τ p.1.1 := stoppedRowGraft_stop S τ hτ p.1.1 filler
      exact Prod.ext (Prod.ext ht rfl) rfl
    · exact (((stoppedObservation_measurable S τ hτ filler).comp
        (measurable_fst.comp measurable_fst)).prodMk (measurable_snd.comp measurable_fst)).prodMk
        ((localStoppedField_measurable e τ σ (measurable_of_stop_events S τ hτ)
          (measurable_of_stop_events S σ hσ)).comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have href : (μ'.fst.prod π).map (Prod.map dat id) =
      (μ'.map (Prod.map dat id)).fst.prod π := by
    rw [← Measure.map_prod_map _ _ hdat measurable_id, Measure.map_id]
    rw [hfst]
  rw [href, hout] at hproj
  refine hproj.trans ?_
  have h := StoppedWindow.parallel_lower_kl_le μ π (Kernel.id.prod K)
  rw [stoppedWindowLaw_fst e ν Q τ σ hτ hσ filler] at h
  exact h

end DirectionalTransience

end

end OAI
