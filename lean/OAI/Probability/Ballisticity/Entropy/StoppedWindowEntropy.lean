import Mathlib
import OAI.Probability.Ballisticity.Estimates.TwoStopSplice

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace DirectionalTransience.StoppedWindow

variable {A B Z : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace Z] [StandardBorelSpace B] [Nonempty B]

noncomputable def ownLowerReference (Q P : Measure (A × B)) [IsFiniteMeasure P] :
    Measure (A × B) := Q.fst.compProd P.condKernel

theorem stopped_chain (Q P : Measure (A × B)) [IsFiniteMeasure Q] [IsFiniteMeasure P] :
    klDiv Q P = klDiv Q.fst P.fst + klDiv Q (ownLowerReference Q P) := by
  calc
    klDiv Q P = klDiv (Q.fst.compProd Q.condKernel) (P.fst.compProd P.condKernel) := by
      rw [Measure.disintegrate, Measure.disintegrate]
    _ = _ := by
      simpa only [Measure.disintegrate, ownLowerReference] using
        klDiv_compProd_eq_add Q.fst P.fst Q.condKernel P.condKernel

theorem stopped_kernel_increment (Q P : Measure (A × B)) [IsFiniteMeasure Q]
    [IsFiniteMeasure P] (K : Kernel (A × B) Z) [IsMarkovKernel K] :
    klDiv Q.fst P.fst +
      klDiv (K ∘ₘ Q) (K ∘ₘ ownLowerReference Q P) ≤ klDiv Q P := by
  have : IsFiniteMeasure (ownLowerReference Q P) := by
    unfold ownLowerReference
    infer_instance
  rw [stopped_chain Q P]
  exact add_le_add le_rfl (klDiv_comp_right_le Q (ownLowerReference Q P) K)

theorem fresh_prod_chain (Q : Measure (A × B)) [IsFiniteMeasure Q]
    (Pdata : Measure A) [IsFiniteMeasure Pdata]
    (Pfield : Measure B) [IsProbabilityMeasure Pfield] :
    klDiv Q (Pdata.prod Pfield) =
      klDiv Q.fst Pdata + klDiv Q (Q.fst.prod Pfield) := by
  have h := klDiv_compProd_eq_add Q.fst Pdata Q.condKernel (Kernel.const A Pfield)
  simpa only [Measure.disintegrate, Measure.compProd_const] using h

omit [StandardBorelSpace B] [Nonempty B] in
theorem same_auxiliary_cost (Q P : Measure A) [IsFiniteMeasure Q] [IsFiniteMeasure P]
    (R : Measure B) [IsProbabilityMeasure R] :
    klDiv (Q.prod R) (P.prod R) = klDiv Q P := by
  simpa only [Measure.compProd_const] using klDiv_compProd_left Q P (Kernel.const A R)

end DirectionalTransience.StoppedWindow

end

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def stoppedWindowOutput {d : ℕ} (e : Direction d)
    (τ σ : Environment d → ℕ) (filler : Environment d)
    (p : Environment d × Environment d) :
    Environment d × ((ℕ × HorizontalSpace e) → Row d) :=
  (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler p.1,
   upperField e (τ p.1)
    (stoppedRowGraft (fun n => BelowHeight (realPosition (step e)) n) σ p.1 p.2))

lemma stoppedWindowOutput_measurable {d : ℕ} (e : Direction d)
    (τ σ : Environment d → ℕ)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) : Measurable (stoppedWindowOutput e τ σ filler) := by
  let S : ℕ → Set (Lattice d) := fun n => BelowHeight (realPosition (step e)) n
  exact ((stoppedObservation_measurable S τ hτ filler).comp measurable_fst).prodMk
    ((upperField_joint_measurable e).comp
      ((stoppedRowGraft_measurable S σ (measurable_of_stop_events S σ hσ)).prodMk
        ((measurable_of_stop_events S τ hτ).comp measurable_fst)))

lemma stoppedWindowOutput_factor {d : ℕ} (e : Direction d)
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω≤σ ω)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    stoppedWindowOutput e τ σ filler ∘
      Prod.map (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) σ filler) id =
        stoppedWindowOutput e τ σ filler := by
  funext p
  let S : ℕ → Set (Lattice d) := fun n => BelowHeight (realPosition (step e)) n
  change (stoppedObservation S τ filler (stoppedRowGraft S σ p.1 filler),
    upperField e (τ (stoppedObservation S σ filler p.1))
      (stoppedRowGraft S σ (stoppedObservation S σ filler p.1) p.2)) = _
  rw [stoppedObservation_nested S (belowHeight_mono e) τ σ hτσ hτ hσ,
    stoppedObservation_nested_stop S (belowHeight_mono e) τ σ hτσ hτ hσ,
    stoppedObservation_regraft S σ hσ]
  rfl

noncomputable def stoppedWindowLaw {d : ℕ} (e : Direction d) (ν : Measure (Row d))
    (Q : Measure (Environment d)) (τ σ : Environment d → ℕ) (filler : Environment d) :=
  (Q.prod (environmentLaw ν)).map (stoppedWindowOutput e τ σ filler)

lemma stoppedWindowLaw_upper_observation {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω≤σ ω)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    stoppedWindowLaw e ν Q τ σ filler =
      ((Q.map (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) σ filler)).prod
        (environmentLaw ν)).map (stoppedWindowOutput e τ σ filler) := by
  let S : ℕ → Set (Lattice d) := fun n => BelowHeight (realPosition (step e)) n
  have hG := stoppedObservation_measurable S σ hσ filler
  have hp := Measure.map_prod_map Q (environmentLaw ν) hG measurable_id
  simp only [Measure.map_id] at hp
  rw [hp, Measure.map_map (stoppedWindowOutput_measurable e τ σ hτ hσ filler)
    (hG.prodMap measurable_id), stoppedWindowOutput_factor e τ σ hτσ hτ hσ filler]
  rfl

lemma stoppedWindowLaw_fst {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (τ σ : Environment d → ℕ)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    (stoppedWindowLaw e ν Q τ σ filler).fst =
      Q.map (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler) := by
  let G := stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler
  have hG : Measurable G := stoppedObservation_measurable _ τ hτ filler
  have hF : Measurable (fun p : Environment d × Environment d =>
      upperField e (τ p.1) (stoppedRowGraft
        (fun n => BelowHeight (realPosition (step e)) n) σ p.1 p.2)) :=
    measurable_snd.comp (stoppedWindowOutput_measurable e τ σ hτ hσ filler)
  change ((Q.prod (environmentLaw ν)).map (fun p => ((G ∘ Prod.fst) p, _))).fst = _
  rw [Measure.fst_map_prodMk (hG.comp measurable_fst) hF]
  rw [← Measure.map_map hG measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]

lemma stoppedWindowLaw_reference {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω≤σ ω)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    stoppedWindowLaw e ν (environmentLaw ν) τ σ filler =
      ((environmentLaw ν).map
        (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler)).prod
          (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν)) := by
  exact twoStopSplice_fresh e ν τ σ hτσ hτ hσ _
    (stoppedObservation_measurable _ τ hτ filler)
    (stoppedObservation_observable _ τ hτ filler)

theorem actual_stopped_window_entropy_increment {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (τ σ : Environment d → ℕ) (hτσ : ∀ ω, τ ω≤σ ω)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (hσ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | σ ω=n})
    (filler : Environment d) :
    let Gτ := stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler
    let Gσ := stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) σ filler
    klDiv (Q.map Gτ) ((environmentLaw ν).map Gτ) +
      klDiv (stoppedWindowLaw e ν Q τ σ filler)
        ((Q.map Gτ).prod (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν))) ≤
      klDiv (Q.map Gσ) ((environmentLaw ν).map Gσ) := by
  let : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  let Gσ := stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) σ filler
  have h := klDiv_map_le ((Q.map Gσ).prod (environmentLaw ν))
    (((environmentLaw ν).map Gσ).prod (environmentLaw ν))
    (stoppedWindowOutput_measurable e τ σ hτ hσ filler)
  rw [← stoppedWindowLaw_upper_observation e ν Q τ σ hτσ hτ hσ filler,
    ← stoppedWindowLaw_upper_observation e ν (environmentLaw ν) τ σ hτσ hτ hσ filler,
    stoppedWindowLaw_reference e ν τ σ hτσ hτ hσ filler,
    StoppedWindow.same_auxiliary_cost] at h
  have : IsFiniteMeasure (stoppedWindowLaw e ν Q τ σ filler) := by
    unfold stoppedWindowLaw
    infer_instance
  rw [StoppedWindow.fresh_prod_chain,
    stoppedWindowLaw_fst e ν Q τ σ hτ hσ filler] at h
  exact h

end DirectionalTransience

end

end OAI
