import Mathlib
import OAI.Probability.Ballisticity.Estimates.AnchorFrameReference
import OAI.Probability.Ballisticity.Geometry.RawWindow
import OAI.Probability.Ballisticity.Estimates.InputMarginal

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience

abbrev CurrentProfiles {d : ℕ} (e : Direction d) :=
  (ℕ × HorizontalSpace e) → Set.Icc (0 : ℝ) 1

abbrev CurrentWindow {d : ℕ} (e : Direction d) :=
  (ReferenceClasses.Data (HorizontalSpace e) × CurrentProfiles e) ×
    ReferenceClasses.AllFields (HorizontalSpace e) (Row d)

noncomputable def rawCurrentProfiles {d : ℕ} (e : Direction d)
    (z : RawCurrentData e) : CurrentProfiles e :=
  fun p => globalHorizontalCoordinate e z.1 z.2.1 (z.2.2 p.1 + p.2)

lemma rawCurrentProfileCoordinate_measurable {d : ℕ} (e : Direction d)
    (a : ℕ) (z : HorizontalSpace e) :
    Measurable (fun p : RawCurrentData e => globalHorizontalCoordinate e p.1 p.2.1 (p.2.2 a+z)) := by
  have hw : Measurable (fun p : RawCurrentData e => p.2.1) := measurable_fst.comp measurable_snd
  have hn : Measurable (fun p : RawCurrentData e => p.1) := measurable_fst
  have hu : Measurable (fun p : RawCurrentData e => p.2.2 a) :=
    (measurable_pi_apply a).comp (measurable_snd.comp measurable_snd)
  have ha : Measurable (fun p : RawCurrentData e => ((p.2.1,p.1),p.2.2 a+z)) :=
    (hw.prodMk hn).prodMk (hu.add_const z)
  have hm := (globalHorizontalCoordinate_joint_measurable e).comp ha
  simpa only [Function.comp_def] using hm

lemma rawCurrentProfiles_measurable {d : ℕ} (e : Direction d) :
    Measurable (rawCurrentProfiles e) :=
  Measurable.of_eval fun p => rawCurrentProfileCoordinate_measurable e p.1 p.2

noncomputable def rawCurrentProjection {d : ℕ} (e : Direction d)
    (p : RawCurrentData e × LocalUpperField e) : CurrentWindow e :=
  ((ReferenceClasses.anchorOffsets p.1.2.2,rawCurrentProfiles e p.1),
    ReferenceClasses.anchorFields p.1.2.2 p.2)

lemma rawCurrentProjection_measurable {d : ℕ} (e : Direction d) :
    Measurable (rawCurrentProjection e) := by
  have hU : Measurable (fun p : RawCurrentData e × LocalUpperField e => p.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  exact ((ReferenceClasses.anchorOffsets_measurable.comp hU).prodMk
    ((rawCurrentProfiles_measurable e).comp measurable_fst)).prodMk
      (ReferenceClasses.anchorFields_measurable.comp (hU.prodMk measurable_snd))

noncomputable def currentWindowReference {d : ℕ} (e : Direction d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] :
    Kernel (ReferenceClasses.Data (HorizontalSpace e) × CurrentProfiles e)
      (ReferenceClasses.AllFields (HorizontalSpace e) (Row d)) :=
  (ReferenceClasses.reference ν).comap Prod.fst measurable_fst

instance currentWindowReference_markov {d : ℕ} (e : Direction d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] : IsMarkovKernel (currentWindowReference e ν) := by
  unfold currentWindowReference
  infer_instance

lemma rawCurrentProjection_kl_le {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (μ : Measure (RawCurrentData e × LocalUpperField e)) [IsFiniteMeasure μ] :
    let out := μ.map (rawCurrentProjection e)
    klDiv out (out.fst.compProd (currentWindowReference e ν)) ≤
      klDiv μ (μ.fst.prod (Measure.infinitePi (fun _ : ℕ × HorizontalSpace e => ν))) := by
  exact ReferenceClasses.anchorFrame_kl_le μ ν (fun z => z.2.2)
    (measurable_snd.comp measurable_snd) (rawCurrentProfiles e) (rawCurrentProfiles_measurable e)

noncomputable def actualCurrentWindow {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (i : ℤ) (m : ℕ) (X : EpisodeInput e) : CurrentWindow e :=
  ((ReferenceClasses.anchorOffsets (fun a => X.1.2 (i,a)),
    fun p => globalHorizontalCoordinate e (t X.1.1 i) X.1.1 (X.1.2 (i,p.1)+p.2)),
    fun p => episodeSplicedRow e t X i m p.1 p.2.1 p.2.2)

lemma actualCurrentWindow_measurable {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (i : ℤ) (m : ℕ) : Measurable (actualCurrentWindow e t i m) := by
  have hu : Measurable (fun X : EpisodeInput e => fun a => X.1.2 (i,a)) :=
    Measurable.of_eval fun a => (measurable_pi_apply (i,a)).comp
      (measurable_snd.comp measurable_fst)
  have ho := ReferenceClasses.anchorOffsets_measurable.comp hu
  have hp : Measurable (fun X : EpisodeInput e => fun p : ℕ × HorizontalSpace e =>
      globalHorizontalCoordinate e (t X.1.1 i) X.1.1 (X.1.2 (i,p.1)+p.2)) :=
    Measurable.of_eval fun p => actualArrayCoordinate_measurable e t ht i (i,p.1) p.2
  have hf : Measurable (fun X : EpisodeInput e => fun p : ReferenceClasses.Site (HorizontalSpace e) =>
      episodeSplicedRow e t X i m p.1 p.2.1 p.2.2) :=
    Measurable.of_eval fun p => episodeSplicedRow_measurable e t ht i m p.1 p.2.1 p.2.2
  exact (ho.prodMk hp).prodMk hf

lemma globalHorizontalCoordinate_stoppedObservation {d : ℕ} (e : Direction d)
    (τ : Environment d → ℕ)
    (hτ : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | τ ω=n})
    (filler ω : Environment d) (z : HorizontalSpace e) :
    globalHorizontalCoordinate e (τ ω)
        (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler ω) z =
      globalHorizontalCoordinate e (τ ω) ω z := by
  have h := currentStoppedProfile_observation e τ hτ filler ω
  have hn : τ (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n) τ filler ω) = τ ω :=
    stoppedRowGraft_stop (fun n => BelowHeight (realPosition (step e)) n) τ hτ ω filler
  dsimp only [currentStoppedProfile] at h
  rw [hn] at h
  apply Subtype.ext
  exact congrArg (fun μ : Measure (HorizontalSpace e) => (μ {z}).toReal) h

lemma actualCurrentWindow_raw {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (i : ℤ) (m : ℕ)
    (ht : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)]
      {ω | t ω i=n}) (filler : Environment d) (X : EpisodeInput e) :
    rawCurrentProjection e ((t X.1.1 i,
      (stoppedObservation (fun n => BelowHeight (realPosition (step e)) n)
        (fun ω => t ω i) filler X.1.1,fun a => X.1.2 (i,a))),
        localStoppedField e (fun ω => t ω i) (fun ω => t ω (i+m)) (X.1.1,X.2 (i,m))) =
      actualCurrentWindow e t i m X := by
  dsimp only [rawCurrentProjection,actualCurrentWindow,rawCurrentProfiles]
  refine Prod.ext (Prod.ext rfl ?_) ?_
  · funext p
    exact globalHorizontalCoordinate_stoppedObservation e (fun ω => t ω i) ht filler X.1.1 _
  · funext p
    dsimp only [ReferenceClasses.anchorFields,localStoppedField,episodeSplicedRow]

theorem actualCurrentWindow_law {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (i : ℤ) (m : ℕ)
    (hi : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | t ω i=n})
    (him : ∀ n : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)] {ω | t ω (i+m)=n})
    (filler : Environment d) :
    (rawCurrentWindow e ν Q (fun ω => t ω i) (fun ω => t ω (i+m)) (ht i) filler).map
      (rawCurrentProjection e) =
      (episodeInputLaw e ν Q t ht).map (actualCurrentWindow e t i m) := by
  unfold rawCurrentWindow
  rw [← episodeInputLaw_current e ν Q t ht i m]
  rw [Measure.map_map (rawCurrentWindow_measurable e _ _ hi him filler)
    (currentInput_measurable e i m)]
  rw [Measure.map_map (rawCurrentProjection_measurable e)]
  · congr 1
    funext X
    exact actualCurrentWindow_raw e t i m hi filler X
  · exact (rawCurrentWindow_measurable e _ _ hi him filler).comp (currentInput_measurable e i m)

end DirectionalTransience

end

end OAI
