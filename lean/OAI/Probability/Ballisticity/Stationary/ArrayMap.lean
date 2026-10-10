import Mathlib
import OAI.Probability.Ballisticity.Estimates.GlobalProfile

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

instance enat_borel : BorelSpace ℕ∞ := ⟨borel_eq_top_of_countable.symm⟩
instance horizontalOnePoint_measurable {d : ℕ} (e : Direction d) :
    MeasurableSpace (OnePoint (HorizontalSpace e)) := borel _
instance horizontalOnePoint_borel {d : ℕ} (e : Direction d) :
    BorelSpace (OnePoint (HorizontalSpace e)) := ⟨rfl⟩

noncomputable def episodeProfile {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ω : Environment d) (i : ℤ) :=
  globalHorizontalProfile e (t ω i) ω

instance episodeProfile_probability {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ω : Environment d) (i : ℤ) :
    IsProbabilityMeasure (episodeProfile e t ω i) := by
  unfold episodeProfile
  infer_instance

lemma globalHorizontalProfile_joint_measurable {d : ℕ} (e : Direction d) :
    Measurable (fun p : Environment d×ℕ => globalHorizontalProfile e p.2 p.1) := by
  apply measurable_from_prod_countable_left
  intro n
  exact globalHorizontalProfile_measurable e n

lemma globalHorizontalCoordinate_joint_measurable {d : ℕ} (e : Direction d) :
    Measurable (fun p : (Environment d×ℕ)×HorizontalSpace e =>
      globalHorizontalCoordinate e p.1.2 p.1.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro z
  apply Measurable.subtype_mk
  exact (((Measure.measurable_coe (measurableSet_singleton z)).comp
    (globalHorizontalProfile_joint_measurable e)).ennreal_toReal)

abbrev EpisodeAnchors {d : ℕ} (e : Direction d) := (ℤ×ℕ) → HorizontalSpace e
abbrev EpisodeAuxiliary {d : ℕ} (e : Direction d) := (ℤ×ℕ) → (ℕ×HorizontalSpace e) → Row d
abbrev EpisodeInput {d : ℕ} (e : Direction d) := (Environment d×EpisodeAnchors e)×EpisodeAuxiliary e

lemma episodeProfile_measurable {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) (i : ℤ) :
    Measurable (fun ω => episodeProfile e t ω i) := by
  have hn : Measurable (fun ω : Environment d => (ω,t ω i)) := measurable_id.prodMk (ht i)
  have hm := (globalHorizontalProfile_joint_measurable e).comp hn
  simpa only [Function.comp_def,episodeProfile] using hm

noncomputable def globalEpisodeAnchors {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) :
    Kernel (Environment d) (EpisodeAnchors e) :=
  AnchorSampling.anchorKernel (episodeProfile e t)
    (episodeProfile_measurable e t ht)

instance globalEpisodeAnchors_markov {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) :
    IsMarkovKernel (globalEpisodeAnchors e t ht) := by unfold globalEpisodeAnchors; infer_instance

noncomputable def episodeAuxiliaryLaw {d : ℕ} (e : Direction d) (ν : Measure (Row d)) :
    Measure (EpisodeAuxiliary e) :=
  Measure.infinitePi (fun _ : ℤ×ℕ => Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν))

instance episodeAuxiliaryLaw_probability {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (episodeAuxiliaryLaw e ν) := by unfold episodeAuxiliaryLaw; infer_instance

noncomputable def episodeInputLaw {d : ℕ} (e : Direction d) (ν : Measure (Row d))
    (Q : Measure (Environment d)) (t : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) : Measure (EpisodeInput e) :=
  (Q.compProd (globalEpisodeAnchors e t ht)).prod (episodeAuxiliaryLaw e ν)

instance episodeInputLaw_probability {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsProbabilityMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) :
    IsProbabilityMeasure (episodeInputLaw e ν Q t ht) := by unfold episodeInputLaw; infer_instance

noncomputable def episodeCost {d : ℕ} (e : Direction d) (t : Environment d → ℤ → ℕ)
    (ω : Environment d) (i : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.log (crossingQuenched (realPosition (step e)) 0 (t ω i) ω).toReal-
    Real.log (crossingQuenched (realPosition (step e)) 0 (t ω (i+1)) ω).toReal)

lemma episodeCost_measurable {d : ℕ} (e : Direction d) (t : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (i : ℤ) : Measurable (fun ω => episodeCost e t ω i) := by
  have hm : Measurable (fun p : Environment d×ℕ => crossingQuenched (realPosition (step e)) 0 p.2 p.1) := by
    apply measurable_from_prod_countable_left
    intro n
    change Measurable (crossingQuenched (realPosition (step e)) 0 (n : ℝ))
    exact measurable_crossingQuenched _ _ _
  exact (((hm.comp (measurable_id.prodMk (ht i))).ennreal_toReal.log).sub
    ((hm.comp (measurable_id.prodMk (ht (i+1)))).ennreal_toReal.log)).ennreal_ofReal

noncomputable def episodeSplicedRow {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (X : EpisodeInput e)
    (i : ℤ) (m a l : ℕ) (z : HorizontalSpace e) : Row d :=
  if l<t X.1.1 (i+m)-t X.1.1 i then
    X.1.1 (horizontalLift e (t X.1.1 i+l) (X.1.2 (i,a)+z))
  else X.2 (i,m) (l,X.1.2 (i,a)+z)

noncomputable def actualArrayMap {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (X : EpisodeInput e) : ActualEpisodeArray e :=
  ⟨(fun i => ((t X.1.1 (i+1)-t X.1.1 i : ℕ),(J X.1.1 i : ℕ),episodeCost e t X.1.1 i)),
    (fun p => ((X.1.2 p.2-X.1.2 p.1 : HorizontalSpace e) : OnePoint (HorizontalSpace e))),
    (fun p => globalHorizontalCoordinate e (t X.1.1 p.1) X.1.1 (X.1.2 p.2.1+p.2.2)),
    (fun p => episodeSplicedRow e t X p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)⟩

lemma episodeSplicedRow_measurable {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (i : ℤ) (m a l : ℕ) (z : HorizontalSpace e) :
    Measurable (fun X : EpisodeInput e => episodeSplicedRow e t X i m a l z) := by
  have hw : Measurable (fun X : EpisodeInput e => X.1.1) := measurable_fst.comp measurable_fst
  have hU : Measurable (fun X : EpisodeInput e => X.1.2 (i,a)) :=
    (measurable_pi_apply (i,a)).comp (measurable_snd.comp measurable_fst)
  have hx : Measurable (fun X : EpisodeInput e => horizontalLift e (t X.1.1 i+l) (X.1.2 (i,a)+z)) :=
    (measurable_of_countable (fun p : ℕ×HorizontalSpace e => horizontalLift e (p.1+l) (p.2+z))).comp
      (((ht i).comp hw).prodMk hU)
  unfold episodeSplicedRow
  apply Measurable.ite (measurableSet_lt measurable_const (((ht (i+m)).comp hw).sub ((ht i).comp hw)))
  · exact measurable_current_row.comp (hw.prodMk hx)
  · have hev : Measurable (fun p : (((ℕ×HorizontalSpace e) → Row d)×(ℕ×HorizontalSpace e)) => p.1 p.2) :=
      measurable_from_prod_countable_left (fun q => measurable_pi_apply q)
    exact hev.comp ((((measurable_pi_apply (i,m)).comp measurable_snd).prodMk
      (measurable_const.prodMk (hU.add_const z))))

lemma actualArrayCoordinate_measurable {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (j : ℤ) (p : ℤ×ℕ) (z : HorizontalSpace e) :
    Measurable (fun X : EpisodeInput e => globalHorizontalCoordinate e (t X.1.1 j) X.1.1 (X.1.2 p+z)) := by
  have hw : Measurable (fun X : EpisodeInput e => X.1.1) := measurable_fst.comp measurable_fst
  have hU : Measurable (fun X : EpisodeInput e => X.1.2 p) :=
    (measurable_pi_apply p).comp (measurable_snd.comp measurable_fst)
  have ha : Measurable (fun X : EpisodeInput e => ((X.1.1,t X.1.1 j),X.1.2 p+z)) :=
    (hw.prodMk ((ht j).comp hw)).prodMk (hU.add_const z)
  have hm := (globalHorizontalCoordinate_joint_measurable e).comp ha
  simpa only [Function.comp_def] using hm

lemma actualArrayMap_measurable {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) : Measurable (actualArrayMap e t J) := by
  have hw : Measurable (fun X : EpisodeInput e => X.1.1) := measurable_fst.comp measurable_fst
  have hU (p : ℤ×ℕ) : Measurable (fun X : EpisodeInput e => X.1.2 p) :=
    (measurable_pi_apply p).comp (measurable_snd.comp measurable_fst)
  refine Measurable.prodMk (Measurable.of_eval fun i => ?_)
    (Measurable.prodMk (Measurable.of_eval fun p => ?_)
      (Measurable.prodMk (Measurable.of_eval fun p => ?_) (Measurable.of_eval fun p => ?_)))
  · have hc : Measurable (fun n : ℕ => (n : ℕ∞)) := measurable_of_countable _
    exact (hc.comp (((ht (i+1)).comp hw).sub ((ht i).comp hw))).prodMk
      ((hc.comp ((hJ i).comp hw)).prodMk ((episodeCost_measurable e t ht i).comp hw))
  · exact OnePoint.continuous_coe.measurable.comp ((hU p.2).sub (hU p.1))
  · exact actualArrayCoordinate_measurable e t ht _ _ _
  · exact episodeSplicedRow_measurable e t ht _ _ _ _ _

end DirectionalTransience

end

end OAI
