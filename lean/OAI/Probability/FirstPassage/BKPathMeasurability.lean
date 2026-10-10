import OAI.Probability.FirstPassage.BKQuantization
import Mathlib.MeasureTheory.Function.Floor

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter Set
open scoped Topology

lemma continuous_pathCost (p : Vertex) (ds : List Step) :
    Continuous (fun w : Edge → ℝ => pathCost w p ds) := by
  induction ds generalizing p with
  | nil => exact continuous_const
  | cons d ds ih => exact (continuous_apply (d.edge p)).add (ih _)

def PositiveStrictDisjointPaths (S : Finset Edge) (Fs : List (Set StrictPathWitness))
    (z : (Edge → ℝ) × (Edge → ℝ)) : Prop :=
  ∃ ps : List StrictPathWitness,
    List.Forall₂ (fun p F => p ∈ F ∧ p.edges ⊆ S ∧
      (∀ e ∈ p.edges, 0 < z.1 e) ∧ p.Good z.2) ps Fs ∧
    ps.Pairwise (fun p q => Disjoint p.edges q.edges)

lemma isOpen_positiveStrictDisjointPaths (S : Finset Edge) (Fs : List (Set StrictPathWitness)) :
    IsOpen {z | PositiveStrictDisjointPaths S Fs z} := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  obtain ⟨ps,hps,hd⟩ := hz
  have hn : ∀ᶠ y in 𝓝 z, List.Forall₂ (fun p F => p ∈ F ∧ p.edges ⊆ S ∧
      (∀ e ∈ p.edges, 0 < y.1 e) ∧ p.Good y.2) ps Fs := by
    clear hd
    induction hps with
    | nil => exact Filter.Eventually.of_forall (fun _ => List.Forall₂.nil)
    | @cons p F ps Fs hp hps ih =>
      have he : ∀ᶠ y in 𝓝 z, ∀ e ∈ p.edges, 0 < y.1 e := by
        rw [Filter.eventually_all_finset]
        intro e he
        exact ((continuous_apply e).comp continuous_fst).continuousAt.eventually
          (lt_mem_nhds (hp.2.2.1 e he))
      have hc : ∀ᶠ y in 𝓝 z, p.Good y.2 :=
        ((continuous_pathCost p.start p.steps).comp continuous_snd).continuousAt.eventually
          (gt_mem_nhds hp.2.2.2)
      filter_upwards [he,hc,ih] with y he hc ht
      exact List.Forall₂.cons ⟨hp.1,hp.2.1,he,hc⟩ ht
  exact hn.mono (fun y hy => ⟨ps,hy,hd⟩)

lemma strictDisjointPaths_positive_iff (S : Finset Edge) (Fs : List (Set StrictPathWitness))
    (w : Edge → ℝ) :
    PositiveStrictDisjointPaths S Fs (fun _ => 1,w) ↔ StrictDisjointPaths S Fs w := by
  constructor
  · rintro ⟨ps,hps,hd⟩
    exact ⟨ps,hps.imp (fun _ _ h => ⟨h.1,h.2.1,h.2.2.2⟩),hd⟩
  · rintro ⟨ps,hps,hd⟩
    exact ⟨ps,hps.imp (fun _ _ h => ⟨h.1,h.2.1,fun _ _ => by norm_num,h.2.2⟩),hd⟩

lemma isOpen_strictDisjointPaths (S : Finset Edge) (Fs : List (Set StrictPathWitness)) :
    IsOpen {w | StrictDisjointPaths S Fs w} := by
  have h := (isOpen_positiveStrictDisjointPaths S Fs).preimage
    (continuous_const.prodMk continuous_id : Continuous (fun w : Edge → ℝ => ((fun _ => (1:ℝ)),w)))
  simpa only [Set.preimage_ofPred_eq,strictDisjointPaths_positive_iff] using h

lemma measurable_roundedSurvival (t : ℕ) : Measurable (roundedSurvival t) := by
  unfold roundedSurvival
  fun_prop

lemma measurable_roundedEdgeCost (t : ℕ) : Measurable (roundedEdgeCost t) := by
  exact (Real.measurable_log.comp (measurable_roundedSurvival t)).neg

lemma measurableSet_roundedDisjointPaths (S : Finset Edge) (Fs : List (Set StrictPathWitness)) (t : ℕ) :
    MeasurableSet {w | RoundedDisjointPaths S Fs t w} := by
  have hm : Measurable (fun w : Edge → ℝ =>
      ((fun e => roundedSurvival t (w e)),(fun e => roundedEdgeCost t (w e)))) :=
    (Measurable.of_eval (fun e => (measurable_roundedSurvival t).comp (measurable_pi_apply e))).prodMk
      (Measurable.of_eval (fun e => (measurable_roundedEdgeCost t).comp (measurable_pi_apply e)))
  exact (isOpen_positiveStrictDisjointPaths S Fs).measurableSet.preimage hm

lemma measurableSet_strictDisjointPaths (S : Finset Edge) (Fs : List (Set StrictPathWitness)) :
    MeasurableSet {w | StrictDisjointPaths S Fs w} := (isOpen_strictDisjointPaths S Fs).measurableSet

end PlanarFPP

end OAI
