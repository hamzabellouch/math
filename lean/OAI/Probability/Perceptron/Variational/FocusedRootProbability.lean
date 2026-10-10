import Mathlib
import OAI.Probability.Perceptron.Variational.FocusedVisit
import OAI.Probability.Perceptron.Variational.DecoratedFocus

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

lemma indexedMarkedRoot_counted (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hb : IndexedCascadeGood (n+1) p.2.1)
    (hj : Function.Injective (fun a => (indexedRootPoint ν step n z F p a).1))
    (ns : List (ℕ×(S×DecoratedCascade S n → ℝ≥0∞)))
    (hn : ∀ nf ∈ ns, 1 ≤ nf.1) (hm : ∀ nf ∈ ns, Measurable nf.2) :
    markedBlockProbability ns
      ((markedStableCountKernel (indexedCascadeRealize (n+1) p.2)).map
        (fun t : ℝ×(S×DecoratedCascade S n) =>
          (t.1+decoratedCenteredRoot ν step n z F (p.1,t.2),t.2)))
      (Fin.elim0 : Fin 0 → ℝ) =
      countedBlockProbability (indexedRootPoint ν step n z F p) ns (Fin.elim0 : Fin 0 → ℝ) := by
  rw [indexedCascadeGood_countKernel hb]
  have hc : Measurable (fun t : ℝ×(S×DecoratedCascade S n) =>
      (t.1+decoratedCenteredRoot ν step n z F (p.1,t.2),t.2)) :=
    (measurable_fst.add ((decoratedCenteredRoot_measurable ν step hs n z F hF).comp
      (measurable_const.prodMk measurable_snd))).prodMk measurable_snd
  have he : (indexedCascadeRealize (n+1) p.2).map
      (fun t : ℝ×(S×DecoratedCascade S n) =>
        (t.1+decoratedCenteredRoot ν step n z F (p.1,t.2),t.2)) =
      Measure.count.map (indexedRootPoint ν step n z F p) := by
    unfold indexedCascadeRealize
    rw [indexedPoissonMeasure_eq_map_count,Measure.map_map hc (measurable_of_countable _)]
    rfl
  rw [he]
  exact markedBlockProbability_count_map _ (measurable_of_countable _) hj ns hn hm (Fin.elim0 : Fin 0 → ℝ)

lemma indexedFocusedRoot_embeddings (ν : ProbabilityMeasure S) (step : X×S → X)
    (hst : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hb : IndexedCascadeGood (n+1) p.2.1)
    (hc : ∀ i j, 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p i j)).toReal)
    (hj : Function.Injective (fun a => (indexedRootPoint ν step n z F p a).1))
    (d : ℕ) (s : CascadeVisitShape n) (ss : List (CascadeVisitShape n))
    (hv : CascadeVisitShape.Valid (n+1) (s::ss)) :
    decoratedFocusedProbability ν step (n+1) z F (d+1) (s::ss)
      (p.1,indexedCascadeRealize (n+1) p.2) =
      ∑' a : Fin (ss.length+1) ↪ (Σ i, Fin ((p.2.1 i).1)),
        (indexedBranchProbability step n F p (a 0)) ^ (cascadeVisitCount n s+1) *
          decoratedFocusedProbability ν step n (fun i => z i.succ) (fun i => F i.succ) d s
            ((indexedChildPoint step n p (a 0).1 (a 0).2.val).1,
              indexedCascadeRealize n (indexedChildPoint step n p (a 0).1 (a 0).2.val).2) *
        ∏ i : Fin ss.length,
          (indexedBranchProbability step n F p (a i.succ)) ^ cascadeVisitCount n ss[i] *
            decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ)
              (trivialDecoratedShape X n ss[i])
              ((indexedChildPoint step n p (a i.succ).1 (a i.succ).2.val).1,
                indexedCascadeRealize n (indexedChildPoint step n p (a i.succ).1 (a i.succ).2.val).2) := by
  let ns : List (ℕ×(S×DecoratedCascade S n → ℝ≥0∞)) :=
    (cascadeVisitCount n s+1,fun t => decoratedFocusedProbability ν step n
      (fun i => z i.succ) (fun i => F i.succ) d s (step (p.1,t.1),t.2)) ::
    ss.map (fun t => (cascadeVisitCount n t,fun u => decoratedShapeProbability ν step n
      (fun i => z i.succ) (fun i => F i.succ) (trivialDecoratedShape X n t) (step (p.1,u.1),u.2)))
  have hn : ∀ nf ∈ ns, 1 ≤ nf.1 := by
    intro nf hnf
    rcases List.mem_cons.mp hnf with rfl | ht
    · simp
    · obtain ⟨t,hmem,rfl⟩ := List.mem_map.mp ht
      exact cascadeVisitCount_pos n t (hv.2 t (by simp [hmem]))
  have hm : ∀ nf ∈ ns, Measurable nf.2 := by
    intro nf hnf
    rcases List.mem_cons.mp hnf with rfl | ht
    · exact (decoratedFocusedProbability_measurable ν step hst n _ _
        (fun i => hF i.succ) d s (hv.2 s (by simp))).comp
          ((hst.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
    · obtain ⟨t,hmem,rfl⟩ := List.mem_map.mp ht
      exact (decoratedShapeProbability_measurable ν step hst n _ _ (fun i => hF i.succ) _
        (trivialDecoratedShape_valid X n t (hv.2 t (by simp [hmem])))).comp
          ((hst.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
  rw [decoratedFocusedProbability, indexedMarkedRoot_counted ν step hst n z F hF p hb hj ns hn hm,
    countedBlockProbability_embeddings _ hj]
  simp only [indexedRootPoint_probability ν step hst n z F hF p hb hc]
  rw [tsum_embedding_cast (show ns.length = ss.length+1 from by simp [ns])
    (fun i a => (indexedBranchProbability step n F p a)^ns[i].1 *
      ns[i].2 (indexedRootPoint ν step n z F p a).2)]
  simp only [ns,Fin.prod_univ_succ,Fin.getElem_fin,Fin.val_cast,Fin.val_zero,Fin.val_succ,
    List.getElem_cons_zero,List.getElem_cons_succ,List.getElem_map]
  rfl


lemma indexedFocusedVisit_eq_shape (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (d : ℕ) (hd : d ≤ n) (s : CascadeVisitShape n) (hv : s.Valid n) (x : X) :
    ∀ᵐ p ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
      (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)),
      indexedFocusedVisit step n F d s hv (x,p) =
        decoratedFocusedProbability ν step n z F d s (x,indexedCascadeRealize n p) := by
  induction d generalizing n x with
  | zero =>
    filter_upwards [indexedTiltedTotal_regular ν step hs n z hz hz0 hz1 F hF hI hM x,
      indexedShapeVisit_eq_shape ν step hs n z hz hz0 hz1 F hF hI hM s hv x] with p hp he
    rw [indexedFocusedVisit_zero step n F s hv (x,p) hp]
    cases n <;> simpa only [decoratedFocusedProbability] using he
  | succ d ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases s with
      | nil => exact (hv.1 rfl).elim
      | cons s ss =>
        have hzt : StrictMono (fun i : Fin n => z i.succ) :=
          fun i j hij => hz (Fin.succ_lt_succ_iff.mpr hij)
        have hvs : s.Valid n := hv.2 s (by simp)
        have hh := indexedCascade_ae_children ν step hs n z
          (fun p => indexedFocusedVisit step n (fun j => F j.succ) d s hvs p =
            decoratedFocusedProbability ν step n (fun j => z j.succ) (fun j => F j.succ) d s
              (p.1,indexedCascadeRealize n p.2))
          (measurableSet_eq_fun (indexedFocusedVisit_measurable step hs n _
            (fun j => hF j.succ) d s hvs)
            ((decoratedFocusedProbability_measurable ν step hs n _ _ (fun j => hF j.succ) d s hvs).comp
              (measurable_fst.prodMk ((indexedCascadeRealize_measurable n).comp measurable_snd))))
          (fun y => ih n _ hzt (fun j => hz0 j.succ) (fun j => hz1 j.succ) _ (fun j => hF j.succ)
            (fun j => hI j.succ) (fun j => hM j.succ) (by omega) s hvs y) x
        have he : ∀ i : Fin ss.length, ∀ᵐ p ∂
            (indexedCascadeBaseLaw (n+1) z : Measure (IndexedCascadeBase (n+1))).prod
              (indexedCascadeMarksLaw ν (n+1) : Measure (IndexedCascadeMarks S (n+1))),
            ∀ a b, indexedShapeVisit step n (fun j => F j.succ) ss[i]
                (indexedChildPoint step n (x,p) a b) =
              decoratedShapeProbability ν step n (fun j => z j.succ) (fun j => F j.succ)
                (trivialDecoratedShape X n ss[i])
                ((indexedChildPoint step n (x,p) a b).1,
                  indexedCascadeRealize n (indexedChildPoint step n (x,p) a b).2) := by
          intro i
          have hvi : ss[i].Valid n := hv.2 _ (List.mem_cons_of_mem _ (List.getElem_mem i.isLt))
          exact indexedCascade_ae_children ν step hs n z
            (fun p => indexedShapeVisit step n (fun j => F j.succ) ss[i] p =
              decoratedShapeProbability ν step n (fun j => z j.succ) (fun j => F j.succ)
                (trivialDecoratedShape X n ss[i]) (p.1,indexedCascadeRealize n p.2))
            (measurableSet_eq_fun (indexedShapeVisit_measurable hs n _ (fun j => hF j.succ) ss[i])
              ((decoratedShapeProbability_measurable ν step hs n _ _ (fun j => hF j.succ) _
                (trivialDecoratedShape_valid X n ss[i] hvi)).comp
                (measurable_fst.prodMk ((indexedCascadeRealize_measurable n).comp measurable_snd))))
            (fun y => indexedShapeVisit_eq_shape ν step hs n _ hzt (fun j => hz0 j.succ)
              (fun j => hz1 j.succ) _ (fun j => hF j.succ) (fun j => hI j.succ)
              (fun j => hM j.succ) ss[i] hvi y) x
        have hc := indexedCascade_ae_children ν step hs n z
          (fun p => 0 < (indexedTiltedTotal step n (fun j => F j.succ) p).toReal)
          (measurableSet_lt measurable_const ((indexedTiltedTotal_measurable hs n _ (fun j => hF j.succ)).ennreal_toReal))
          (fun y => indexedTiltedTotal_regular ν step hs n _ hzt (fun j => hz0 j.succ) (fun j => hz1 j.succ)
            _ (fun j => hF j.succ) (fun j => hI j.succ) (fun j => hM j.succ) y) x
        have hj := indexedCenteredRoot_simple ν step hs n z hz hz0 hz1 F hF hI hM x
        have hb := (measurePreserving_fst
          (μ := (indexedCascadeBaseLaw (n+1) z : Measure (IndexedCascadeBase (n+1))))
          (ν := (indexedCascadeMarksLaw ν (n+1) : Measure (IndexedCascadeMarks S (n+1))))).quasiMeasurePreserving.ae
            (indexedCascadeGood_ae (n+1) z hz0 hz1)
        filter_upwards [hh,ae_all_iff.mpr he,hc,hj,hb] with p hh he hc hj hb
        rw [indexedFocusedVisit_succ step n F d s ss hv (x,p) hc,
          indexedFocusedRoot_embeddings ν step hs n z F hF (x,p) hb hc hj d s ss hv]
        apply tsum_congr
        intro a
        apply congrArg₂ (· * ·)
        · exact congrArg (fun c : ℝ≥0∞ => _ * c) (hh (a 0).1 (a 0).2.val)
        · apply Finset.prod_congr rfl
          intro i _hi
          exact congrArg (fun c : ℝ≥0∞ => _ * c) (he i (a i.succ).1 (a i.succ).2.val)

theorem indexedFocusedVisit_integral (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (d : ℕ) (hd : d ≤ n) (s : CascadeVisitShape n) (hv : s.Valid n) (x : X) :
    (∫⁻ p, indexedFocusedVisit step n F d s hv (x,p)
      ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))) =
      cascadeShapeLikelihood n z 0 s *
        ENNReal.ofReal (focusedShapeNumerator n z 0 d s/(cascadeVisitCount n s:ℝ)) := by
  rw [lintegral_congr_ae (indexedFocusedVisit_eq_shape ν step hs n z hz hz0 hz1 F hF hI hM d hd s hv x)]
  have hm : Measurable (fun η : DecoratedCascade S n =>
      decoratedFocusedProbability ν step n z F d s (x,η)) :=
    (decoratedFocusedProbability_measurable ν step hs n z F hF d s hv).comp
      (measurable_const.prodMk measurable_id)
  rw [← lintegral_map hm (indexedCascadeRealize_measurable n),indexedCascadeRealize_law ν n z,
    ← decoratedBiasedLaw_zero ν step n z F x]
  simpa only [sub_zero] using decoratedFocusedProbability_integral ν step hs n z hz hz0 hz1 F hF hI hM
    0 (by norm_num) hz0 d hd s hv x

end SphericalPerceptronFreeEnergy
end

end OAI
