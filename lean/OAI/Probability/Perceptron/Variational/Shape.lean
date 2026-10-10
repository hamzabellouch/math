import Mathlib
import OAI.Probability.Perceptron.Variational.IndexedTwoShape
import OAI.Probability.Perceptron.Variational.ShapeProbability

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology

section

lemma countedBlockProbability_eq_excluded {I S : Type*} (p : I → ℝ×S)
    (ns : List (ℕ×(S → ℝ≥0∞))) {m : ℕ} (v : Fin m → ℝ) :
    countedBlockProbability p ns v = excludedBlockSum (fun i => (p i).1)
      (ns.map (fun nf i =>
        (((∑' k, ENNReal.ofReal (Real.exp (p k).1))⁻¹)*
          ENNReal.ofReal (Real.exp (p i).1))^nf.1 * nf.2 (p i).2)) v := by
  induction ns generalizing m with
  | nil => rfl
  | cons nf ns ih =>
    simp only [countedBlockProbability, List.map_cons, excludedBlockSum]
    apply tsum_congr
    intro i
    split_ifs <;> simp only [ih]

lemma countedBlockProbability_embeddings {I S : Type*} (p : I → ℝ×S)
    (hinj : Function.Injective (fun i => (p i).1))
    (ns : List (ℕ×(S → ℝ≥0∞))) :
    countedBlockProbability p ns (Fin.elim0 : Fin 0 → ℝ) =
      ∑' a : Fin ns.length ↪ I, ∏ j : Fin ns.length,
        (((∑' k, ENNReal.ofReal (Real.exp (p k).1))⁻¹)*
          ENNReal.ofReal (Real.exp (p (a j)).1))^ns[j].1 * ns[j].2 (p (a j)).2 := by
  rw [countedBlockProbability_eq_excluded, excludedBlockSum_embeddings _ hinj]
  exact tsum_embeddings_list_map ns _ (fun (f : I → ℝ≥0∞) a => f a)

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

lemma indexedShapeRoot_embeddings (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hb : IndexedCascadeGood (n+1) p.2.1)
    (hc : ∀ i j, 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p i j)).toReal)
    (hj : Function.Injective (fun a => (indexedRootPoint ν step n z F p a).1))
    (ss : List (DecoratedVisitShape X n)) (hv : ∀ s ∈ ss, s.Valid n) :
    decoratedShapeProbability ν step (n+1) z F ss (p.1,indexedCascadeRealize (n+1) p.2) =
      ∑' a : Fin ss.length ↪ (Σ i, Fin ((p.2.1 i).1)),
        ∏ i : Fin ss.length,
          (indexedBranchProbability step n F p (a i)) ^ cascadeVisitCount n (ss[i].bare n) *
            decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ) ss[i]
              ((indexedChildPoint step n p (a i).1 (a i).2.val).1,
                indexedCascadeRealize n (indexedChildPoint step n p (a i).1 (a i).2.val).2) := by
  rw [indexedShapeRoot_counted ν step hs n z F hF p hb hj ss hv,
    countedBlockProbability_embeddings _ hj]
  rw [tsum_embeddings_list_map ss _ (fun (nf : ℕ×(S×DecoratedCascade S n → ℝ≥0∞)) a =>
    (((∑' b, ENNReal.ofReal (Real.exp (indexedRootPoint ν step n z F p b).1))⁻¹)*
      ENNReal.ofReal (Real.exp (indexedRootPoint ν step n z F p a).1))^nf.1 *
        nf.2 (indexedRootPoint ν step n z F p a).2)]
  simp only [indexedRootPoint_probability ν step hs n z F hF p hb hc]
  rfl

end

def trivialDecoratedShape (X : Type) : (n : ℕ) → CascadeVisitShape n → DecoratedVisitShape X n
  | 0, s => (s,fun _ => 1)
  | n+1, ss => ss.map (trivialDecoratedShape X n)

lemma trivialDecoratedShape_bare (X : Type) (n : ℕ) (s : CascadeVisitShape n) :
    (trivialDecoratedShape X n s).bare n = s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [trivialDecoratedShape, DecoratedVisitShape.bare, List.map_map]
    have h : (DecoratedVisitShape.bare n ∘ trivialDecoratedShape X n) = id := funext ih
    rw [h, List.map_id]

lemma trivialDecoratedShape_valid (X : Type) [MeasurableSpace X]
    (n : ℕ) (s : CascadeVisitShape n) (hs : s.Valid n) :
    (trivialDecoratedShape X n s).Valid n := by
  induction n with
  | zero => exact ⟨hs,measurable_const⟩
  | succ n ih =>
    refine ⟨fun he => hs.1 (List.map_eq_nil_iff.mp he), ?_⟩
    intro t ht
    obtain ⟨s',hs',rfl⟩ := List.mem_map.mp ht
    exact ih s' (hs.2 s' hs')

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

omit [MeasurableSpace X] [Nonempty S] in
lemma trivialDecoratedShape_markValue (ν : ProbabilityMeasure S) (step : X×S → X)
    (n : ℕ) (z : Fin n → ℝ) (F : Fin n → X×S → ℝ)
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (s : CascadeVisitShape n) (x : X) :
    decoratedShapeMarkValue ν step n z F (trivialDecoratedShape X n s) x = 1 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [trivialDecoratedShape, decoratedShapeMarkValue, List.map_map]
    apply List.prod_eq_one
    intro y hy
    obtain ⟨s',hs',rfl⟩ := List.mem_map.mp hy
    simp only [Function.comp_apply]
    simp_rw [ih _ _ (fun i => hI i.succ) (fun i => hM i.succ), mul_one]
    rw [← ofReal_integral_eq_lintegral_ofReal (hI 0 x)
      (ae_of_all _ fun s => (Real.exp_pos _).le), hM 0 x, ENNReal.ofReal_one]

lemma trivialDecoratedShape_probability_succ (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hb : IndexedCascadeGood (n+1) p.2.1)
    (hc : ∀ i j, 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p i j)).toReal)
    (hj : Function.Injective (fun a => (indexedRootPoint ν step n z F p a).1))
    (ss : CascadeVisitShape (n+1)) (hv : ss.Valid (n+1)) :
    decoratedShapeProbability ν step (n+1) z F (trivialDecoratedShape X (n+1) ss)
        (p.1,indexedCascadeRealize (n+1) p.2) =
      ∑' a : Fin ss.length ↪ (Σ i, Fin ((p.2.1 i).1)),
        ∏ i : Fin ss.length,
          (indexedBranchProbability step n F p (a i)) ^ cascadeVisitCount n ss[i] *
            decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ)
              (trivialDecoratedShape X n ss[i])
              ((indexedChildPoint step n p (a i).1 (a i).2.val).1,
                indexedCascadeRealize n (indexedChildPoint step n p (a i).1 (a i).2.val).2) := by
  rw [trivialDecoratedShape, indexedShapeRoot_embeddings ν step hs n z F hF p hb hc hj _
    (by intro s h; obtain ⟨t,ht,rfl⟩ := List.mem_map.mp h
        exact trivialDecoratedShape_valid X n t (hv.2 t ht))]
  rw [tsum_embeddings_list_map ss (trivialDecoratedShape X n)
    (fun (s : DecoratedVisitShape X n) a =>
      (indexedBranchProbability step n F p a)^cascadeVisitCount n (s.bare n) *
        decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ) s
          ((indexedChildPoint step n p a.1 a.2.val).1,
            indexedCascadeRealize n (indexedChildPoint step n p a.1 a.2.val).2))]
  simp only [trivialDecoratedShape_bare]

lemma indexedShapeVisit_eq_shape (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (s : CascadeVisitShape n) (hv : s.Valid n) (x : X) :
    ∀ᵐ p ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
      (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)),
      indexedShapeVisit step n F s (x,p) =
        decoratedShapeProbability ν step n z F (trivialDecoratedShape X n s)
          (x,indexedCascadeRealize n p) := by
  induction n generalizing x with
  | zero => exact ae_of_all _ fun p => indexedShapeVisit_zero step F s (x,p)
  | succ n ih =>
    have hzt : StrictMono (fun i : Fin n => z i.succ) := fun i j hij => hz (Fin.succ_lt_succ_iff.mpr hij)
    have he : ∀ i : Fin s.length, ∀ᵐ p ∂
        (indexedCascadeBaseLaw (n+1) z : Measure (IndexedCascadeBase (n+1))).prod
          (indexedCascadeMarksLaw ν (n+1) : Measure (IndexedCascadeMarks S (n+1))),
        ∀ a b, indexedShapeVisit step n (fun j => F j.succ) s[i]
            (indexedChildPoint step n (x,p) a b) =
          decoratedShapeProbability ν step n (fun j => z j.succ) (fun j => F j.succ)
            (trivialDecoratedShape X n s[i])
            ((indexedChildPoint step n (x,p) a b).1,
              indexedCascadeRealize n (indexedChildPoint step n (x,p) a b).2) := by
      intro i
      exact indexedCascade_ae_children ν step hs n z
        (fun p => indexedShapeVisit step n (fun j => F j.succ) s[i] p =
          decoratedShapeProbability ν step n (fun j => z j.succ) (fun j => F j.succ)
            (trivialDecoratedShape X n s[i]) (p.1,indexedCascadeRealize n p.2))
        (measurableSet_eq_fun (indexedShapeVisit_measurable hs n _ (fun j => hF j.succ) s[i])
          ((decoratedShapeProbability_measurable ν step hs n _ _ (fun j => hF j.succ) _
            (trivialDecoratedShape_valid X n s[i] (hv.2 _ (List.getElem_mem i.isLt)))).comp
            (measurable_fst.prodMk ((indexedCascadeRealize_measurable n).comp measurable_snd))))
        (fun y => ih _ hzt (fun j => hz0 j.succ) (fun j => hz1 j.succ) _ (fun j => hF j.succ)
          (fun j => hI j.succ) (fun j => hM j.succ) s[i] (hv.2 _ (List.getElem_mem i.isLt)) y) x
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
    filter_upwards [ae_all_iff.mpr he,hc,hj,hb] with p he hc hj hb
    rw [indexedShapeVisit_succ step n F s hv (x,p) hc,
      trivialDecoratedShape_probability_succ ν step hs n z F hF (x,p) hb hc hj s hv]
    apply tsum_congr
    intro a
    apply Finset.prod_congr rfl
    intro i hi
    rw [he i (a i).1 (a i).2.val]

theorem indexedShapeVisit_integral (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1)
    (s : CascadeVisitShape n) (hv : s.Valid n) (x : X) :
    (∫⁻ p, indexedShapeVisit step n F s (x,p)
      ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))) =
      cascadeShapeLikelihood n z 0 s := by
  rw [lintegral_congr_ae (indexedShapeVisit_eq_shape ν step hs n z hz hz0 hz1 F hF hI hM s hv x),
    indexedShapeProbability_integral ν step hs n z hz hz0 hz1 F hF hI hM _
      (trivialDecoratedShape_valid X n s hv) x,
    trivialDecoratedShape_bare, trivialDecoratedShape_markValue ν step n z F hI hM s x, mul_one]

end SphericalPerceptronFreeEnergy

end

end OAI
