import Mathlib
import OAI.Probability.Perceptron.Variational.AtomicBranches
import OAI.Probability.Perceptron.Cascade.IndexedTiltedWeights

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

lemma indexedTiltedTotal_regular (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) :
    ∀ᵐ p ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
      (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)),
       0 < (indexedTiltedTotal step n F (x,p)).toReal := by
  have hR : MeasurePreserving (indexedCascadeRealize (S := S) n)
      ((indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)))
      (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)) :=
    ⟨indexedCascadeRealize_measurable n,indexedCascadeRealize_law ν n z⟩
  have hp := hR.quasiMeasurePreserving.ae
    (decoratedWeightedTotal_pos ν step hs n z hz hz0 hz1 F hF hI hM x)
  have hg := (measurePreserving_fst (μ := (indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)))
    (ν := (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)))).quasiMeasurePreserving.ae
      (indexedCascadeGood_ae n z hz0 hz1)
  filter_upwards [hp,hg] with p hp hg
  rwa [indexedTiltedTotal_eq hs n F hF (x,p) hg]

lemma centeredMarkedPoisson_simple (ν : Measure S) [IsProbabilityMeasure ν]
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) {F : S → ℝ} (hF : Measurable F)
    (hI : Integrable (fun s => Real.exp (b*F s)) ν) :
    ∀ᵐ η ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν),
      ∀ᵐ t ∂((η.map (logMarkShift (centeredLogMark ν b F))).map Prod.fst),
        ((η.map (logMarkShift (centeredLogMark ν b F))).map Prod.fst) {t} = 1 := by
  let τ := exponentialMarkTilt ν b F
  have : IsProbabilityMeasure τ := exponentialMarkTilt_probability ν hI
  have hc : Measurable (centeredLogMark ν b F) := centeredLogMark_measurable ν b hF
  have ht : MeasurePreserving (Measure.map (logMarkShift (centeredLogMark ν b F)))
      (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν))
      (poissonRandomMeasureLaw ((stableLogIntensity b).prod τ)) := by
    refine ⟨Measure.measurable_map _ (logMarkShift_measurable hc), ?_⟩
    rw [stablePoisson_mark_shift ν hb.le hc]
    congr 1
    exact congrArg ((stableLogIntensity b).prod) (centeredLogMark_density ν hb.ne' hI)
  have hp : MeasurePreserving (Measure.map (Prod.fst : ℝ×S → ℝ))
      (poissonRandomMeasureLaw ((stableLogIntensity b).prod τ))
      (poissonRandomMeasureLaw (stableLogIntensity b)) :=
    ⟨Measure.measurable_map _ measurable_fst,markedStable_project_law τ b⟩
  exact (hp.comp ht).quasiMeasurePreserving.ae (stablePoissonCount_simple hb hb1)

lemma indexedCenteredRoot_simple (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) :
    ∀ᵐ p ∂(indexedCascadeBaseLaw (n+1) z : Measure (IndexedCascadeBase (n+1))).prod
      (indexedCascadeMarksLaw ν (n+1) : Measure (IndexedCascadeMarks S (n+1))),
      Function.Injective (fun a : Σ i, Fin ((p.1 i).1) =>
        (((p.1 a.1).2 a.2.val).1 + decoratedCenteredRoot ν step n z F
          (x,((p.2 a.1 a.2.val).1,indexedCascadeRealize n
            ((((p.1 a.1).2 a.2.val).2,(p.2 a.1 a.2.val).2)))))) := by
  let D := ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ) :
    Measure (DecoratedCascade S n)))
  have hR : MeasurePreserving (indexedCascadeRealize (S := S) (n+1))
      ((indexedCascadeBaseLaw (n+1) z : Measure (IndexedCascadeBase (n+1))).prod
        (indexedCascadeMarksLaw ν (n+1) : Measure (IndexedCascadeMarks S (n+1))))
      (decoratedCascadeLaw ν (n+1) z : Measure (DecoratedCascade S (n+1))) :=
    ⟨indexedCascadeRealize_measurable (n+1),indexedCascadeRealize_law ν (n+1) z⟩
  have hpot : Measurable (fun t => decoratedRootPotential step n F (x,t)) :=
    (decoratedRootPotential_measurable step hs n F hF).comp (measurable_const.prodMk measurable_id)
  have he := centeredMarkedPoisson_simple D (hz0 0) (hz1 0) hpot
    (decoratedRootPotential_integrable ν step hs n z hz hz0 hz1 F hF hI hM x)
  have hae := hR.quasiMeasurePreserving.ae he
  filter_upwards [hae] with p hp
  let a : ℕ → ℕ×(ℕ → ℝ×(S×DecoratedCascade S n)) := fun i => ((p.1 i).1,fun j =>
      (((p.1 i).2 j).1,((p.2 i j).1,indexedCascadeRealize n ((((p.1 i).2 j).2,(p.2 i j).2)))))
  let f : (Σ i, Fin ((p.1 i).1)) → ℝ := fun q => ((a q.1).2 q.2.val).1 +
    decoratedCenteredRoot ν step n z F (x,((a q.1).2 q.2.val).2)
  have hmap : (((indexedCascadeRealize (n+1) p).map
      (logMarkShift (centeredLogMark D (z 0) (fun t => decoratedRootPotential step n F (x,t))))).map
        Prod.fst) = Measure.count.map f := by
    change ((indexedPoissonMeasure a).map _).map _ = _
    rw [indexedPoissonMeasure_eq_map_count,
      Measure.map_map (logMarkShift_measurable (centeredLogMark_measurable D (z 0) hpot))
          (measurable_of_countable _),
      Measure.map_map measurable_fst (measurable_of_countable _)]
    rfl
  rw [hmap] at hp
  exact injective_of_simple_count_map f (measurable_of_countable _) hp

lemma indexedShapeRoot_counted (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hb : IndexedCascadeGood (n+1) p.2.1)
    (hj : Function.Injective (fun a => (indexedRootPoint ν step n z F p a).1))
    (ss : List (DecoratedVisitShape X n)) (hv : ∀ s ∈ ss, s.Valid n) :
    decoratedShapeProbability ν step (n+1) z F ss (p.1,indexedCascadeRealize (n+1) p.2) =
      countedBlockProbability (indexedRootPoint ν step n z F p)
        (ss.map (fun s => (cascadeVisitCount n (s.bare n),fun t : S×DecoratedCascade S n =>
          decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ) s
            (step (p.1,t.1),t.2)))) (Fin.elim0 : Fin 0 → ℝ) := by
  rw [decoratedShapeProbability,indexedCascadeGood_countKernel hb]
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
  apply markedBlockProbability_count_map _ (measurable_of_countable _) hj
  · intro nf hnf
    obtain ⟨s,hs',rfl⟩ := List.mem_map.mp hnf
    exact cascadeVisitCount_pos n _ (s.bare_valid n (hv s hs'))
  · intro nf hnf
    obtain ⟨s,hs',rfl⟩ := List.mem_map.mp hnf
    exact (decoratedShapeProbability_measurable ν step hs n _ _ (fun i => hF i.succ) s (hv s hs')).comp
      ((hs.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)

lemma indexedShapeRoot_singleton (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hb : IndexedCascadeGood (n+1) p.2.1)
    (hc : ∀ i j, 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p i j)).toReal)
    (hj : Function.Injective (fun a => (indexedRootPoint ν step n z F p a).1))
    (s : DecoratedVisitShape X n) (hv : s.Valid n) :
    decoratedShapeProbability ν step (n+1) z F [s] (p.1,indexedCascadeRealize (n+1) p.2) =
      ∑' a, (indexedBranchProbability step n F p a)^(cascadeVisitCount n (s.bare n))*
        decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ) s
          ((indexedChildPoint step n p a.1 a.2.val).1,
            indexedCascadeRealize n (indexedChildPoint step n p a.1 a.2.val).2) := by
  rw [indexedShapeRoot_counted ν step hs n z F hF p hb hj [s] (by simpa using hv)]
  simp only [List.map_cons,List.map_nil,countedBlockProbability,Fin.exists_fin_zero,
    ite_false,mul_one,indexedRootPoint_probability ν step hs n z F hF p hb hc]
  rfl

lemma indexedShapeRoot_pair (ν : ProbabilityMeasure S) (step : X×S → X)
    (hs : Measurable step) (n : ℕ) (z : Fin (n+1) → ℝ)
    (F : Fin (n+1) → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hb : IndexedCascadeGood (n+1) p.2.1)
    (hc : ∀ i j, 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p i j)).toReal)
    (hj : Function.Injective (fun a => (indexedRootPoint ν step n z F p a).1))
    (s t : DecoratedVisitShape X n) (hv : s.Valid n) (hw : t.Valid n) :
    decoratedShapeProbability ν step (n+1) z F [s,t] (p.1,indexedCascadeRealize (n+1) p.2) =
      ∑' a, (indexedBranchProbability step n F p a)^(cascadeVisitCount n (s.bare n))*
        decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ) s
          ((indexedChildPoint step n p a.1 a.2.val).1,
            indexedCascadeRealize n (indexedChildPoint step n p a.1 a.2.val).2)*
        ∑' b, if a=b then 0 else (indexedBranchProbability step n F p b)^(cascadeVisitCount n (t.bare n))*
          decoratedShapeProbability ν step n (fun i => z i.succ) (fun i => F i.succ) t
            ((indexedChildPoint step n p b.1 b.2.val).1,
              indexedCascadeRealize n (indexedChildPoint step n p b.1 b.2.val).2) := by
  classical
  rw [indexedShapeRoot_counted ν step hs n z F hF p hb hj [s,t] (by
    intro u hu; simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl|rfl <;> assumption)]
  simp only [List.map_cons,List.map_nil,countedBlockProbability,Fin.exists_fin_zero,
    ite_false,mul_one,indexedRootPoint_probability ν step hs n z F hF p hb hc,
    Fin.exists_fin_succ,Fin.cons_zero,or_false,hj.eq_iff]
  rfl

end SphericalPerceptronFreeEnergy

end

end OAI
