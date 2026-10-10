import Mathlib
import OAI.Probability.Perceptron.Interpolation.TripleGaussianReplica
import OAI.Probability.Perceptron.Variational.SingleRestorationLaw

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

def tripleGaussianMean (k : ℕ)
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (B : ℕ→EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (R : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (Q : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (T : EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (H : EuclideanSpace ℝ I→ℝ) (G : EuclideanSpace ℝ J→ℝ) (F : EuclideanSpace ℝ K→ℝ)
    (f : EuclideanSpace ℝ I→ℝ) (g : EuclideanSpace ℝ J→ℝ)
    (p : TripleGaussianData I J K k) : ℝ :=
  indexedTerminalMean (tripleGaussianStep A B C) k (tripleGaussianTerminal H G F)
    (tripleGaussianRoot R Q T p.1) (tripleGaussianObservable f g)
    (p.2.1,indexedMarksZip k p.2.2)

lemma tripleGaussianMean_measurable (k : ℕ)
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (B : ℕ→EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (R : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (Q : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (T : EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (H : EuclideanSpace ℝ I→ℝ) (G : EuclideanSpace ℝ J→ℝ) (F : EuclideanSpace ℝ K→ℝ)
    (hH : Measurable H) (hG : Measurable G) (hF : Measurable F)
    (f : EuclideanSpace ℝ I→ℝ) (g : EuclideanSpace ℝ J→ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (tripleGaussianMean k A B C R Q T H G F f g) := by
  have ht : Measurable (tripleGaussianTerminal H G F) := by unfold tripleGaussianTerminal; fun_prop
  have ho : Measurable (tripleGaussianObservable (K:=K) f g) := by unfold tripleGaussianObservable; fun_prop
  have hr : Measurable (tripleGaussianRoot R Q T) := by unfold tripleGaussianRoot; fun_prop
  have hm := indexedTerminalMean_joint_measurable (tripleGaussianStep A B C)
    (tripleGaussianStep_measurable A B C) k (tripleGaussianTerminal H G F) ht
    (tripleGaussianObservable f g) ho
  have hp : Measurable (fun p : TripleGaussianData I J K k =>
      (tripleGaussianRoot R Q T p.1,(p.2.1,indexedMarksZip k p.2.2))) :=
    (hr.comp measurable_fst).prodMk (measurable_snd.fst.prodMk
      ((indexedMarksZip_measurable k).comp measurable_snd.snd))
  have hc := hm.comp hp
  exact hc

theorem countable_three_terminal_single_value (k : ℕ) (z : Fin k→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (B : ℕ→EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (R : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (Q : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (T : EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (H : EuclideanSpace ℝ I→ℝ) (G : EuclideanSpace ℝ J→ℝ) (F : EuclideanSpace ℝ K→ℝ)
    {L₁ L₂ L₀ : ℝ≥0} (hH : LipschitzWith L₁ H) (hG : LipschitzWith L₂ G) (hF : LipschitzWith L₀ F)
    (f : EuclideanSpace ℝ I→ℝ) (g : EuclideanSpace ℝ J→ℝ)
    (hf : Measurable f) (hg : Measurable g) (D E : ℝ) (hD : 0≤D) (hE : 0≤E)
    (hfB : ∀ x, |f x|≤D) (hgB : ∀ y, |g y|≤E) :
    (∫ t : IndexedCascadeBase k×(((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ)),
      tripleGaussianMean k A B C R Q T H G F f g
        ((((indexedGaussianDisorder k I t.2.1.1).1,(indexedGaussianDisorder k J t.2.1.2).1),
          (indexedGaussianDisorder k K t.2.2).1),
         (t.1,(indexedMarksZip k ((indexedGaussianDisorder k I t.2.1.1).2,
           (indexedGaussianDisorder k J t.2.1.2).2),(indexedGaussianDisorder k K t.2.2).2)))
      ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        ((countableGaussianLaw.prod countableGaussianLaw).prod countableGaussianLaw)) =
      (rootPathMean (stdGaussian (EuclideanSpace ℝ I)) (fun r => fun _ => R r) k
          (fun i => tiltedStateStep (gaussianMarkLaw (E:=EuclideanSpace ℝ I)) (gaussianLinearMarkStep A) (z i)
            (finiteCascadeShifts (gaussianMarkLaw (E:=EuclideanSpace ℝ I)) (gaussianLinearMarkStep A) k z (fun x => H (x 0)) i))
          (fun x => f (x 0)) *
        rootPathMean (stdGaussian (EuclideanSpace ℝ J)) (fun r => fun _ => Q r) k
          (fun i => tiltedStateStep (gaussianMarkLaw (E:=EuclideanSpace ℝ J)) (gaussianLinearMarkStep B) (z i)
            (finiteCascadeShifts (gaussianMarkLaw (E:=EuclideanSpace ℝ J)) (gaussianLinearMarkStep B) k z (fun x => G (x 0)) i))
          (fun x => g (x 0))) := by
  let : IsGaussian (gaussianMarkLaw (E:=EuclideanSpace ℝ I) : Measure (EuclideanSpace ℝ I)) := (inferInstance : IsGaussian (stdGaussian (EuclideanSpace ℝ I)))
  let : IsGaussian (gaussianMarkLaw (E:=EuclideanSpace ℝ J) : Measure (EuclideanSpace ℝ J)) := (inferInstance : IsGaussian (stdGaussian (EuclideanSpace ℝ J)))
  let : IsGaussian (gaussianMarkLaw (E:=EuclideanSpace ℝ K) : Measure (EuclideanSpace ℝ K)) := (inferInstance : IsGaussian (stdGaussian (EuclideanSpace ℝ K)))
  have hI := gaussianLinearRecursion_realization (gaussianMarkLaw (E:=EuclideanSpace ℝ I)) A hH k z hz0
  have hJ := gaussianLinearRecursion_realization (gaussianMarkLaw (E:=EuclideanSpace ℝ J)) B hG k z hz0
  have hK := gaussianLinearRecursion_realization (gaussianMarkLaw (E:=EuclideanSpace ℝ K)) C hF k z hz0
  have hv := indexedTerminalMean_two_fresh_old
    (gaussianMarkLaw (E:=EuclideanSpace ℝ I)) (gaussianMarkLaw (E:=EuclideanSpace ℝ J))
    (gaussianMarkLaw (E:=EuclideanSpace ℝ K))
    (gaussianMarkLaw (E:=EuclideanSpace ℝ I)) (gaussianMarkLaw (E:=EuclideanSpace ℝ J))
    (gaussianMarkLaw (E:=EuclideanSpace ℝ K))
    (gaussianLinearMarkStep A) (gaussianLinearMarkStep B) (gaussianLinearMarkStep C)
    (gaussianLinearMarkStep_measurable A) (gaussianLinearMarkStep_measurable B) (gaussianLinearMarkStep_measurable C)
    k z hz hz0 hz1 (fun x => H (x 0)) (fun x => G (x 0)) (fun x => F (x 0))
    (hH.continuous.measurable.comp (measurable_pi_apply 0))
    (hG.continuous.measurable.comp (measurable_pi_apply 0))
    (hF.continuous.measurable.comp (measurable_pi_apply 0)) hI.2 hJ.2 hK.2
    (fun r => fun _ => R r) (fun r => fun _ => Q r) (fun r => fun _ => T r)
    (by fun_prop) (by fun_prop) (by fun_prop) (fun x => f (x 0)) (fun x => g (x 0))
    (hf.comp (measurable_pi_apply 0)) (hg.comp (measurable_pi_apply 0)) D E hD hE (fun x => hfB _) (fun x => hgB _)
  have hp := indexedGaussian_three_regroup_law k z I J K
  have hm := tripleGaussianMean_measurable k A B C R Q T H G F hH.continuous.measurable
    hG.continuous.measurable hF.continuous.measurable f g hf hg
  have he := integral_map (μ:=(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        ((countableGaussianLaw.prod countableGaussianLaw).prod countableGaussianLaw))
    hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at he
  exact he.symm.trans hv


lemma tripleGaussianMean_replica (k : ℕ)
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (B : ℕ→EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (R : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (Q : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (T : EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (H : EuclideanSpace ℝ I→ℝ) (G : EuclideanSpace ℝ J→ℝ) (F : EuclideanSpace ℝ K→ℝ)
    (hH : Measurable H) (hG : Measurable G) (hF : Measurable F)
    (f : EuclideanSpace ℝ I→ℝ) (g : EuclideanSpace ℝ J→ℝ)
    (b : IndexedCascadeBase k) (t : ((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ))
    (hi : Integrable (fun l => Real.exp ((H (gaussianLeafValue k A R t.1.1 l)+
      G (gaussianLeafValue k B Q t.1.2 l))+F (gaussianLeafValue k C T t.2 l))) (indexedLeafProbability k b)) :
    tripleGaussianMean k A B C R Q T H G F f g (tripleGaussianCountableData (I:=I) (J:=J) (K:=K) k b t) =
      gibbsReplicaMean (indexedLeafProbability k b)
        (fun l => (H (gaussianLeafValue k A R t.1.1 l)+G (gaussianLeafValue k B Q t.1.2 l))+
          F (gaussianLeafValue k C T t.2 l)) 1
        (fun l => f (gaussianLeafValue k A R t.1.1 (l 0))*g (gaussianLeafValue k B Q t.1.2 (l 0))) := by
  have ht : Measurable (tripleGaussianTerminal H G F) := by unfold tripleGaussianTerminal; fun_prop
  unfold tripleGaussianMean
  have he := indexedTerminalMean_tiltMean (tripleGaussianStep A B C) (tripleGaussianStep_measurable A B C)
    k (tripleGaussianTerminal H G F) ht
    (tripleGaussianRoot R Q T (tripleGaussianCountableData (I:=I) (J:=J) (K:=K) k b t).1) (tripleGaussianObservable f g)
    ((tripleGaussianCountableData (I:=I) (J:=J) (K:=K) k b t).2.1,indexedMarksZip k (tripleGaussianCountableData (I:=I) (J:=J) (K:=K) k b t).2.2)
  have hstate (l : IndexedLeaf k) := tripleGaussianLeafState k A B C
    (fun _ => R (indexedGaussianDisorder k I t.1.1).1)
    (fun _ => Q (indexedGaussianDisorder k J t.1.2).1)
    (fun _ => T (indexedGaussianDisorder k K t.2).1)
    (indexedGaussianDisorder k I t.1.1).2 (indexedGaussianDisorder k J t.1.2).2
    (indexedGaussianDisorder k K t.2).2 l
  simp only [tripleGaussianCountableData,tripleGaussianRoot] at he ⊢
  simp only [tripleGaussianTerminal,hstate] at he
  have hv := he hi
  simp only [tripleGaussianObservable] at hv
  rw [hv]
  symm
  refine (gibbsReplicaMean_coordinate_of_integrable (indexedLeafProbability k b)
    (F:=fun l => f (gaussianLeafValue k A R t.1.1 l)*g (gaussianLeafValue k B Q t.1.2 l))
    (measurable_of_countable _) (measurable_of_countable _) hi 1 0).trans ?_
  congr 1
  funext l
  simp only [indexedTerminalEnergy,tripleGaussianTerminal,hstate,gaussianLeafValue]

end SphericalPerceptronFreeEnergy
end

end OAI
