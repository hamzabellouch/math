import Mathlib
import OAI.Probability.Perceptron.Pressure.TerminalRestorationLaw
import OAI.Probability.Perceptron.Variational.TripleRootRegroup

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable (I J K : Type) [Fintype I] [Fintype J] [Fintype K]

abbrev TripleGaussianState := ((ℕ→EuclideanSpace ℝ I)×(ℕ→EuclideanSpace ℝ J))×(ℕ→EuclideanSpace ℝ K)
abbrev TripleGaussianMark := (EuclideanSpace ℝ I×EuclideanSpace ℝ J)×EuclideanSpace ℝ K
abbrev TripleGaussianData (k : ℕ) :=
  TripleGaussianMark I J K × (IndexedCascadeBase k×
    (IndexedCascadeMarks (EuclideanSpace ℝ I×EuclideanSpace ℝ J) k×IndexedCascadeMarks (EuclideanSpace ℝ K) k))

variable {I J K}
def tripleGaussianStep
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (B : ℕ→EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K) :
    TripleGaussianState I J K×TripleGaussianMark I J K→TripleGaussianState I J K :=
  fun p => ((gaussianLinearMarkStep A (p.1.1.1,p.2.1.1),
    gaussianLinearMarkStep B (p.1.1.2,p.2.1.2)),gaussianLinearMarkStep C (p.1.2,p.2.2))

lemma tripleGaussianStep_measurable
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (B : ℕ→EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K) : Measurable (tripleGaussianStep A B C) := by
  have ha := gaussianLinearMarkStep_measurable A
  have hb := gaussianLinearMarkStep_measurable B
  have hc := gaussianLinearMarkStep_measurable C
  unfold tripleGaussianStep
  fun_prop

def tripleGaussianTerminal
    (H : EuclideanSpace ℝ I→ℝ) (G : EuclideanSpace ℝ J→ℝ) (F : EuclideanSpace ℝ K→ℝ) :
    TripleGaussianState I J K→ℝ := fun x => (H (x.1.1 0)+G (x.1.2 0))+F (x.2 0)

def tripleGaussianObservable (f : EuclideanSpace ℝ I→ℝ) (g : EuclideanSpace ℝ J→ℝ) :
    TripleGaussianState I J K→ℝ := fun x => f (x.1.1 0)*g (x.1.2 0)

def tripleGaussianRoot
    (R : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (Q : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (T : EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K) :
    TripleGaussianMark I J K→TripleGaussianState I J K :=
  fun p => ((fun _ => R p.1.1,fun _ => Q p.1.2),fun _ => T p.2)

def tripleGaussianPair (k : ℕ)
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (B : ℕ→EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (R : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (Q : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (T : EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (H : EuclideanSpace ℝ I→ℝ) (G : EuclideanSpace ℝ J→ℝ) (F : EuclideanSpace ℝ K→ℝ)
    (d : Fin (k+1)) (f : EuclideanSpace ℝ I→ℝ) (g : EuclideanSpace ℝ J→ℝ)
    (p : TripleGaussianData I J K k) : ℝ :=
  indexedTerminalPairMean (tripleGaussianStep A B C) k (tripleGaussianTerminal H G F)
    (tripleGaussianRoot R Q T p.1) d (tripleGaussianObservable f g)
    (p.2.1,indexedMarksZip k p.2.2)

lemma tripleGaussianPair_measurable (k : ℕ)
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (B : ℕ→EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (R : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (Q : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (T : EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (H : EuclideanSpace ℝ I→ℝ) (G : EuclideanSpace ℝ J→ℝ) (F : EuclideanSpace ℝ K→ℝ)
    (hH : Measurable H) (hG : Measurable G) (hF : Measurable F)
    (d : Fin (k+1)) (f : EuclideanSpace ℝ I→ℝ) (g : EuclideanSpace ℝ J→ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (tripleGaussianPair k A B C R Q T H G F d f g) := by
  have ht : Measurable (tripleGaussianTerminal H G F) := by unfold tripleGaussianTerminal; fun_prop
  have ho : Measurable (tripleGaussianObservable (K:=K) f g) := by unfold tripleGaussianObservable; fun_prop
  have hr : Measurable (tripleGaussianRoot R Q T) := by unfold tripleGaussianRoot; fun_prop
  have hm := indexedTerminalPairMean_joint_measurable (tripleGaussianStep A B C)
    (tripleGaussianStep_measurable A B C) k (tripleGaussianTerminal H G F) ht d
    (tripleGaussianObservable f g) ho
  have hp : Measurable (fun p : TripleGaussianData I J K k =>
      (tripleGaussianRoot R Q T p.1,(p.2.1,indexedMarksZip k p.2.2))) :=
    (hr.comp measurable_fst).prodMk (measurable_snd.fst.prodMk
      ((indexedMarksZip_measurable k).comp measurable_snd.snd))
  have hc := hm.comp hp
  exact hc

theorem countable_three_terminal_pair_value (k : ℕ) (z : Fin k→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (B : ℕ→EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (R : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (Q : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (T : EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (H : EuclideanSpace ℝ I→ℝ) (G : EuclideanSpace ℝ J→ℝ) (F : EuclideanSpace ℝ K→ℝ)
    {L₁ L₂ L₀ : ℝ≥0} (hH : LipschitzWith L₁ H) (hG : LipschitzWith L₂ G) (hF : LipschitzWith L₀ F)
    (d : Fin (k+1)) (f : EuclideanSpace ℝ I→ℝ) (g : EuclideanSpace ℝ J→ℝ)
    (hf : Measurable f) (hg : Measurable g) (D E : ℝ) (hD : 0≤D) (hE : 0≤E)
    (hfB : ∀ x, |f x|≤D) (hgB : ∀ y, |g y|≤E) :
    (∫ t : IndexedCascadeBase k×(((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ)),
      tripleGaussianPair k A B C R Q T H G F d f g
        ((((indexedGaussianDisorder k I t.2.1.1).1,(indexedGaussianDisorder k J t.2.1.2).1),
          (indexedGaussianDisorder k K t.2.2).1),
         (t.1,(indexedMarksZip k ((indexedGaussianDisorder k I t.2.1.1).2,
           (indexedGaussianDisorder k J t.2.1.2).2),(indexedGaussianDisorder k K t.2.2).2)))
      ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        ((countableGaussianLaw.prod countableGaussianLaw).prod countableGaussianLaw)) =
      (twoVisitMass k z d).toReal *
        (rootPathCorrelation (stdGaussian (EuclideanSpace ℝ I)) (fun r => fun _ => R r) k
          (fun i => tiltedStateStep (gaussianMarkLaw (E:=EuclideanSpace ℝ I)) (gaussianLinearMarkStep A) (z i)
            (finiteCascadeShifts (gaussianMarkLaw (E:=EuclideanSpace ℝ I)) (gaussianLinearMarkStep A) k z (fun x => H (x 0)) i))
          (fun x => f (x 0)) d *
        rootPathCorrelation (stdGaussian (EuclideanSpace ℝ J)) (fun r => fun _ => Q r) k
          (fun i => tiltedStateStep (gaussianMarkLaw (E:=EuclideanSpace ℝ J)) (gaussianLinearMarkStep B) (z i)
            (finiteCascadeShifts (gaussianMarkLaw (E:=EuclideanSpace ℝ J)) (gaussianLinearMarkStep B) k z (fun x => G (x 0)) i))
          (fun x => g (x 0)) d) := by
  let : IsGaussian (gaussianMarkLaw (E:=EuclideanSpace ℝ I) : Measure (EuclideanSpace ℝ I)) := (inferInstance : IsGaussian (stdGaussian (EuclideanSpace ℝ I)))
  let : IsGaussian (gaussianMarkLaw (E:=EuclideanSpace ℝ J) : Measure (EuclideanSpace ℝ J)) := (inferInstance : IsGaussian (stdGaussian (EuclideanSpace ℝ J)))
  let : IsGaussian (gaussianMarkLaw (E:=EuclideanSpace ℝ K) : Measure (EuclideanSpace ℝ K)) := (inferInstance : IsGaussian (stdGaussian (EuclideanSpace ℝ K)))
  have hI := gaussianLinearRecursion_realization (gaussianMarkLaw (E:=EuclideanSpace ℝ I)) A hH k z hz0
  have hJ := gaussianLinearRecursion_realization (gaussianMarkLaw (E:=EuclideanSpace ℝ J)) B hG k z hz0
  have hK := gaussianLinearRecursion_realization (gaussianMarkLaw (E:=EuclideanSpace ℝ K)) C hF k z hz0
  have hv := indexedTerminalPairMean_two_fresh_old
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
    (by fun_prop) (by fun_prop) (by fun_prop) d (fun x => f (x 0)) (fun x => g (x 0))
    (hf.comp (measurable_pi_apply 0)) (hg.comp (measurable_pi_apply 0)) D E hD hE (fun x => hfB _) (fun x => hgB _)
  have hp := indexedGaussian_three_regroup_law k z I J K
  have hm := tripleGaussianPair_measurable k A B C R Q T H G F hH.continuous.measurable
    hG.continuous.measurable hF.continuous.measurable d f g hf hg
  have he := integral_map (μ:=(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        ((countableGaussianLaw.prod countableGaussianLaw).prod countableGaussianLaw))
    hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at he
  exact he.symm.trans hv

end SphericalPerceptronFreeEnergy
end

end OAI
