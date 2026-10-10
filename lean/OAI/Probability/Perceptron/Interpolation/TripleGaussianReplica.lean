import Mathlib
import OAI.Probability.Perceptron.Interpolation.TerminalReplicaRestoration
import OAI.Probability.Perceptron.Pressure.CountableTerminalRestoration

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace SphericalPerceptronFreeEnergy
variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

def gaussianLeafValue (k : ℕ)
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (R : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I) (g : ℕ→ℝ) (l : IndexedLeaf k) : EuclideanSpace ℝ I :=
  indexedLeafState (gaussianLinearMarkStep A) k
    ((fun _ => R (indexedGaussianDisorder k I g).1),(indexedGaussianDisorder k I g).2) l 0

def tripleGaussianCountableData (k : ℕ) (b : IndexedCascadeBase k)
    (t : ((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ)) : TripleGaussianData I J K k :=
  ((((indexedGaussianDisorder k I t.1.1).1,(indexedGaussianDisorder k J t.1.2).1),
    (indexedGaussianDisorder k K t.2).1),
    (b,(indexedMarksZip k ((indexedGaussianDisorder k I t.1.1).2,
      (indexedGaussianDisorder k J t.1.2).2),(indexedGaussianDisorder k K t.2).2)))

lemma tripleGaussianLeafState (k : ℕ)
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (B : ℕ→EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (x : ℕ→EuclideanSpace ℝ I) (y : ℕ→EuclideanSpace ℝ J) (z : ℕ→EuclideanSpace ℝ K)
    (a : IndexedCascadeMarks (EuclideanSpace ℝ I) k) (b : IndexedCascadeMarks (EuclideanSpace ℝ J) k)
    (c : IndexedCascadeMarks (EuclideanSpace ℝ K) k) (l : IndexedLeaf k) :
    indexedLeafState (tripleGaussianStep A B C) k (((x,y),z),indexedMarksZip k (indexedMarksZip k (a,b),c)) l =
      ((indexedLeafState (gaussianLinearMarkStep A) k (x,a) l,
        indexedLeafState (gaussianLinearMarkStep B) k (y,b) l),
        indexedLeafState (gaussianLinearMarkStep C) k (z,c) l) := by
  have he := indexedLeafState_product
    (fun p : ((ℕ→EuclideanSpace ℝ I)×(ℕ→EuclideanSpace ℝ J))×
      (EuclideanSpace ℝ I×EuclideanSpace ℝ J) =>
      (gaussianLinearMarkStep A (p.1.1,p.2.1),gaussianLinearMarkStep B (p.1.2,p.2.2)))
    (gaussianLinearMarkStep C) k (x,y) z (indexedMarksZip k (a,b)) c l
  rw [indexedLeafState_product] at he
  exact he

lemma tripleGaussianPair_replica (k : ℕ)
    (A : ℕ→EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (B : ℕ→EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (C : ℕ→EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (R : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)
    (Q : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J)
    (T : EuclideanSpace ℝ K →L[ℝ] EuclideanSpace ℝ K)
    (H : EuclideanSpace ℝ I→ℝ) (G : EuclideanSpace ℝ J→ℝ) (F : EuclideanSpace ℝ K→ℝ)
    (hH : Measurable H) (hG : Measurable G) (hF : Measurable F)
    (d : Fin (k+1)) (f : EuclideanSpace ℝ I→ℝ) (g : EuclideanSpace ℝ J→ℝ)
    (b : IndexedCascadeBase k) (t : ((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ))
    (hi : Integrable (fun l => Real.exp ((H (gaussianLeafValue k A R t.1.1 l)+
      G (gaussianLeafValue k B Q t.1.2 l))+F (gaussianLeafValue k C T t.2 l))) (indexedLeafProbability k b)) :
    tripleGaussianPair k A B C R Q T H G F d f g (tripleGaussianCountableData (I:=I) (J:=J) (K:=K) k b t) =
      gibbsReplicaMean (indexedLeafProbability k b)
        (fun l => (H (gaussianLeafValue k A R t.1.1 l)+G (gaussianLeafValue k B Q t.1.2 l))+
          F (gaussianLeafValue k C T t.2 l)) 2
        (fun l => if indexedCommonDepth k (l 0) (l 1)=d then
          (f (gaussianLeafValue k A R t.1.1 (l 0))*g (gaussianLeafValue k B Q t.1.2 (l 0)))*
          (f (gaussianLeafValue k A R t.1.1 (l 1))*g (gaussianLeafValue k B Q t.1.2 (l 1))) else 0) := by
  have ht : Measurable (tripleGaussianTerminal H G F) := by unfold tripleGaussianTerminal; fun_prop
  unfold tripleGaussianPair
  have he := indexedTerminalPairMean_replica (tripleGaussianStep A B C) (tripleGaussianStep_measurable A B C)
    k (tripleGaussianTerminal H G F) ht
    (tripleGaussianRoot R Q T (tripleGaussianCountableData (I:=I) (J:=J) (K:=K) k b t).1) d (tripleGaussianObservable f g)
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
  congr 1
  funext l
  simp only [indexedTerminalEnergy,tripleGaussianTerminal,hstate,gaussianLeafValue]

end SphericalPerceptronFreeEnergy
end

end OAI
