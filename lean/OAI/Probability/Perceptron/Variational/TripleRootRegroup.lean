import Mathlib
import OAI.Probability.Perceptron.Cavity.LeafFreshLog

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma indexedGaussian_pair_zip_law (k : ℕ) (I J : Type) [Fintype I] [Fintype J] :
    MeasurePreserving (fun t : (ℕ→ℝ)×(ℕ→ℝ) =>
      (((indexedGaussianDisorder k I t.1).1,(indexedGaussianDisorder k J t.2).1),
        indexedMarksZip k ((indexedGaussianDisorder k I t.1).2,(indexedGaussianDisorder k J t.2).2)))
      (countableGaussianLaw.prod countableGaussianLaw)
      (((stdGaussian (EuclideanSpace ℝ I)).prod (stdGaussian (EuclideanSpace ℝ J))).prod
        (indexedCascadeMarksLaw
          (productMarkLaw (gaussianMarkLaw (E:=EuclideanSpace ℝ I))
            (gaussianMarkLaw (E:=EuclideanSpace ℝ J))) k)) := by
  have hI : MeasurePreserving (indexedGaussianDisorder k I) countableGaussianLaw
      ((stdGaussian (EuclideanSpace ℝ I)).prod
        (indexedCascadeMarksLaw (gaussianMarkLaw (E := EuclideanSpace ℝ I)) k)) :=
    ⟨indexedGaussianDisorder_measurable k I,indexedGaussianDisorder_law k I⟩
  have hJ : MeasurePreserving (indexedGaussianDisorder k J) countableGaussianLaw
      ((stdGaussian (EuclideanSpace ℝ J)).prod
        (indexedCascadeMarksLaw (gaussianMarkLaw (E := EuclideanSpace ℝ J)) k)) :=
    ⟨indexedGaussianDisorder_measurable k J,indexedGaussianDisorder_law k J⟩
  have hz : MeasurePreserving (indexedMarksZip (S:=EuclideanSpace ℝ I) (T:=EuclideanSpace ℝ J) k)
      ((indexedCascadeMarksLaw (gaussianMarkLaw (E:=EuclideanSpace ℝ I)) k : Measure _).prod
        (indexedCascadeMarksLaw (gaussianMarkLaw (E:=EuclideanSpace ℝ J)) k))
      (indexedCascadeMarksLaw (productMarkLaw (gaussianMarkLaw (E:=EuclideanSpace ℝ I))
        (gaussianMarkLaw (E:=EuclideanSpace ℝ J))) k) :=
    ⟨indexedMarksZip_measurable k,indexedMarksZip_law _ _ k⟩
  exact ((MeasurePreserving.id _).prod hz).comp
    ((freshRoot_four_shuffle _ _ _ _).comp (hI.prod hJ))

lemma indexedGaussian_three_regroup_law (k : ℕ) (z : Fin k→ℝ)
    (I J K : Type) [Fintype I] [Fintype J] [Fintype K] :
    MeasurePreserving
      (fun t : IndexedCascadeBase k×(((ℕ→ℝ)×(ℕ→ℝ))×(ℕ→ℝ)) =>
        ((((indexedGaussianDisorder k I t.2.1.1).1,(indexedGaussianDisorder k J t.2.1.2).1),
          (indexedGaussianDisorder k K t.2.2).1),
         (t.1,(indexedMarksZip k ((indexedGaussianDisorder k I t.2.1.1).2,
           (indexedGaussianDisorder k J t.2.1.2).2),(indexedGaussianDisorder k K t.2.2).2))))
      ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
        ((countableGaussianLaw.prod countableGaussianLaw).prod countableGaussianLaw))
      ((((stdGaussian (EuclideanSpace ℝ I)).prod (stdGaussian (EuclideanSpace ℝ J))).prod
        (stdGaussian (EuclideanSpace ℝ K))).prod
        ((indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod
          ((indexedCascadeMarksLaw
              (productMarkLaw (gaussianMarkLaw (E:=EuclideanSpace ℝ I))
                (gaussianMarkLaw (E:=EuclideanSpace ℝ J))) k :
              Measure (IndexedCascadeMarks (EuclideanSpace ℝ I×EuclideanSpace ℝ J) k)).prod
            (indexedCascadeMarksLaw (gaussianMarkLaw (E:=EuclideanSpace ℝ K)) k)))) := by
  have hK : MeasurePreserving (indexedGaussianDisorder k K) countableGaussianLaw
      ((stdGaussian (EuclideanSpace ℝ K)).prod
        (indexedCascadeMarksLaw (gaussianMarkLaw (E := EuclideanSpace ℝ K)) k)) :=
    ⟨indexedGaussianDisorder_measurable k K,indexedGaussianDisorder_law k K⟩
  exact (freshRoot_five_regroup _ _ _ _ _).comp
    ((MeasurePreserving.id (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k))).prod
      ((indexedGaussian_pair_zip_law k I J).prod hK))

end SphericalPerceptronFreeEnergy
end

end OAI
