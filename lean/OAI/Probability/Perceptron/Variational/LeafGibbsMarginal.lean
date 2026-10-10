import Mathlib
import OAI.Probability.Perceptron.Variational.GaussianCoupling

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma tiltMean_prod_snd_of_partition {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) (ν : Measure T) [SFinite μ] [SFinite ν]
    (H : S×T→ℝ) (G F : T→ℝ) (hF : Measurable F) {B : ℝ} (hB : ∀ t, |F t|≤B)
    (he : Integrable (fun x => Real.exp (H x)) (μ.prod ν))
    (hp : ∀ t, (∫ s, Real.exp (H (s,t)) ∂μ)=Real.exp (G t)) :
    tiltMean (μ.prod ν) H (fun x => F x.2) 1=tiltMean ν G F 1 := by
  have hi : Integrable (fun x : S×T => F x.2*Real.exp (H x)) (μ.prod ν) :=
    he.bdd_mul (hF.comp measurable_snd).aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hB x.2)
  have hi' : Integrable (fun x : S×T => Real.exp (H x)*F x.2) (μ.prod ν) := by
    simpa only [mul_comm] using hi
  unfold tiltMean tiltIntegral tiltPartition
  simp only [one_mul]
  rw [integral_prod_symm _ hi',integral_prod_symm _ he]
  simp_rw [integral_mul_const,hp]

lemma enrichedIndexedHamiltonian_leaf_partition (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (g : ℕ→ℝ) (l : IndexedLeaf k) :
    (∫ x, Real.exp (enrichedIndexedHamiltonian n M k f a p d h u g (x,l)) ∂unitSphereLaw (n+1))=
      Real.exp (enrichedTerminal n M f a p u (h (Fin.last k))
        (indexedLeafState (gaussianLinearMarkStep (enrichedIncrementMap p d h)) k
          ((fun _ => enrichedRootMap p d h (indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) g).1),
            (indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) g).2) l 0)) := by
  let root := profileGaussianRoot (enrichedCoordinateLevel p d h)
  let step := profileGaussianStep (enrichedCoordinateLevel p d h)
  have hA : enrichedIncrementMap p d h = fun j => diagonalMark (step j) :=
    funext (enrichedIncrementMap_profile p d h)
  have hR : enrichedRootMap p d h = diagonalMark root := rfl
  rw [hA,hR]
  let v := indexedLeafState (gaussianLinearMarkStep (fun j => diagonalMark (step j))) k
    ((fun _ => diagonalMark root (indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) g).1),
      (indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) g).2) l 0
  have he (x : NormalizedSpin (n+1)) :
      enrichedIndexedHamiltonian n M k f a p d h u g (x,l)=
        normalizedPatternEnergy (n+1) M f a x+inner ℝ (sourceEnrichedFeature (n+1) p u x) v-
          (n+1:ℕ)*h (Fin.last k) := by
    unfold enrichedIndexedHamiltonian countableGaussianHamiltonian enrichedIndexedBoundedEnergy sourceGaussianRow
    rw [indexedGaussianRow_diagonal_identity]
    dsimp only [v,root,step]
    ring
  simp_rw [he]
  exact vectorPartition_exp_terminal (unitSphereLaw (n+1))
    ((normalizedPatternEnergy_continuous (n+1) M f).comp (continuous_const.prodMk continuous_id)).measurable
    (sourceEnrichedFeature_measurable (n+1) p u) (normalizedPatternEnergy_bound (n+1) M f a)
    (fun x => (sourceEnrichedFeature_norm (n+1) p u x).le) _ v

theorem enrichedIndexedHamiltonian_leaf_observable (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M→Fin (n+1)→ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (g : ℕ→ℝ) (b : IndexedCascadeBase k)
    (he : Integrable (fun x => Real.exp (enrichedIndexedHamiltonian n M k f a p d h u g x))
      (enrichedIndexedBaseMeasure n k b)) (F : IndexedLeaf k→ℝ) {B : ℝ} (hB : ∀ l, |F l|≤B) :
    tiltMean (enrichedIndexedBaseMeasure n k b) (enrichedIndexedHamiltonian n M k f a p d h u g)
      (fun x => F x.2) 1=
      tiltMean (indexedLeafProbability k b)
        (fun l => enrichedTerminal n M f a p u (h (Fin.last k))
          (indexedLeafState (gaussianLinearMarkStep (enrichedIncrementMap p d h)) k
            ((fun _ => enrichedRootMap p d h (indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) g).1),
              (indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) g).2) l 0)) F 1 := by
  exact tiltMean_prod_snd_of_partition _ _ _ _ F (measurable_of_countable _) hB he
    (enrichedIndexedHamiltonian_leaf_partition n M k f a p d h u g)

end SphericalPerceptronFreeEnergy
end

end OAI
