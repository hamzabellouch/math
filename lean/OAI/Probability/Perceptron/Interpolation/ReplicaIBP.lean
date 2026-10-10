import Mathlib
import OAI.Probability.Perceptron.Variational.GaussianCoupling
import OAI.Probability.Perceptron.Variational.IndexedGaussianCovariance
import OAI.Probability.Perceptron.Variational.CountableGaussianFullIBP

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceGaussianTestRow_measurable {N k : ℕ} (p d : Fin N → ℕ)
    (h : Fin (k+1) → ℝ) (j : Fin N) (i : ℕ) :
    Measurable (sourceGaussianTestRow p d h j i) :=
  indexedGaussianRow_measurable _ _ (enrichedFeature_continuous _ _ _ _ _).measurable i

lemma sourceGaussianTestRow_square_bound {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) {H : ℝ} (hH : 0 ≤ H) (hhH : ∀ l, h l ≤ H)
    (j : Fin N) (x : NormalizedSpin N×IndexedLeaf k) :
    (∑ i : Fin (indexedGaussianRowLength (I := EnrichedIndex N N p) k x),
      sourceGaussianTestRow p d h j i.val x^2) ≤ 2*H+1 := by
  have hb (y : NormalizedSpin N) : (∑ i, sourceGaussianTestFeature N p j y i^2) ≤ (1:ℝ) := by
    have he := enrichedFeature_norm_sq N N p 0 (Pi.single j 1) y
    have hsum : (∑ i : Fin N, ((Pi.single j (1:ℝ) : Fin N → ℝ) i)^2) = (1:ℝ) := by
      classical
      simp [Pi.single_apply]
    simp only [zero_pow (by decide : (2:ℕ) ≠ 0),zero_add,hsum] at he
    simpa only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,sourceGaussianTestFeature] using he.le
  have ht := indexedGaussianRow_norm_le k
    (hierarchyRowCoefficients k (profileGaussianRoot (enrichedCoordinateLevel p d h))
      (profileGaussianStep (enrichedCoordinateLevel p d h))) (sourceGaussianTestFeature N p j)
    (C := 2*H+1) (D := 1)
    (fun i => by
      rw [profileGaussian_coefficient_squares _ (enrichedCoordinateLevel_nonneg p d hh0 0)
        (enrichedCoordinateLevel_monotone p d hh)]
      exact enrichedCoordinateLevel_le p d hH hhH _ i)
    (by positivity) hb x
  simpa only [mul_one,sourceGaussianTestRow] using ht

def sourceJointMonomial {N k : ℕ} (p d : Fin N → ℕ) (j : Fin N)
    (x y : NormalizedSpin N×IndexedLeaf k) : ℝ :=
  (((indexedCommonDepth k y.2 x.2).val:ℝ)/(k+1:ℕ))^(d j)*spinOverlap x.1 y.1^(p j)

lemma sourceJointMonomial_diagonal {N k : ℕ} (p d : Fin N → ℕ) (j : Fin N)
    (x : NormalizedSpin N×IndexedLeaf k) :
    sourceJointMonomial p d j x x = ((k:ℝ)/(k+1:ℕ))^(d j) := by
  have hx : ‖x.1.val‖=1 := by simp
  simp [sourceJointMonomial,indexedCommonDepth_self,spinOverlap,hx]

lemma sourceReplica_gaussian_ibp (n M k r : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h)
    (u : Fin (n+1) → ℝ) (b : IndexedCascadeBase k) (j : Fin (n+1)) (z : Fin r)
    {G : (Fin r → NormalizedSpin (n+1)×IndexedLeaf k) → ℝ}
    (hG : Measurable G) {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    let μ := enrichedIndexedBaseMeasure n k b
    let H := enrichedIndexedHamiltonian n M k f a p d h u
    let Y := countableGaussianField (sourceGaussianTestRow p d h j)
      (indexedGaussianRowLength (I := EnrichedIndex (n+1) (n+1) p) k)
    (∫ g, gibbsReplicaMean μ (H g) r (fun x => Y g (x z)*G x) ∂countableGaussianLaw) =
      ∫ g, gibbsReplicaMean μ (H g) r (fun x => G x*∑ l,
        perturbationAmplitude (n+1) u j*sourceJointMonomial p d j (x z) (x l)) -
        r*gibbsReplicaMean μ (H g) (r+1) (fun x => G (fun l => x l.succ)*
          (perturbationAmplitude (n+1) u j*sourceJointMonomial p d j (x z.succ) (x 0)))
        ∂countableGaussianLaw := by
  dsimp only
  have ht : ∀ l, h l ≤ h (Fin.last k) := fun l => hh (Fin.le_last l)
  have hi := countableGaussian_replica_full_ibp (enrichedIndexedBaseMeasure n k b) r z
    (enrichedIndexedBoundedEnergy_measurable n M k f a h)
    (sourceGaussianRow_measurable p d h u) (sourceGaussianTestRow_measurable p d h j)
    (indexedGaussianRowLength_measurable k) hG
    (enrichedIndexedBoundedEnergy_bound n M k f a h)
    (sourceGaussianRow_square_bound p d h u hh0 hh (hh0 (Fin.last k)) ht)
    (sourceGaussianTestRow_square_bound p d h hh0 hh (hh0 (Fin.last k)) ht j) hB hGB
  dsimp only at hi
  simpa only [sourceGaussianRow_test_covariance p d h hh0 hh u j,mul_assoc,
    sourceJointMonomial,enrichedIndexedHamiltonian] using hi

end SphericalPerceptronFreeEnergy
end

end OAI
