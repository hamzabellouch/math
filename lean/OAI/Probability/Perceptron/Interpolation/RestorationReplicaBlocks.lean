import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkModel
import OAI.Probability.Perceptron.Variational.RestorationMoments

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def restorationBlockTest (r : ℕ) (F : CompactBlock CompactOverlap r→ᵇℝ) :
    (k : ℕ) → CompactBlock CompactOverlap (r+k)→ᵇℝ
  | 0 => F
  | k+1 => (restorationBlockTest r F k).compContinuous
      ⟨fun Q i j => Q i.succ j.succ,by fun_prop⟩

def restorationMarkTest (r : ℕ) (f : ℝ→ᵇℝ) (Ψ : EuclideanSpace ℝ (Fin r)→ᵇℝ) :
    (k : ℕ) → EuclideanSpace ℝ (Fin (r+k))→ᵇℝ
  | 0 => gaussianReplicaTest (expBCF 1 f)*Ψ
  | k+1 => ((expBCF 1 f).compContinuous ⟨fun x => x 0,by fun_prop⟩)*
      (restorationMarkTest r f Ψ k).compContinuous
        ⟨fun x => WithLp.toLp 2 (fun i => x i.succ),by fun_prop⟩

lemma restorationReplicaTest_twoMarks {N r : ℕ} (f : ℝ→ᵇℝ)
    (F : CompactBlock CompactOverlap r→ᵇℝ) (Ψ Φ : EuclideanSpace ℝ (Fin r)→ᵇℝ)
    (z₁ z₂ : EuclideanSpace ℝ (Fin N)) (k : ℕ) (x : Fin (r+k)→NormalizedSpin N) :
    restorationReplicaTest r (fun x : NormalizedSpin N => Real.exp (f (inner ℝ x.val z₁)+f (inner ℝ x.val z₂)))
      (fun x => (∏ i, Real.exp (f (inner ℝ (x i).val z₁)+f (inner ℝ (x i).val z₂)))*
        F (fun i j => bulkOverlap (x i) (x j))*Ψ (gaussianRows (fun i => (x i).val) z₁)*
          Φ (gaussianRows (fun i => (x i).val) z₂)) k x =
      restorationBlockTest r F k (fun i j => bulkOverlap (x i) (x j))*
        restorationMarkTest r f Ψ k (gaussianRows (fun i => (x i).val) z₁)*
        restorationMarkTest r f Φ k (gaussianRows (fun i => (x i).val) z₂) := by
  induction k with
  | zero =>
    simp only [restorationReplicaTest,restorationBlockTest,restorationMarkTest,
      BoundedContinuousFunction.mul_apply, gaussianReplicaTest, BoundedContinuousFunction.prod_apply,
      BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk, expBCF_apply,one_mul,
      gaussianRows_apply,Real.exp_add,Finset.prod_mul_distrib]
    ring_nf
    rfl
  | succ k hk =>
    change Real.exp (f (inner ℝ (x 0).val z₁)+f (inner ℝ (x 0).val z₂))*
      restorationReplicaTest r _ _ k (fun i => x i.succ) = _
    rw [hk,Real.exp_add]
    change Real.exp (f (inner ℝ (x 0).val z₁))*Real.exp (f (inner ℝ (x 0).val z₂))*
      (restorationBlockTest r F k (fun i j => bulkOverlap (x i.succ) (x j.succ))*
        restorationMarkTest r f Ψ k (gaussianRows (fun i => (x i.succ).val) z₁)*
        restorationMarkTest r f Φ k (gaussianRows (fun i => (x i.succ).val) z₂)) =
      restorationBlockTest r F k (fun i j => bulkOverlap (x i.succ) (x j.succ))*
        (Real.exp (1*f (inner ℝ (x 0).val z₁))*restorationMarkTest r f Ψ k
          (gaussianRows (fun i => (x i.succ).val) z₁))*
        (Real.exp (1*f (inner ℝ (x 0).val z₂))*restorationMarkTest r f Φ k
          (gaussianRows (fun i => (x i.succ).val) z₂))
    simp only [one_mul]
    ring

end SphericalPerceptronFreeEnergy
end

end OAI
