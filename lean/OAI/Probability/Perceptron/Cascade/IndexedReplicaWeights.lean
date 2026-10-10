import Mathlib
import OAI.Probability.Perceptron.Cascade.IndexedTiltedWeights

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma indexedLeaf_tsum_active (n : ℕ) (b : IndexedCascadeBase (n+1))
    (f : IndexedLeaf (n+1) → ℝ≥0∞)
    (hf : ∀ i j, ¬j<(b i).1 → ∀ l : IndexedLeaf n, f (i,j,l)=0) :
    (∑' l, f l) = ∑' a : Σ i, Fin ((b i).1), ∑' l : IndexedLeaf n, f (a.1,a.2.val,l) := by
  change (∑' l : ℕ×ℕ×IndexedLeaf n, f l) = _
  rw [ENNReal.tsum_prod',ENNReal.tsum_sigma']
  apply tsum_congr
  intro i
  rw [ENNReal.tsum_prod']
  conv_rhs => rw [tsum_fintype]
  rw [tsum_eq_sum (s := Finset.range ((b i).1)) (fun j hj => by
    simp only [hf i j (Finset.mem_range.not.mp hj),tsum_zero])]
  exact (Fin.sum_univ_eq_sum_range (fun j => ∑' l : IndexedLeaf n, f (i,j,l)) _).symm

variable {X S : Type} [MeasurableSpace S]

lemma indexedTiltedProbability_active (step : X×S → X) (n : ℕ)
    (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (a : Σ i, Fin ((p.2.1 i).1))
    (hc : 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p a.1 a.2.val)).toReal) (l : IndexedLeaf n) :
    indexedTiltedProbability step (n+1) F p (a.1,a.2.val,l) =
      indexedBranchProbability step n F p a * indexedTiltedProbability step n (fun i => F i.succ)
        (indexedChildPoint step n p a.1 a.2.val) l := by
  rw [indexedTiltedProbability,indexedTiltedWeight_succ,ite_eq_left a.2.isLt]
  simp only [indexedBranchProbability,indexedBranchWeight,indexedTiltedProbability]
  rw [show (indexedTiltedTotal step (n+1) F p)⁻¹ *
      (ENNReal.ofReal (Real.exp (((p.2.1 a.1).2 a.2.val).1+F 0 (p.1,(p.2.2 a.1 a.2.val).1)))*
        indexedTiltedTotal step n (fun i => F i.succ) (indexedChildPoint step n p a.1 a.2.val)) *
      ((indexedTiltedTotal step n (fun i => F i.succ) (indexedChildPoint step n p a.1 a.2.val))⁻¹ *
        indexedTiltedWeight step n (fun i => F i.succ) (indexedChildPoint step n p a.1 a.2.val) l) =
      (indexedTiltedTotal step (n+1) F p)⁻¹ *
      (ENNReal.ofReal (Real.exp (((p.2.1 a.1).2 a.2.val).1+F 0 (p.1,(p.2.2 a.1 a.2.val).1)))*
        ((indexedTiltedTotal step n (fun i => F i.succ) (indexedChildPoint step n p a.1 a.2.val))*
          (indexedTiltedTotal step n (fun i => F i.succ) (indexedChildPoint step n p a.1 a.2.val))⁻¹)*
        indexedTiltedWeight step n (fun i => F i.succ) (indexedChildPoint step n p a.1 a.2.val) l) by ac_rfl,
    ENNReal.mul_inv_cancel (ENNReal.toReal_pos_iff.mp hc).1.ne' (ENNReal.toReal_pos_iff.mp hc).2.ne,
    mul_one]
  rfl

lemma indexedTiltedProbability_inactive (step : X×S → X) (n : ℕ)
    (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (i j : ℕ) (hj : ¬j<(p.2.1 i).1) (l : IndexedLeaf n) :
    indexedTiltedProbability step (n+1) F p (i,j,l) = 0 := by
  simp [indexedTiltedProbability,indexedTiltedWeight_succ,hj]

lemma indexedTiltedProbability_tsum_succ (step : X×S → X) (n : ℕ)
    (F : Fin (n+1) → X×S → ℝ)
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hc : ∀ i j, 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p i j)).toReal) (f : IndexedLeaf (n+1) → ℝ≥0∞) :
    (∑' l, indexedTiltedProbability step (n+1) F p l*f l) =
      ∑' a : Σ i, Fin ((p.2.1 i).1), indexedBranchProbability step n F p a *
        ∑' l, indexedTiltedProbability step n (fun i => F i.succ)
          (indexedChildPoint step n p a.1 a.2.val) l * f (a.1,a.2.val,l) := by
  rw [indexedLeaf_tsum_active n p.2.1 _ (by
    intro i j hj l; rw [indexedTiltedProbability_inactive step n F p i j hj l,zero_mul])]
  apply tsum_congr
  intro a
  simp_rw [indexedTiltedProbability_active step n F p a (hc a.1 a.2.val),mul_assoc,ENNReal.tsum_mul_left]

end SphericalPerceptronFreeEnergy
end

end OAI
