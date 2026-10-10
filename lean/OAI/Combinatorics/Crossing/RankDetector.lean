import OAI.Combinatorics.Crossing.NodeMoments
import OAI.Combinatorics.Crossing.TwoTriangleBasis
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def detectorVector (s : ℕ) (node : ι → ℝ) (p q : ι) : BiExponent s → ℝ :=
  fun ab => node p ^ ab.1.val * node q ^ ab.2.val

def detectorWeight (node : ι → ℝ) (p q : ι) : ℝ :=
  (node p-node q) / (derivativeAtNode node p * derivativeAtNode node q)

def detectorAtom (s : ℕ) (node : ι → ℝ) (p q : ι) :
    Matrix (BiExponent s) (BiExponent s) ℝ :=
  detectorWeight node p q • Matrix.vecMulVec (detectorVector s node p q) (detectorVector s node p q)

def rankDetector (s : ℕ) (node : ι → ℝ) :
    Matrix ι ι ℝ →ₗ[ℝ] Matrix (BiExponent s) (BiExponent s) ℝ where
  toFun H := ∑ p, ∑ q, H p q • detectorAtom s node p q
  map_add' H K := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c H := by simp [smul_smul, Finset.smul_sum]

theorem detectorAtom_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (node : ι → ℝ) (p : ι) : detectorAtom s node p p = 0 := by
  simp [detectorAtom, detectorWeight]

theorem detectorWeight_ne_zero (node : ι → ℝ) (hn : Function.Injective node)
    {p q : ι} (hpq : p ≠ q) : detectorWeight node p q ≠ 0 := by
  exact div_ne_zero (sub_ne_zero.mpr (hn.ne hpq))
    (mul_ne_zero (derivativeAtNode_ne_zero node hn p) (derivativeAtNode_ne_zero node hn q))

theorem detectorAtom_entry
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (node : ι → ℝ) (p q : ι) (ab cd : BiExponent s) :
    detectorAtom s node p q ab cd =
      (node p-node q) * node p^(ab.1.val+cd.1.val) * node q^(ab.2.val+cd.2.val) /
        (derivativeAtNode node p * derivativeAtNode node q) := by
  simp only [detectorAtom, detectorWeight, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, detectorVector, pow_add]
  ring

theorem rankDetector_diagonal (s : ℕ) (node : ι → ℝ) (d : ι → ℝ) :
    rankDetector s node (Matrix.diagonal d) = 0 := by
  change (∑ p, ∑ q, Matrix.diagonal d p q • detectorAtom s node p q) = 0
  simp [Matrix.diagonal_apply, detectorAtom_self]

end Zarankiewicz

end

end OAI
