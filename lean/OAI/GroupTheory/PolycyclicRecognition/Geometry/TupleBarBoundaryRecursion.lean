import OAI.GroupTheory.PolycyclicRecognition.Algebra.TupleBarPrepend
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AbelianMultilinearHomology

namespace OAI

/-! # The actual integral bar differential in head-and-tail coordinates -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {A : Type} [Group A]

theorem tupleBarBoundary_cons (n : ℕ) (a : A) (v : Fin (n + 1) → A) :
    groupHomology.inhomogeneousChains.d (integralTrivialCoefficient A) (n + 1)
      (Finsupp.single (Fin.cons a v) 1) =
    Finsupp.single v 1 - Finsupp.single (Fin.cons (a * v 0) (fun i => v i.succ)) 1 +
      tupleBarPrepend n a (Finsupp.single (fun i => v i.succ) 1) -
      tupleBarPrepend n a
        (groupHomology.inhomogeneousChains.d (integralTrivialCoefficient A) n
          (Finsupp.single v 1)) := by
  rw [groupHomology.inhomogeneousChains.d_single,
    groupHomology.inhomogeneousChains.d_single]
  change (Finsupp.single v (1 : ℤ) + ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j.val + 1) •
    Finsupp.single (Fin.contractNth j (· * ·) (Fin.cons a v)) 1) = _
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, zero_add, pow_one, neg_smul, one_smul,
    contractNth_cons_zero, contractNth_cons_succ, Fin.val_succ,
    map_add, map_sum, map_smul, tupleBarPrepend_single]
  have hs (j : Fin (n + 1)) : (-1 : ℤ) ^ (j.val + 1 + 1) = -((-1 : ℤ) ^ (j.val + 1)) := by
    rw [pow_succ, mul_neg_one]
  simp_rw [hs, neg_smul]
  rw [Finset.sum_neg_distrib]
  simp only [show ((Representation.trivial ℤ A ℤ) (v 0)⁻¹) 1 = 1 from rfl]
  abel

end PolycyclicRecognition

end

end OAI
