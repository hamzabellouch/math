import OAI.Analysis.FreeEntropy.MatrixBasis

namespace OAI

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
 theorem hermitianMatrix_single {n d : ℕ} (i l : Fin n) (j k : Fin d) :
    hermitianMatrix (EuclideanSpace.single (i,j,k) 1 : MatrixCoordinates n d) l =
      if i=l then hermitianBasis j k else 0 := by
  ext a b
  simp only [hermitianMatrix, hermitianBasis, EuclideanSpace.single, PiLp.single_apply]
  by_cases hil : i=l
  · subst l
    by_cases hjk : j=k
    · subst k
      by_cases hab : a=b
      · subst b
        by_cases hja : j=a <;> simp [*,Prod.mk.injEq,eq_comm]
      · have hbad : ¬(j=a ∧ j=b) := fun h => hab (h.1.symm.trans h.2)
        simp [*,Prod.mk.injEq,eq_comm, and_comm]
    · rcases lt_or_gt_of_ne hjk with hjk' | hkj'
      · by_cases hab : a=b
        · subst b
          have hbad : ¬(j=a ∧ k=a) := fun h => hjk (h.1.trans h.2.symm)
          have hbad' : ¬(k=a ∧ j=a) := fun h => hjk (h.2.trans h.1.symm)
          simp [*,Prod.mk.injEq,eq_comm, and_comm]
        · by_cases hjka : j=a ∧ k=b
          · rcases hjka with ⟨rfl,rfl⟩; simp [*,Prod.mk.injEq,eq_comm,div_eq_mul_inv]
          · by_cases hkja : k=a ∧ j=b
            · rcases hkja with ⟨rfl,rfl⟩; simp [*,Prod.mk.injEq,eq_comm,Ne.symm hab,not_lt_of_gt hjk',div_eq_mul_inv]
            · have hbad : ¬(j=b ∧ k=a) := fun h => hkja ⟨h.2,h.1⟩
              simp [*,Prod.mk.injEq,eq_comm, and_comm]
      · by_cases hab : a=b
        · subst b
          have hbad : ¬(j=a ∧ k=a) := fun h => hjk (h.1.trans h.2.symm)
          have hbad' : ¬(k=a ∧ j=a) := fun h => hjk (h.2.trans h.1.symm)
          simp [*,Prod.mk.injEq,eq_comm, and_comm, not_lt_of_gt hkj']
        · by_cases hjka : j=a ∧ k=b
          · rcases hjka with ⟨rfl,rfl⟩; simp [*,Prod.mk.injEq,eq_comm,not_lt_of_gt hkj',div_eq_mul_inv]
          · by_cases hkja : k=a ∧ j=b
            · rcases hkja with ⟨rfl,rfl⟩; simp [*,Prod.mk.injEq,eq_comm,Ne.symm hab,not_lt_of_gt hkj',div_eq_mul_inv]
            · have hbad : ¬(j=b ∧ k=a) := fun h => hkja ⟨h.2,h.1⟩
              simp [*,Prod.mk.injEq,eq_comm, and_comm,not_lt_of_gt hkj']
  · simp [hil,Prod.mk.injEq,eq_comm]
end FiniteEntropySeparation

end

end OAI
