import OAI.Analysis.Laughlin.Fock.Bidegree

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

noncomputable def occupationFourLabels (Q : ℕ) (A : Finset (Fin (Q+1))) (hA : A.card=4) :
    Fin 4 ↪o Fin (Q+1) := Set.powersetCard.ofFinEmbEquiv.symm ⟨A,hA⟩

theorem occupationBasis_four (Q : ℕ) (A : Finset (Fin (Q+1))) (hA : A.card=4) :
    occupationBasis Q A =
      create (occupationFourLabels Q A hA 0) (create (occupationFourLabels Q A hA 1)
        (create (occupationFourLabels Q A hA 2) (create (occupationFourLabels Q A hA 3) (1 : Space Q)))) := by
  let B : Set.powersetCard (Fin (Q+1)) 4 := ⟨A,hA⟩
  change (Pi.basisFun ℂ (Fin (Q+1))).ExteriorAlgebra B.val = _
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp [ExteriorAlgebra.ιMulti_family,ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply,occupationFourLabels,B,create,Pi.basisFun_apply,mode,Matrix.vecTail,Function.comp_def]

theorem occupationFourLabels_range (Q : ℕ) (A : Finset (Fin (Q+1))) (hA : A.card=4) :
    Finset.univ.image (occupationFourLabels Q A hA) = A := by
  ext i
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  exact Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem ⟨A,hA⟩ i

theorem occupationFourLabels_sum (Q : ℕ) (A : Finset (Fin (Q+1))) (hA : A.card=4) :
    (∑ i ∈ A, i.val) =
      (occupationFourLabels Q A hA 0).val + (occupationFourLabels Q A hA 1).val +
      (occupationFourLabels Q A hA 2).val + (occupationFourLabels Q A hA 3).val := by
  conv_lhs => rw [← occupationFourLabels_range Q A hA]
  rw [Finset.sum_image]
  · simp [Fin.sum_univ_succ,Nat.add_assoc]
  · intro i hi j hj he
    exact (occupationFourLabels Q A hA).injective he

end Laughlin.Fock

end OAI
