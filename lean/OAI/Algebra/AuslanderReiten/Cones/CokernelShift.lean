import OAI.Algebra.AuslanderReiten.Complete.CompleteShift

namespace OAI

open CategoryTheory

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]

noncomputable def cokernelOpcyclesEquiv
    (P : ChainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Cokernel P n ≃ₗ[R] P.opcycles n :=
  ((P.opcyclesIsoSc' (n + 1) n (n - 1)
    (ChainComplex.prev ℤ n) (ChainComplex.next ℤ n)) ≪≫
      (P.sc' (n + 1) n (n - 1)).moduleCatOpcyclesIso).toLinearEquiv.symm

noncomputable def cochainCokernelEquiv
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Cokernel (chainOfCochain K) n ≃ₗ[R] K.opcycles (-n) :=
  (cokernelOpcyclesEquiv (chainOfCochain K) n).trans
    (K.extendOpcyclesIso negIndexEmbedding (j := -n) (j' := n) (neg_neg n)).toLinearEquiv

noncomputable def shiftedCokernelEquiv
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a n : ℤ) (ha : a = -n) :
    Cokernel (chainOfCochain (K⟦a⟧)) 0 ≃ₗ[R] Cokernel (chainOfCochain K) n := by
  let E : (K⟦a⟧).opcycles 0 ≃ₗ[R] K.opcycles (-n) :=
    (ShortComplex.opcyclesMapIso
      ((CochainComplex.shiftShortComplexFunctorIso (ModuleCat.{u} R) a 0 (-n)
        (by simpa using ha)).app K)).toLinearEquiv
  exact (cochainCokernelEquiv (K⟦a⟧) 0).trans
    (E.trans (cochainCokernelEquiv K n).symm)

end ArExplicit.CompleteComparison

end OAI
