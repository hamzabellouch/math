import OAI.Algebra.AuslanderReiten.HomComplex.FullHomComparison
import OAI.Algebra.AuslanderReiten.Algebras.FrobeniusTrace
import OAI.Algebra.AuslanderReiten.Complete.SelfInjectiveComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

structure ExactProjectiveCochain (K : CochainComplex (ModuleCat.{u} R) ℤ) : Prop where
  finite : ∀ i, Module.Finite R (K.X i)
  projective : ∀ i, Module.Projective R (K.X i)
  exactAt : ∀ i, K.ExactAt i

theorem chain_exactAt_iff (P : ChainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    P.ExactAt i ↔ LinearMap.range (P.d (i + 1) i).hom =
      LinearMap.ker (P.d i (i - 1)).hom := by
  rw [P.exactAt_iff' (i := i + 1) (j := i) (k := i - 1)
      (ChainComplex.prev ℤ i) (ChainComplex.next ℤ i),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  rfl

namespace ExactProjectiveCochain

open CompleteComparison

theorem of_chain {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : ExactProjectiveComplex (chainOfCochain K)) : ExactProjectiveCochain K where
  finite i := by
    let := hK.finite (-i)
    exact Module.Finite.equiv (CategoryTheory.Iso.toLinearEquiv (K.extendXIso negIndexEmbedding (i := i) (i' := -i) rfl))
  projective i := by
    let := hK.projective (-i)
    exact Module.Projective.of_equiv
      (CategoryTheory.Iso.toLinearEquiv (K.extendXIso negIndexEmbedding (i := i) (i' := -i) rfl))
  exactAt i :=
    (K.extend_exactAt_iff negIndexEmbedding (j := i) (j' := -i) rfl).mp
      ((chain_exactAt_iff (chainOfCochain K) (-i)).mpr (hK.exactAt (-i)))

theorem to_chain {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : ExactProjectiveCochain K) : ExactProjectiveComplex (chainOfCochain K) where
  finite i := by
    let := hK.finite (-i)
    exact Module.Finite.equiv (CategoryTheory.Iso.toLinearEquiv
      (K.extendXIso negIndexEmbedding (show negIndexEmbedding.f (-i) = i from neg_neg i))).symm
  projective i := by
    let := hK.projective (-i)
    exact Module.Projective.of_equiv (CategoryTheory.Iso.toLinearEquiv
      (K.extendXIso negIndexEmbedding (show negIndexEmbedding.f (-i) = i from neg_neg i))).symm
  exactAt i := (chain_exactAt_iff (chainOfCochain K) i).mp
    ((K.extend_exactAt_iff negIndexEmbedding (j := -i) (j' := i) (neg_neg i)).mpr
      (hK.exactAt (-i)))

theorem shift {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : ExactProjectiveCochain K) (n : ℤ) : ExactProjectiveCochain (K⟦n⟧) where
  finite i := hK.finite (i + n)
  projective i := hK.projective (i + n)
  exactAt i := ShortComplex.exact_of_iso
    ((CochainComplex.shiftShortComplexFunctorIso (ModuleCat.{u} R) n i (n + i) rfl).app K).symm
    (hK.exactAt (n + i))

end ExactProjectiveCochain

namespace ExactProjectiveComplex

open CompleteComparison

theorem cochainShift {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : ExactProjectiveComplex (chainOfCochain K)) (n : ℤ) :
    ExactProjectiveComplex (chainOfCochain (K⟦n⟧)) :=
  ((ExactProjectiveCochain.of_chain hK).shift n).to_chain

end ExactProjectiveComplex

namespace FrobeniusTrace

variable {k : Type u} [Field k] [Algebra k R] [Module.Finite k R]
open CompleteComparison

theorem totallyAcyclicShift (τ : FrobeniusTrace k R)
    {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : ExactProjectiveComplex (chainOfCochain K)) (n : ℤ) :
    TotallyAcyclicComplex (chainOfCochain (K⟦n⟧)) := by
  let := τ.regular_injective
  exact (hK.cochainShift n).totallyAcyclic

end FrobeniusTrace
end ArExplicit

end OAI
