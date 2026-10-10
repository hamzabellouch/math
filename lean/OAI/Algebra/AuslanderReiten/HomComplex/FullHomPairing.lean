import OAI.Algebra.AuslanderReiten.HomComplex.FullHomDuality

namespace OAI

open CategoryTheory
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra

namespace ArExplicit.FrobeniusTrace

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable (hs : ∀ a b : R, τ.trace (a * b) = τ.trace (b * a))
variable {N N' : Type u}
variable [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
variable [SMulCommClass R k N]
variable [AddCommGroup N'] [Module R N'] [Module k N'] [IsScalarTower k R N']
variable [SMulCommClass R k N']

open CompleteComparison

theorem completeStableDuality_natural
    (P : ChainComplex (ModuleCat.{u} R) ℤ) (hP : ExactProjectiveComplex P)
    (u : N →ₗ[R] N') (f : StableHom R (Cokernel P 0) N)
    (g : StableHom R N' (Cokernel P 1)) :
    ((τ.completeStableDuality hs P hP).symm g) (StableHom.postcomp u f) =
      ((τ.completeStableDuality hs P hP).symm (StableHom.precomp u g)) f := by
  let : ∀ i, Module.Finite R (P.X i) := hP.finite
  let : ∀ i, Module.Projective R (P.X i) := hP.projective
  let E := cokernelSyzygyEquiv hP 0
  change ((τ.projectiveStableDuality hs (P.d 1 0).hom (P.d 0 (-1)).hom
    (differential_comp P 1 0 (-1)) (hP.exactAt 0)).symm
      (StableHom.postcomp E.toLinearMap g)) (StableHom.postcomp u f) =
    ((τ.projectiveStableDuality hs (P.d 1 0).hom (P.d 0 (-1)).hom
    (differential_comp P 1 0 (-1)) (hP.exactAt 0)).symm
      (StableHom.postcomp E.toLinearMap (StableHom.precomp u g))) f
  rw [τ.projectiveStableDuality_natural]
  congr 2
  obtain ⟨g, rfl⟩ := StableHom.classOf_surjective g
  rfl

noncomputable def fullHomTracePairing
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : TotallyAcyclicComplex (chainOfCochain K)) (n : ℤ) :
    StableHom R (Cokernel (chainOfCochain (K⟦n⟧)) 0) (Cokernel (chainOfCochain K) 1)
      ≃ₗ[k] Module.Dual k (CohomologyClass K K n) :=
  (τ.completeStableDuality hs (chainOfCochain K) hK.toExactProjectiveComplex).symm.trans
    (fullHomStableLinearEquiv (k := k) K K n hK
      (hK.toExactProjectiveComplex.cochainShift n)).dualMap

theorem fullHomTracePairing_product
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : TotallyAcyclicComplex (chainOfCochain K)) {n m : ℤ}
    (x : Cocycle K K n) (y : Cocycle K K m)
    (g : StableHom R (Cokernel (chainOfCochain (K⟦n + m⟧)) 0)
      (Cokernel (chainOfCochain K) 1)) :
    (τ.fullHomTracePairing hs K hK (n + m) g) (CohomologyClass.mk (cocycleProduct x y)) =
      (τ.fullHomTracePairing hs K hK n
        (StableHom.precomp
          (cokernelMap (HomologicalComplex.extendMap (shiftedCocycleHom y n) negIndexEmbedding) 0)
          g)) (CohomologyClass.mk x) := by
  change ((τ.completeStableDuality hs (chainOfCochain K) hK.toExactProjectiveComplex).symm g)
    (fullHomStableEquiv K K (n + m) hK (hK.toExactProjectiveComplex.cochainShift (n + m))
      (CohomologyClass.mk (cocycleProduct x y))) = _
  rw [fullHomStableEquiv_product hK (hK.toExactProjectiveComplex.cochainShift n)
    (hK.toExactProjectiveComplex.cochainShift (n + m))]
  let u := cokernelMap
    (HomologicalComplex.extendMap (shiftedCocycleHom y n) negIndexEmbedding) 0
  have hc (z : StableHom R (Cokernel (chainOfCochain K) 0)
      (Cokernel (chainOfCochain (K⟦n⟧)) 0)) :
      StableHom.comp (StableHom.classOf R _ _ u) z = StableHom.postcomp u z := by
    obtain ⟨z, rfl⟩ := StableHom.classOf_surjective z
    rw [StableHom.comp_classOf, StableHom.postcomp_classOf]
  rw [hc]
  exact τ.completeStableDuality_natural hs (chainOfCochain K) hK.toExactProjectiveComplex u
    (fullHomStableEquiv K K n hK (hK.toExactProjectiveComplex.cochainShift n)
      (CohomologyClass.mk x)) g

end ArExplicit.FrobeniusTrace

end OAI
