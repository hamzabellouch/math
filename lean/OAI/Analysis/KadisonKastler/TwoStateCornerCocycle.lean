import OAI.Analysis.KadisonKastler.TwoStateModularAction
import OAI.Analysis.KadisonKastler.MatrixActionCocycle

namespace OAI

/-! # The algebraic cocycle between the two modular corners -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H) (Ω ξ : H)
  (m : ModularSpectralResolution (twoStateMatrixAlgebra M) (twoStateMatrixVector Ω ξ))

def twoStateMatrixAction : Multiplicative ℝ →*
    (CStarMatrix (Fin 2) (Fin 2) (Algebra M) ≃⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) (Algebra M)) where
  toFun := twoStateMatrixAut M Ω ξ m
  map_one' := by
    apply StarAlgEquiv.ext
    intro a
    apply (twoStateMatrixEquiv M).injective
    change (twoStateMatrixEquiv M) ((twoStateMatrixEquiv M).symm
      (modularAlgebraAut m 1 (twoStateMatrixEquiv M a))) = twoStateMatrixEquiv M a
    rw [StarAlgEquiv.apply_symm_apply]
    have h := congrArg (fun f : Algebra (twoStateMatrixAlgebra M) ≃⋆ₐ[ℂ]
      Algebra (twoStateMatrixAlgebra M) => f (twoStateMatrixEquiv M a))
      (map_one (modularAlgebraAction m))
    exact h
  map_mul' s t := by
    apply StarAlgEquiv.ext
    intro a
    apply (twoStateMatrixEquiv M).injective
    change (twoStateMatrixEquiv M) ((twoStateMatrixEquiv M).symm
      (modularAlgebraAut m (s * t) (twoStateMatrixEquiv M a))) =
      (twoStateMatrixEquiv M) ((twoStateMatrixEquiv M).symm
        (modularAlgebraAut m s ((twoStateMatrixEquiv M) ((twoStateMatrixEquiv M).symm
          (modularAlgebraAut m t (twoStateMatrixEquiv M a))))))
    simp only [StarAlgEquiv.apply_symm_apply]
    have h := congrArg (fun f : Algebra (twoStateMatrixAlgebra M) ≃⋆ₐ[ℂ]
      Algebra (twoStateMatrixAlgebra M) => f (twoStateMatrixEquiv M a))
      (map_mul (modularAlgebraAction m) s t)
    exact h

def twoStateCornerAction (i : Fin 2) : Multiplicative ℝ →* (Algebra M ≃⋆ₐ[ℂ] Algebra M) :=
  matrixCornerAction (twoStateMatrixAction M Ω ξ m)
    (twoStateMatrixAut_fixes_diagonal M Ω ξ m) i

def twoStateCornerCocycle (t : Multiplicative ℝ) : unitary (Algebra M) :=
  matrixActionCocycleValue (twoStateMatrixAction M Ω ξ m)
    (twoStateMatrixAut_fixes_diagonal M Ω ξ m) t

theorem twoStateCornerCocycle_mul (s t : Multiplicative ℝ) :
    (twoStateCornerCocycle M Ω ξ m (s * t) : Algebra M) =
      (twoStateCornerCocycle M Ω ξ m s : Algebra M) *
        twoStateCornerAction M Ω ξ m 0 s (twoStateCornerCocycle M Ω ξ m t : Algebra M) :=
  matrixActionCocycleValue_mul _ _ s t

theorem twoStateCornerAction_conjugate (t : Multiplicative ℝ) (a : Algebra M) :
    twoStateCornerAction M Ω ξ m 1 t a =
      (twoStateCornerCocycle M Ω ξ m t : Algebra M) * twoStateCornerAction M Ω ξ m 0 t a *
        star (twoStateCornerCocycle M Ω ξ m t : Algebra M) :=
  matrixCornerAction_conjugate _ _ t a

end

end KadisonKastler

end OAI
