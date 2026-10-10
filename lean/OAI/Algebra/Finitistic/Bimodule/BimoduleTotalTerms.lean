import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorDerivedFunctor
import OAI.Algebra.Finitistic.Bimodule.BimoduleTensorUnderlying

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
attribute [local instance] BimoduleBalancedTensor.inputEnveloping
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

abbrev right (P : BiComplex k B) : RightComplex B :=
  ((forgetRight k B).mapHomologicalComplex (.up ℤ)).obj P

abbrev Term (P : BiComplex k B) (Z : CochainComplex (ModuleCat.{u} B) ℤ) (p q : ℤ) :=
  BimoduleBalancedTensor.Tensor k B (P.X p) (ComplexTensor.leftTerm k B Z q)

variable {k B}
variable {P : BiComplex k B} {Z Z' : CochainComplex (ModuleCat.{u} B) ℤ}
variable {p p' q q' : ℤ}

/-- Balanced tensor maps retain the original outside left B action. -/
theorem bimap_smul (f : P.X p ⟶ P.X p') (g : Z.X q ⟶ Z'.X q')
    (b : B) (x : Term k B P Z p q) :
    @BalancedTensor.bimap k B
      (ComplexTensor.rightTerm k B (right k B P) p)
      (ComplexTensor.rightTerm k B (right k B P) p')
      (ComplexTensor.leftTerm k B Z q) (ComplexTensor.leftTerm k B Z' q') _ _ _
      _ _ _ (BalancedTensor.scalarLeftTower k Bᵐᵒᵖ ((right k B P).X p))
      _ _ _ (BalancedTensor.scalarLeftTower k Bᵐᵒᵖ ((right k B P).X p'))
      _ _ _ (BalancedTensor.scalarLeftTower k B (Z.X q))
      _ _ _ (BalancedTensor.scalarLeftTower k B (Z'.X q'))
      ((forgetRight k B).map f).hom g.hom (b • x) =
    b • (show Term k B P Z' p' q' from @BalancedTensor.bimap k B
      (ComplexTensor.rightTerm k B (right k B P) p)
      (ComplexTensor.rightTerm k B (right k B P) p')
      (ComplexTensor.leftTerm k B Z q) (ComplexTensor.leftTerm k B Z' q') _ _ _
      _ _ _ (BalancedTensor.scalarLeftTower k Bᵐᵒᵖ ((right k B P).X p))
      _ _ _ (BalancedTensor.scalarLeftTower k Bᵐᵒᵖ ((right k B P).X p'))
      _ _ _ (BalancedTensor.scalarLeftTower k B (Z.X q))
      _ _ _ (BalancedTensor.scalarLeftTower k B (Z'.X q'))
      ((forgetRight k B).map f).hom g.hom x) := by
  induction x using BalancedTensor.induction_on with
  | hz =>
    rw [smul_zero]
    exact (map_zero _).trans
      ((congrArg (fun y : Term k B P Z' p' q' => b • y) (map_zero _)).trans
        (smul_zero b : b • (0 : Term k B P Z' p' q') = 0)).symm
  | ht m n =>
    change BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B (P.X p'))
      (ComplexTensor.leftTerm k B Z' q') (f.hom ((b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (m : P.X p))) (g.hom n) =
      BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B (P.X p'))
        (ComplexTensor.leftTerm k B Z' q') ((b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (f.hom m : P.X p')) (g.hom n)
    exact congrArg (fun m' => BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B (P.X p'))
      (ComplexTensor.leftTerm k B Z' q') m' (g.hom n))
      (f.hom.map_smul (b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) (m : P.X p))
  | ha x y hx hy =>
    rw [smul_add]
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans
      ((smul_add b (show Term k B P Z' p' q' from _)
        (show Term k B P Z' p' q' from _)).symm.trans
          (congrArg (fun y : Term k B P Z' p' q' => b • y) (map_add _ _ _).symm)))

variable (k B P Z)

theorem horizontal_smul (n p p' : ℤ) (h : p+1=p') (b : B)
    (x : Term k B P Z p (n + -p)) :
    ComplexTensor.horizontal k B (right k B P) Z n p p' h (b • x) =
      b • (show Term k B P Z p' ((n+1) + -p') from
        ComplexTensor.horizontal k B (right k B P) Z n p p' h x) :=
  bimap_smul (P.d p p') (eqToHom (congrArg Z.X (show n + -p = (n+1) + -p' by omega))) b x

theorem column_d_smul (p n m : ℤ) (b : B)
    (x : Term k B P Z p (n + -p)) :
    ((ComplexTensor.column k B (right k B P) Z p).d n m).hom (b • x) =
      b • (show Term k B P Z p (m + -p) from
        ((ComplexTensor.column k B (right k B P) Z p).d n m).hom x) := by
  rw [ComplexTensor.column_d]
  change (-p).negOnePow • (ComplexTensor.map k B (right k B P) Z (𝟙 _) (Z.d _ _) (b • x)) =
    b • ((-p).negOnePow • (show Term k B P Z p (m + -p) from
      ComplexTensor.map k B (right k B P) Z (𝟙 _) (Z.d _ _) x))
  rw [show ComplexTensor.map k B (right k B P) Z (𝟙 _) (Z.d _ _) (b • x) =
    b • (show Term k B P Z p (m + -p) from
      ComplexTensor.map k B (right k B P) Z (𝟙 _) (Z.d _ _) x) from
      bimap_smul (𝟙 (P.X p)) (Z.d _ _) b x]
  exact smul_comm _ _ _

variable {Z}
theorem inputMap_smul (f : Z ⟶ Z') (p q : ℤ) (b : B) (x : Term k B P Z p q) :
    ComplexTensor.inputMap k B (right k B P) f p q (b • x) =
      b • (show Term k B P Z' p q from ComplexTensor.inputMap k B (right k B P) f p q x) :=
  bimap_smul (𝟙 (P.X p)) (f.f q) b x
end LittleFinitistic.BimoduleTotal

end

end OAI
