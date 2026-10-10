import OAI.Algebra.Finitistic.Ordinary.OrdinaryOffDiagonalComplexMaps
import OAI.Algebra.Finitistic.Ordinary.OrdinaryOffDiagonalProjective
import OAI.Algebra.Finitistic.Ordinary.OrdinaryRetainedRestriction
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleAugmentationQuasiIso
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleResolutionProjective
import OAI.Algebra.Finitistic.Ordinary.OrdinaryRightProjective

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.XResolution
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)

abbrev ordinaryOObject : ModuleCat.{u} ((B ⊗[k] ChainAlgebra k l) ⊗[k] Bᵐᵒᵖ) :=
  RetainedBimodule.object k (B ⊗[k] ChainAlgebra k l) B (BimoduleO P a l)

abbrev ordinaryOComplex : CochainComplex (ModuleCat.{u} ((B ⊗[k] ChainAlgebra k l) ⊗[k] Bᵐᵒᵖ)) ℤ :=
  (HomologicalComplex.single _ (.up ℤ) 0).obj (ordinaryOObject P a l)

/-- The manuscript's actual Q_X = O[0] ⊕ Q_T, with both D-actions retained. -/
def complex := OffDiagonal.complex k B (B ⊗[k] ChainAlgebra k l)
  (ordinaryOComplex P a l) (TensorResolution.integerBimoduleComplex k B l)

abbrev target := OffDiagonal.complex k B (B ⊗[k] ChainAlgebra k l)
  (ordinaryOComplex P a l)
  ((HomologicalComplex.single _ (.up ℤ) 0).obj (TensorResolution.bimoduleTerminalObject k B l))

/-- The identity on O and the genuine terminal augmentation give a D-bimodule chain map. -/
def augmentation : complex P a l ⟶ target P a l :=
  OffDiagonal.complexMap k B (B ⊗[k] ChainAlgebra k l) (𝟙 _)
    (TensorResolution.integerBimoduleAugmentation k B l)

theorem ordinaryOComplex_right_projective
    [∀ n, Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X n)] (n : ℤ) :
    Module.Projective Bᵐᵒᵖ (BimoduleCoefficients k (B ⊗[k] ChainAlgebra k l) B
      ((ordinaryOComplex P a l).X n)) := by
  let F : ModuleCat.{u} ((B ⊗[k] ChainAlgebra k l) ⊗[k] Bᵐᵒᵖ) ⥤ ModuleCat.{u} Bᵐᵒᵖ := ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight (R := k) (A := B ⊗[k] ChainAlgebra k l) (B := Bᵐᵒᵖ)).toRingHom
  by_cases hn : n = 0
  · subst n
    have := ordinaryO_right_projective P a l
    have : Module.Projective Bᵐᵒᵖ (F.obj (ordinaryOObject P a l)) :=
      Module.Projective.of_equiv (RetainedBimodule.rightEquiv k (B ⊗[k] ChainAlgebra k l) B (BimoduleO P a l)).symm
    have : Projective (F.obj (ordinaryOObject P a l)) := ModuleCat.projective_of_categoryTheory_projective _
    have : Projective (F.obj ((ordinaryOComplex P a l).X 0)) := Projective.of_iso
      (F.mapIso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ordinaryOObject P a l))).symm inferInstance
    exact ModuleCat.projective_of_module_projective (F.obj ((ordinaryOComplex P a l).X 0))
  · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ordinaryOObject P a l) n hn
    have : Projective (F.obj ((ordinaryOComplex P a l).X n)) := (F.map_isZero hz).projective
    exact ModuleCat.projective_of_module_projective (F.obj ((ordinaryOComplex P a l).X n))

/-- Every actual term of Q_X is right-D-projective; no left projectivity is assumed. -/
theorem right_projective
    [∀ n, Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X n)] (n : ℤ) :
    Module.Projective (AlgebraD k l B)ᵐᵒᵖ
      (BimoduleCoefficients k (AlgebraD k l B) (AlgebraD k l B) ((complex P a l).X n)) := by
  have := ordinaryOComplex_right_projective P a l n
  have : Module.Projective (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ
      (BimoduleCoefficients k B (B ⊗[k] ChainAlgebra k l)
        ((TensorResolution.integerBimoduleComplex k B l).X n)) :=
    TensorResolution.integerBimoduleRight_projective k B l n
  have := OffDiagonal.right_projective B (B ⊗[k] ChainAlgebra k l)
    (BimoduleCoefficients k (B ⊗[k] ChainAlgebra k l) B ((ordinaryOComplex P a l).X n))
    (BimoduleCoefficients k B (B ⊗[k] ChainAlgebra k l) ((TensorResolution.integerBimoduleComplex k B l).X n))
  exact Module.Projective.of_equiv (RetainedBimodule.rightEquiv k (AlgebraD k l B) (AlgebraD k l B) _).symm

/-- The support of the genuine resolution is exactly bounded by [-l,0]. -/
theorem vanishes (n : ℤ) (hn : n < -(l:ℤ) ∨ 0 < n) : IsZero ((complex P a l).X n) := by
  have hn0 : n ≠ 0 := by omega
  have hO := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ordinaryOObject P a l) n hn0
  have hT : IsZero ((TensorResolution.integerBimoduleComplex k B l).X n) := hn.elim
    (TensorResolution.integerBimodule_lower k B l n) (TensorResolution.integerBimodule_upper k B l n)
  have := ModuleCat.isZero_iff_subsingleton.mp hO
  have := ModuleCat.isZero_iff_subsingleton.mp hT
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact inferInstanceAs (Subsingleton (((ordinaryOComplex P a l).X n) ×
    ((TensorResolution.integerBimoduleComplex k B l).X n)))
end LittleFinitistic.OrdinarySimulation.XResolution

end

end OAI
