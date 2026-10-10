import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleAugmentation

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

/-- The genuine augmentation becomes exactly the already verified right-module augmentation. -/
theorem forget_bimoduleAugmentation :
    (forgetBimoduleComplex k B l).hom ≫ augmentationMap k B l =
      ((forgetBimodule k B l).mapHomologicalComplex (.up ℕ)).map (bimoduleAugmentationMap k B l) ≫
        (forgetAugmentationTargetIso k B l).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : n = l
  · subst n
    change (forgetBimoduleTerm k B l l).hom ≫ (augmentationMap k B l).f l =
      (forgetBimodule k B l).map ((bimoduleAugmentationMap k B l).f l) ≫
        (forgetAugmentationTargetIso k B l).hom.f l
    have h₁ : (augmentationMap k B l).f l = augmentationHom k B l ≫
        (HomologicalComplex.singleObjXSelf (.up ℕ) l
          (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B))).inv := by
      unfold augmentationMap
      apply HomologicalComplex.mkHomToSingle_f
    have h₂ : (bimoduleAugmentationMap k B l).f l = bimoduleAugmentationHom k B l ≫
        (HomologicalComplex.singleObjXSelf (.up ℕ) l (bimoduleTerminalObject k B l)).inv := by
      unfold bimoduleAugmentationMap
      apply HomologicalComplex.mkHomToSingle_f
    rw [h₁,h₂]
    change (forgetBimoduleTerm k B l l).hom ≫ augmentationHom k B l ≫
        (HomologicalComplex.singleObjXSelf (.up ℕ) l
          (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B))).inv =
      (forgetBimodule k B l).map (bimoduleAugmentationHom k B l ≫
        (HomologicalComplex.singleObjXSelf (.up ℕ) l (bimoduleTerminalObject k B l)).inv) ≫
      ((HomologicalComplex.singleMapHomologicalComplex (forgetBimodule k B l) (.up ℕ) l).hom.app
        (bimoduleTerminalObject k B l)).f l ≫
      ((HomologicalComplex.single _ (.up ℕ) l).map (forgetBimoduleTerminal k B l).hom).f l
    rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self]
    simp only [Category.assoc,Iso.inv_hom_id_assoc]
    rw [(forgetBimodule k B l).map_comp]
    have hc := ((forgetBimodule k B l).mapIso
      (HomologicalComplex.singleObjXSelf (.up ℕ) l (bimoduleTerminalObject k B l))).inv_hom_id_assoc
        ((forgetBimoduleTerminal k B l).hom ≫
          (HomologicalComplex.singleObjXSelf (.up ℕ) l
            (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B))).inv)
    rw [Category.assoc]
    refine Eq.trans ?_ (congrArg (fun t => (forgetBimodule k B l).map (bimoduleAugmentationHom k B l) ≫ t) hc).symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℕ) l
      (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B)) n hn).eq_of_tgt _ _

/-- Actual augmentation quasi-isomorphism with its outside left B-action retained. -/
theorem bimoduleAugmentationMap_quasiIso : QuasiIso (bimoduleAugmentationMap k B l) := by
  apply (RestrictionHomology.quasiIso_iff
    (Algebra.TensorProduct.includeRight (R := k) (A := B) (B := (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ)).toRingHom _).mp
  let g := ((forgetBimodule k B l).mapHomologicalComplex (.up ℕ)).map (bimoduleAugmentationMap k B l)
  let := augmentationMap_quasiIso k B l
  have h : QuasiIso (g ≫ (forgetAugmentationTargetIso k B l).hom) := by
    dsimp only [g]
    rw [← forget_bimoduleAugmentation]
    infer_instance
  exact (quasiIso_iff_comp_right g (forgetAugmentationTargetIso k B l).hom).mp h

/-- The source's augmentation in degrees [-l,0], as a genuine bimodule map. -/
def integerBimoduleAugmentation : integerBimoduleComplex k B l ⟶
    (HomologicalComplex.single _ (.up ℤ) 0).obj (bimoduleTerminalObject k B l) :=
  HomologicalComplex.extendMap (bimoduleAugmentationMap k B l) (degreeEmbedding l) ≫
    (HomologicalComplex.extendSingleIso (e := degreeEmbedding l)
      (X := bimoduleTerminalObject k B l) l 0 (by simp)).hom

theorem integerBimoduleAugmentation_quasiIso : QuasiIso (integerBimoduleAugmentation k B l) := by
  have := bimoduleAugmentationMap_quasiIso k B l
  exact inferInstanceAs (QuasiIso
    (HomologicalComplex.extendMap (bimoduleAugmentationMap k B l) (degreeEmbedding l) ≫
      (HomologicalComplex.extendSingleIso (e := degreeEmbedding l)
        (X := bimoduleTerminalObject k B l) l 0 (by simp)).hom))
end LittleFinitistic.OrdinarySimulation.TensorResolution

end

end OAI
