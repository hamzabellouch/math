import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.TotalSingle

namespace OAI

section

section

open CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace BiResolution

open DiagonalResolution TotalHomotopy

noncomputable def aug₀ : total.X 0 ⟶ (Functor.const D).obj Z :=
  complex.totalDesc (fun p q hpq => eqToHom (by
    change p+q=0 at hpq
    obtain ⟨rfl,rfl⟩ := Nat.add_eq_zero_iff.mp hpq
    rfl) ≫ DiagonalResolution.augmentation.app (op ⦋0⦌))

@[reassoc (attr := simp)] lemma ι_aug₀ :
    complex.ιTotal c 0 0 0 (by simp) ≫ aug₀ =
      DiagonalResolution.augmentation.app (op ⦋0⦌) := by
  simp [aug₀,ι_totalDesc]
  change (𝟙 _) ≫ DiagonalResolution.augmentation.app (op ⦋0⦌) = _
  exact Category.id_comp _

lemma d_aug₀ : total.d 1 0 ≫ aug₀=0 := by
  change (complex.total c).d 1 0 ≫ aug₀=0
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  change p+q=1 at hpq
  have hpq' : (p=0 ∧ q=1) ∨ (p=1 ∧ q=0) := by omega
  rcases hpq' with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals
    simp only [comp_zero]
    erw [←Category.assoc]
    first | erw [ι_d_leftZero] | erw [ι_d_rightZero]
    erw [Category.assoc,ι_aug₀]
    apply NatTrans.ext
    funext d
    apply Sigma.hom_ext
    intro f
    simp [complex,chains,row,rowMap,AlternatingFaceMapComplex.objD,
      DiagonalResolution.augmentation,pre,SimplicialObject.δ]
    erw [NatTrans.comp_app,NatTrans.app_add,NatTrans.app_neg]
  · change Sigma.ι (fun _ : (⦋0⦌,⦋1⦌) ⟶ d => Z) f ≫
      ((Limits.Sigma.desc (fun index : (⦋0⦌,⦋1⦌) ⟶ d =>
        Sigma.ι (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => Z)
          (Prod.mkHom index.1 (SimplexCategory.δ 0 ≫ index.2))) +
        -Limits.Sigma.desc (fun index : (⦋0⦌,⦋1⦌) ⟶ d =>
          Sigma.ι (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => Z)
            (Prod.mkHom index.1 (SimplexCategory.δ 1 ≫ index.2)))) ≫
        Sigma.desc (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => 𝟙 Z)) = 0
    simp [Preadditive.add_comp,Preadditive.comp_add,Preadditive.neg_comp,
      Preadditive.comp_neg]
  · change Sigma.ι (fun _ : (⦋1⦌,⦋0⦌) ⟶ d => Z) f ≫
      ((Limits.Sigma.desc (fun index : (⦋1⦌,⦋0⦌) ⟶ d =>
        Sigma.ι (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => Z)
          (Prod.mkHom (SimplexCategory.δ 0 ≫ index.1) index.2)) +
        -Limits.Sigma.desc (fun index : (⦋1⦌,⦋0⦌) ⟶ d =>
          Sigma.ι (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => Z)
            (Prod.mkHom (SimplexCategory.δ 1 ≫ index.1) index.2))) ≫
        Sigma.desc (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => 𝟙 Z)) = 0
    simp [Preadditive.add_comp,Preadditive.comp_add,Preadditive.neg_comp,
      Preadditive.comp_neg]

noncomputable def pi : total ⟶ (ChainComplex.single₀ (D ⥤ A)).obj ((Functor.const D).obj Z) :=
  (ChainComplex.toSingle₀Equiv total ((Functor.const D).obj Z)).symm ⟨aug₀,d_aug₀⟩

@[simp] lemma pi_f_zero : pi.f 0 = aug₀ := ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

noncomputable def evalComplexIso (d : D) :
    TotalFunctor.map₂ ((evaluation D A).obj d) complex ≅ complexAt d := by
  let E := (evaluation D A).obj d
  let F := E.mapHomologicalComplex c
  refine eqToIso ?_
  change ((alternatingFaceMapComplex (ChainComplex (D ⥤ A) ℕ) ⋙ F.mapHomologicalComplex c).obj
    (chains ⋙ alternatingFaceMapComplex (D ⥤ A))) = _
  rw [map_alternatingFaceMapComplex F]
  change AlternatingFaceMapComplex.obj (chains ⋙ alternatingFaceMapComplex (D ⥤ A) ⋙ F) = _
  rw [map_alternatingFaceMapComplex E]
  rfl

noncomputable def evalTotalIso (d : D) :
    (((evaluation D A).obj d).mapHomologicalComplex c).obj total ≅ (complexAt d).total c :=
  TotalFunctor.iso ((evaluation D A).obj d) complex ≪≫ total.mapIso (evalComplexIso d) c

end BiResolution

end

section

open CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace BiResolution

open DiagonalResolution TotalHomotopy

lemma contraction_aug (d : D) :
    (complexAt d).ιTotal c 0 0 0 (by simp) ≫ ((totalAtEquiv d).hom.f 0) =
      Sigma.desc (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => 𝟙 Z) := by
  change (complexAt d).ιTotal c 0 0 0 (by simp) ≫
    (total.map (complexAtEquiv d).hom c).f 0 ≫
    (TotalHomotopy.singleIso (AlternatingFaceMapComplex.obj (point d))).hom.f 0 ≫
    (pointExtra d).homotopyEquiv.hom.f 0 = _
  rw [ιTotal_map_assoc]
  have hs : (TotalHomotopy.single (AlternatingFaceMapComplex.obj (point d))).ιTotal c 0 0 0 (by simp) ≫
      (TotalHomotopy.singleIso (AlternatingFaceMapComplex.obj (point d))).hom.f 0 = 𝟙 _ := by
    change (TotalHomotopy.singleIn _).f 0 ≫ _ = _
    have h := congrArg (fun f : AlternatingFaceMapComplex.obj (point d) ⟶ _ => f.f 0)
      (Iso.inv_hom_id (TotalHomotopy.singleIso (AlternatingFaceMapComplex.obj (point d))))
    exact h
  erw [←Category.assoc _ ((TotalHomotopy.singleIso (AlternatingFaceMapComplex.obj (point d))).hom.f 0)
    ((pointExtra d).homotopyEquiv.hom.f 0),hs,Category.id_comp]
  dsimp [complexAtEquiv,complexAtIso,pointExtra]
  simp [HomotopyEquiv.ofIso,CategoryTheory.eqToIso,HomologicalComplex.eqToHom_f,HomologicalComplex.singleMapHomologicalComplex,
    SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv,
    extra,augmentedAt,augmentation,pointAugmented,pointAugmentation]
  apply Sigma.hom_ext
  intro f
  erw [eqToHom_refl,Category.id_comp]
  change Sigma.ι (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => Z) f ≫
    Sigma.desc (fun index : (⦋0⦌,⦋0⦌) ⟶ d =>
      Sigma.ι (fun _ : ⦋0⦌ ⟶ d.2 => Z) index.2) ≫
    Sigma.desc (fun _ : ⦋0⦌ ⟶ d.2 => 𝟙 Z) =
    Sigma.ι (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => Z) f ≫
      Sigma.desc (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => 𝟙 Z)
  simp

lemma eval_inverse_aug (d : D) :
    (complexAt d).ιTotal c 0 0 0 (by simp) ≫ (evalTotalIso d).inv.f 0 ≫
      ((((evaluation D A).obj d).mapHomologicalComplex c).map pi).f 0 =
      Sigma.desc (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => 𝟙 Z) := by
  change (complexAt d).ιTotal c 0 0 0 (by simp) ≫
    (total.map (evalComplexIso d).inv c).f 0 ≫
    TotalFunctor.comparisonF ((evaluation D A).obj d) complex 0 ≫ (pi.f 0).app d = _
  rw [ιTotal_map_assoc]
  simp only [evalComplexIso,CategoryTheory.eqToIso,HomologicalComplex.eqToHom_f]
  change _ ≫ (TotalFunctor.comparisonF ((evaluation D A).obj d) complex 0) ≫ (pi.f 0).app d = _
  erw [←Category.assoc,TotalFunctor.ι_comparisonF,pi_f_zero]
  change (complex.ιTotal c 0 0 0 (by simp)).app d ≫ aug₀.app d = _
  erw [←NatTrans.comp_app,ι_aug₀]
  rfl

instance pi_quasiIso : QuasiIso pi := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro d
  let f := (((evaluation D A).obj d).mapHomologicalComplex c).map pi
  have h : (evalTotalIso d).inv ≫ f ≫ (DiagonalResolution.singleAtIso d).hom =
      (totalAtEquiv d).hom := by
    apply HomologicalComplex.to_single_hom_ext
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    change p+q=0 at hpq
    obtain ⟨rfl,rfl⟩ := Nat.add_eq_zero_iff.mp hpq
    simp only [HomologicalComplex.comp_f,←Category.assoc,contraction_aug]
    dsimp only [f]
    rw [Category.assoc ((complexAt d).ιTotal c 0 0 0 hpq),eval_inverse_aug]
    simp [DiagonalResolution.singleAtIso,HomologicalComplex.singleMapHomologicalComplex]
    change (Sigma.desc (fun _ : (⦋0⦌,⦋0⦌) ⟶ d => 𝟙 Z)) ≫ 𝟙 Z = _
    exact Category.comp_id _
  change QuasiIso f
  rw [←quasiIso_iff_comp_left (evalTotalIso d).inv f,
    ←quasiIso_iff_comp_right ((evalTotalIso d).inv ≫ f) (DiagonalResolution.singleAtIso d).hom,
    Category.assoc,h]
  infer_instance

noncomputable def resolution : ProjectiveResolution ((Functor.const D).obj Z) where
  complex := total
  π := pi
  quasiIso := pi_quasiIso

end BiResolution

end

section

open CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace ModelAssembly

open DiagonalResolution
variable (X : Dᵒᵖ ⥤ Type)

@[reassoc (attr := simp)] lemma pre_forward {a b : D} (k : a ⟶ b) :
    (assembly X).map (pre k) ≫ forward X a =
      forward X b ≫ (sigmaConst.obj Z).map (X.map k.op) := by
  apply colimit.hom_ext
  intro e
  apply Sigma.hom_ext
  intro f
  change Sigma.ι (fun _ : b ⟶ e.unop.1.unop => Z) f ≫
    colimit.ι (projection X ⋙ free b) e ≫
      colim.map (Functor.whiskerLeft (projection X) (pre k)) ≫ forward X a = _
  erw [colimit.ι_map_assoc]
  change Sigma.ι (fun _ : b ⟶ e.unop.1.unop => Z) f ≫
    (pre k).app e.unop.1.unop ≫ colimit.ι (projection X ⋙ free a) e ≫ forward X a = _
  erw [←Category.assoc,ι_pre,ι_to]
  erw [ι_to_assoc]
  dsimp [freeCocone,sigmaConst]
  erw [Sigma.ι_comp_desc,←Category.assoc,Sigma.ι_comp_desc,Sigma.ι_comp_map',Category.id_comp]
  congr 1
  change X.map (k ≫ f).op e.unop.2 = X.map k.op (X.map f.op e.unop.2)
  rw [op_comp,X.map_comp]
  rfl

noncomputable def models : Dᵒᵖ ⥤ (D ⥤ A) where
  obj d := free d.unop
  map f := pre f.unop
  map_id d := pre_id _
  map_comp f g := by simp only [unop_comp,pre_comp]

noncomputable def freeNatIso : models ⋙ assembly X ≅ X ⋙ sigmaConst.obj Z :=
  NatIso.ofComponents (fun d => freeIso X d.unop) (fun f => pre_forward X f.unop)

noncomputable def modelEquiv : HomotopyEquiv DiagonalResolution.complex BiResolution.total :=
  ProjectiveResolution.homotopyEquiv DiagonalResolution.resolution BiResolution.resolution

noncomputable def assembledEquiv : HomotopyEquiv
    (((assembly X).mapHomologicalComplex (ComplexShape.down ℕ)).obj DiagonalResolution.complex)
    (((assembly X).mapHomologicalComplex (ComplexShape.down ℕ)).obj BiResolution.total) :=
  (assembly X).mapHomotopyEquiv modelEquiv

end ModelAssembly

end

end

end OAI
