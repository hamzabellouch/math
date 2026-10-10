import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.GroupoidComponentHomology
import OAI.GroupTheory.SimpleAmenable.Simplicial.BarComponents

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Simplicial Opposite
namespace TranslationNerve
open TranslationFiltered

variable (P:Type) [CommMonoid P]
abbrev C := ActionCategory P (Q P)
abbrev B (n:ℕ) := ComposableArrows (SingleObj P) n
lemma eqToHom_val {x y:C P} (h:x=y) : (eqToHom h).hom=(1:P) := by subst y; rfl
lemma single_eqToHom {x y:SingleObj P} (h:x=y) : eqToHom h=(1:P) := by subst y; rfl
noncomputable def lift (n:ℕ) (q:Q P) (s:B P n) : ComposableArrows (C P) n where
  obj i := (Algebra.GrothendieckGroup.of (M:=P) (s.map (homOfLE (Fin.zero_le i))) * q : Q P)
  map {i j} f := ⟨s.map f, by
    change Algebra.GrothendieckGroup.of (M:=P) (s.map f) * (Algebra.GrothendieckGroup.of (M:=P)
      (s.map (homOfLE (Fin.zero_le i))) * q) = Algebra.GrothendieckGroup.of (M:=P) (s.map (homOfLE (Fin.zero_le j))) * q
    rw [←mul_assoc,←map_mul (Algebra.GrothendieckGroup.of (M:=P))]
    have h:=s.map_comp (homOfLE (Fin.zero_le i)) f
    change s.map (homOfLE (Fin.zero_le i) ≫ f)=s.map f*s.map (homOfLE (Fin.zero_le i)) at h
    rw [←h]
    rfl⟩
  map_id i := by apply Functor.Elements.Hom.ext; exact s.map_id i
  map_comp f g := by apply Functor.Elements.Hom.ext; exact s.map_comp f g
lemma lift_left (n:ℕ) (q:Q P) (s:B P n) : (lift P n q s).left.back=q := by
  change Algebra.GrothendieckGroup.of (s.map (homOfLE (Fin.zero_le (0:Fin (n+1))))) * q=q
  rw [show homOfLE (Fin.zero_le (0:Fin (n+1))) = 𝟙 _ from rfl,s.map_id]
  change Algebra.GrothendieckGroup.of (M:=P) (1:P)*q=q
  rw [map_one,one_mul]
lemma lift_project (n:ℕ) (q:Q P) (s:B P n) : lift P n q s ⋙ ActionCategory.π P (Q P)=s := by
  apply CategoryTheory.Functor.ext
  · intro i j f; simp only [single_eqToHom,SingleObj.comp_as_mul,one_mul,mul_one]; rfl
  · intro i; exact Subsingleton.elim _ _
lemma lift_recover (n:ℕ) (s:ComposableArrows (C P) n) :
    lift P n s.left.back (s ⋙ ActionCategory.π P (Q P))=s := by
  apply CategoryTheory.Functor.ext
  · intro i j f; apply Functor.Elements.Hom.ext
    erw [Functor.Elements.comp_hom,Functor.Elements.comp_hom]
    simp only [SingleObj.comp_as_mul,eqToHom_val,one_mul,mul_one]
    rfl
  · intro i
    apply (ActionCategory.objEquiv P (Q P)).symm.injective
    exact (s.map (homOfLE (Fin.zero_le i))).map_val
noncomputable def coordinates (n:ℕ) : ComposableArrows (C P) n ≃ Q P × B P n where
  toFun s := (s.left.back,s ⋙ ActionCategory.π P (Q P))
  invFun x := lift P n x.1 x.2
  left_inv := lift_recover P n
  right_inv x := Prod.ext (lift_left P n x.1 x.2) (lift_project P n x.1 x.2)
noncomputable def translate (q:Q P) : C P ⥤ C P where
  obj x := (q*x.back:Q P)
  map f := ⟨f.hom,by
    change Algebra.GrothendieckGroup.of f.hom * (q * _) = _
    rw [mul_left_comm]
    exact congrArg (q*·) f.map_val⟩
  map_id _ := rfl
  map_comp _ _ := rfl
lemma translate_one : translate P 1=𝟭 _ := by
  apply CategoryTheory.Functor.ext
  · intro x y f; apply Functor.Elements.Hom.ext
    erw [Functor.Elements.comp_hom,Functor.Elements.comp_hom]
    simp only [SingleObj.comp_as_mul,eqToHom_val,one_mul,mul_one]
    rfl
  · intro x; apply (ActionCategory.objEquiv P (Q P)).symm.injective; exact one_mul _
lemma translate_mul (q r:Q P) : translate P (q*r)=translate P r ⋙ translate P q := by
  apply CategoryTheory.Functor.ext
  · intro x y f; apply Functor.Elements.Hom.ext
    erw [Functor.Elements.comp_hom,Functor.Elements.comp_hom]
    simp only [SingleObj.comp_as_mul,eqToHom_val,one_mul,mul_one]
    rfl
  · intro x; apply (ActionCategory.objEquiv P (Q P)).symm.injective; exact mul_assoc _ _ _
noncomputable instance action (n:ℕ) : MulAction (Q P) (ComposableArrows (C P) n) where
  smul q s := s ⋙ translate P q
  one_smul s := by change s ⋙ translate P 1=s; rw [translate_one]; rfl
  mul_smul q r s := by change s ⋙ translate P (q*r)=(s ⋙ translate P r) ⋙ translate P q; rw [translate_mul]; rfl
lemma smul_left (n:ℕ) (q:Q P) (s:ComposableArrows (C P) n) :
    (q • s).left.back=q*s.left.back := rfl
lemma smul_project (n:ℕ) (q:Q P) (s:ComposableArrows (C P) n) :
    (q • s) ⋙ ActionCategory.π P (Q P)=s ⋙ ActionCategory.π P (Q P) := by
  apply CategoryTheory.Functor.ext
  · intro i j f; simp only [single_eqToHom,SingleObj.comp_as_mul,one_mul,mul_one]; rfl
  · intro i; exact Subsingleton.elim _ _
lemma smul_lift (n:ℕ) (q r:Q P) (s:B P n) :
    q • lift P n r s=lift P n (q*r) s := by
  apply (coordinates P n).injective
  apply Prod.ext
  · change (q • lift P n r s).left.back=(lift P n (q*r) s).left.back
    rw [smul_left,lift_left,lift_left]
  · change (q • lift P n r s) ⋙ ActionCategory.π P (Q P)=lift P n (q*r) s ⋙ ActionCategory.π P (Q P)
    rw [smul_project,lift_project,lift_project]
noncomputable def simplicial : SimplicialObject (Action (Type) (Q P)) where
  obj n := Action.ofMulAction (Q P) (ComposableArrows (C P) n.unop.len)
  map f := { hom := (nerve (C P)).map f
             comm _ := by ext s; rfl }
  map_id _ := by ext s; rfl
  map_comp _ _ := by ext s; rfl
end TranslationNerve

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial SimplicialObject Opposite AlgebraicTopology
namespace TranslationNerve
open TranslationFiltered FreeChains

attribute [local instance 1200] Rep.hV2
variable (P:Type) [CommMonoid P]
noncomputable def actionCoordinates (n:ℕ) :
    (simplicial P).obj (op ⦋n⦌) ≅ Action.leftRegular (Q P) ⊗ Action.trivial (Q P) (B P n) :=
  Action.mkIso (coordinates P n).toIso (by
    intro q
    ext s
    exact Prod.ext (smul_left P n q s) (smul_project P n q s))
noncomputable def linear : SimplicialObject (Rep ℤ (Q P)) := simplicial P ⋙ Rep.linearization ℤ (Q P)
noncomputable def complex : ChainComplex (Rep ℤ (Q P)) ℕ := AlternatingFaceMapComplex.obj (linear P)
noncomputable def freeIso (n:ℕ) : (complex P).X n ≅ Rep.free ℤ (Q P) (B P n) :=
  (Rep.linearization ℤ (Q P)).mapIso (actionCoordinates P n) ≪≫
  (Functor.Monoidal.μIso (Rep.linearization ℤ (Q P)) _ _).symm ≪≫
  tensorIso (Rep.linearizationOfMulActionIso ℤ (Q P) (Q P))
    (Rep.linearizationTrivialIso ℤ (Q P) (B P n)) ≪≫
  Rep.leftRegularTensorTrivialIsoFree ℤ (Q P) (B P n)
noncomputable instance projective (n:ℕ) : Projective ((complex P).X n) :=
  Projective.of_iso (freeIso P n).symm inferInstance
abbrev forgetRep := forget₂ (Rep ℤ (Q P)) (ModuleCat ℤ)
noncomputable def coeffIso (n:ℕ) : (forgetRep P).obj ((complex P).X n) ≅
    (FreeChains.complex (nerve (C P))).X n := (MonoidAlgebra.coeffLinearEquiv ℤ).toModuleIso
lemma coeff_natural {n m:SimplexCategoryᵒᵖ} (f:n⟶m) :
    (coeffIso P n.unop.len).hom ≫ (ModuleCat.free ℤ).map ((nerve (C P)).map f) =
    (forgetRep P).map ((linear P).map f) ≫ (coeffIso P m.unop.len).hom := by
  ext x
  rfl
lemma coeff_d (m:ℕ) : (coeffIso P (m+1)).hom ≫ (FreeChains.complex (nerve (C P))).d (m+1) m =
    (forgetRep P).map ((complex P).d (m+1) m) ≫ (coeffIso P m).hom := by
  rw [show (FreeChains.complex (nerve (C P))).d (m+1) m =
      ∑ i:Fin (m+2),(-1:ℤ)^i.val • (ModuleCat.free ℤ).map ((nerve (C P)).δ i) from
      AlternatingFaceMapComplex.obj_d_eq _ m]
  rw [show (complex P).d (m+1) m=∑ i:Fin (m+2),(-1:ℤ)^i.val • (linear P).δ i from
      AlternatingFaceMapComplex.obj_d_eq _ m]
  dsimp only [coeffIso,FreeChains.complex,complex,linear]
  erw [Functor.map_sum]
  simp only [Preadditive.comp_sum,Preadditive.sum_comp,Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun f => ((-1:ℤ)^i.val) • f)
    (coeff_natural P (SimplexCategory.δ i).op)
noncomputable def forgetIso : ((forgetRep P).mapHomologicalComplex c).obj (complex P) ≅
    FreeChains.complex (nerve (C P)) := by
  refine HomologicalComplex.Hom.isoOfComponents (coeffIso P) ?_
  rintro n m rfl
  exact coeff_d P m
noncomputable def aug0 : (complex P).X 0 ⟶ Rep.trivial ℤ (Q P) ℤ :=
  Rep.ofHom ⟨((coeffIso P 0).hom ≫ SimplicialAugment.aug0 (nerve (C P))).hom, by
    intro q
    ext s
    change (SimplicialAugment.aug0 (nerve (C P)))
        ((coeffIso P 0).hom (Representation.linearize ℤ (Q P) ((simplicial P).obj (op ⦋0⦌)) q
          (MonoidAlgebra.single s 1))) =
      (SimplicialAugment.aug0 (nerve (C P))) ((coeffIso P 0).hom (MonoidAlgebra.single s 1))
    rw [Representation.linearize_single]
    change (SimplicialAugment.aug0 (nerve (C P))) (ModuleCat.freeMk (s ⋙ translate P q)) =
      (SimplicialAugment.aug0 (nerve (C P))) (ModuleCat.freeMk s)
    exact (SimplicialAugment.aug0_mk (nerve (C P)) _).trans
      (SimplicialAugment.aug0_mk (nerve (C P)) _).symm⟩
lemma d_aug0 : (complex P).d 1 0 ≫ aug0 P=0 := by
  apply (forgetRep P).map_injective
  rw [Functor.map_comp,Functor.map_zero]
  change (forgetRep P).map ((complex P).d 1 0) ≫ (coeffIso P 0).hom ≫
    SimplicialAugment.aug0 (nerve (C P))=0
  have h := (forgetIso P).hom.comm 1 0
  change (coeffIso P 1).hom ≫ (FreeChains.complex (nerve (C P))).d 1 0 =
    (forgetRep P).map ((complex P).d 1 0) ≫ (coeffIso P 0).hom at h
  erw [←Category.assoc,←h,Category.assoc,SimplicialAugment.d_aug0,HasZeroMorphisms.comp_zero]
noncomputable def aug : complex P ⟶ (ChainComplex.single₀ _).obj (Rep.trivial ℤ (Q P) ℤ) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨aug0 P,d_aug0 P⟩
lemma forget_aug : ((forgetRep P).mapHomologicalComplex c).map (aug P) ≫
    (HomologicalComplex.singleMapHomologicalComplex (forgetRep P) c 0).hom.app _ =
    (forgetIso P).hom ≫ SimplicialAugment.aug (nerve (C P)) := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f,Functor.mapHomologicalComplex_map_f]
  rfl
noncomputable instance nerve_aug_quasiIso : QuasiIso (SimplicialAugment.aug (nerve (C P))) where
  quasiIsoAt n := by
    cases n with
    | zero => rw [quasiIsoAt_iff_isIso_homologyMap]; infer_instance
    | succ n =>
      rw [quasiIsoAt_iff_isIso_homologyMap]
      have hX : IsZero ((FreeChains.complex (nerve (C P))).homology (n+1)) :=
        (FilteredNerve.positive_acyclic (C P) (n+1) (by omega)).of_iso
          ((HomologicalComplex.homologyFunctor A c (n+1)).mapIso (complexIso (nerve (C P)))).symm
      have hY : IsZero (((ChainComplex.single₀ A).obj Z).homology (n+1)) := by
        apply ShortComplex.isZero_homology_of_isZero_X₂
        exact HomologicalComplex.isZero_single_obj_X c 0 Z (n+1) (by omega)
      exact hX.isIso hY _
noncomputable instance aug_quasiIso : QuasiIso (aug P) := by
  rw [←HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (forgetRep P)]
  have h : QuasiIso ((forgetIso P).hom ≫ SimplicialAugment.aug (nerve (C P))) := inferInstance
  rw [←forget_aug] at h
  exact quasiIso_of_comp_right
    (((forgetRep P).mapHomologicalComplex c).map (aug P))
    ((HomologicalComplex.singleMapHomologicalComplex (forgetRep P) c 0).hom.app _)
noncomputable def resolution : ProjectiveResolution (Rep.trivial ℤ (Q P) ℤ) where
  complex := complex P
  π := aug P
end TranslationNerve

end

end OAI
