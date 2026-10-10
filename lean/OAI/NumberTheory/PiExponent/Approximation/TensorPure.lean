import OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor

namespace OAI

noncomputable section

namespace PiExponentSeshadri.TensorPure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
open MonoidalCategory

variable {X Y : Scheme.{0}}

private local instance sectionModule {X : Scheme.{0}}
    (P : PresheafOfModules X.ringCatSheaf.obj) (U : X.Opens) :
    Module Γ(X, U) (P.obj (op U)) := (P.obj (op U)).isModule

abbrev presheaf (M N : X.Modules) :=
  PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val

abbrev adj (X : Scheme.{0}) :=
  PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)

def pure (M N : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensor X M N).val.obj (op U) :=
  (((adj X).unit.app (presheaf M N)).app (op U)).hom (m ⊗ₜ[Γ(X,U)] n)

@[simp] lemma pure_add_left (M N : X.Modules) (U : X.Opens) (m m' : M.val.obj (op U)) (n : N.val.obj (op U)) :
    pure M N U (m+m') n = pure M N U m n + pure M N U m' n := by
  unfold pure
  rw [TensorProduct.add_tmul]
  exact map_add _ _ _

@[simp] lemma pure_add_right (M N : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) (n n' : N.val.obj (op U)) :
    pure M N U m (n+n') = pure M N U m n + pure M N U m n' := by
  unfold pure
  rw [TensorProduct.tmul_add]
  exact map_add _ _ _

@[simp] lemma pure_smul_left (M N : X.Modules) (U : X.Opens) (a : Γ(X,U)) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    pure M N U (a • m) n = a • pure M N U m n := by
  unfold pure
  rw [← TensorProduct.smul_tmul']
  exact map_smul _ _ _

@[simp] lemma pure_smul_right (M N : X.Modules) (U : X.Opens) (a : Γ(X,U)) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    pure M N U m (a • n) = a • pure M N U m n := by
  simp only [pure]
  rw [TensorProduct.tmul_smul]
  exact map_smul _ _ _

lemma pure_restrict (M N : X.Modules) {U V : X.Opens} (i : V ⟶ U)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensor X M N).val.map i.op (pure M N U m n) =
      pure M N V (M.val.map i.op m) (N.val.map i.op n) := by
  exact (PresheafOfModules.naturality_apply ((adj X).unit.app (presheaf M N)) i.op
    (m ⊗ₜ[Γ(X,U)] n)).symm

lemma map_pure {M N P Q : X.Modules} (f : M ⟶ P) (g : N ⟶ Q)
    (U : X.Opens) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensorMap f g).app U (pure M N U m n) =
      pure P Q U (f.app U m) (g.app U n) := by
  have h := (adj X).unit.naturality
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f.val g.val)
  exact (congrArg (fun q => q.app (op U) (m ⊗ₜ[Γ(X,U)] n)) h).symm

lemma hom_ext {M N P : X.Modules} {f g : moduleTensor X M N ⟶ P}
    (h : ∀ U m n, f.app U (pure M N U m n) = g.app U (pure M N U m n)) : f = g := by
  apply ((adj X).homEquiv (presheaf M N) P).injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  exact h U.unop m n

lemma sheafify_restrict_unit (f : X ⟶ Y) [IsOpenImmersion f]
    (P : PresheafOfModules Y.ringCatSheaf.obj) :
    (modulePresheafRestrict f).map ((adj Y).unit.app P) ≫
      ((moduleSheafificationRestrict f).hom.app P).val =
    (adj X).unit.app ((modulePresheafRestrict f).obj P) := by
  let a := adj Y
  let b := Scheme.Modules.restrictAdjunction f
  let c := modulePresheafRestrictAdjunction f
  let d := adj X
  apply (c.homEquiv _ _).injective
  erw [Adjunction.homEquiv_unit,Functor.map_comp]
  have hn := c.unit_naturality (a.unit.app P)
  rw [← Category.assoc,hn]
  have he := Adjunction.unit_leftAdjointUniq_hom_app (a.comp b) (c.comp d) P
  have ha := a.comp_unit_app b P
  have hd := c.comp_unit_app d P
  let G : Y.Modules ⥤ PresheafOfModules Y.ringCatSheaf.obj :=
    SheafOfModules.forget Y.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)
  let I : X.Modules ⥤ Y.Modules := Scheme.Modules.pushforward f
  have hh := congrArg (fun h => h ≫ (I ⋙ G).map
    (((a.comp b).leftAdjointUniq (c.comp d)).hom.app P)) ha
  exact hh.symm.trans (he.trans hd)

lemma presheaf_restrict_pure (U : X.Opens) (M N : X.Modules)
    (V : U.toScheme.Opens)
    (m : M.val.obj (op (U.ι ''ᵁ V))) (n : N.val.obj (op (U.ι ''ᵁ V))) :
    ((modulePresheafTensorRestrict U M.val N.val).hom.app (op V)).hom
      (m ⊗ₜ[Γ(X,U.ι ''ᵁ V)] n) = (show ((modulePresheafRestrict U.ι).obj M.val).obj (op V) from m) ⊗ₜ[Γ(U.toScheme,V)]
      (show ((modulePresheafRestrict U.ι).obj N.val).obj (op V) from n) := by
  rfl

lemma restrict_pure (U : X.Opens) (M N : X.Modules) (V : U.toScheme.Opens)
    (m : M.val.obj (op (U.ι ''ᵁ V))) (n : N.val.obj (op (U.ι ''ᵁ V))) :
    (moduleTensorRestrict U M N).hom.app V
      (pure M N (U.ι ''ᵁ V) m n) =
      pure (M.restrict U.ι) (N.restrict U.ι) V m n := by
  have h := sheafify_restrict_unit U.ι (presheaf M N)
  have h' := congrArg (fun q => q.app (op V) (m ⊗ₜ[Γ(X,U.ι ''ᵁ V)] n)) h
  have hn := (adj U.toScheme).unit.naturality
    (modulePresheafTensorRestrict U M.val N.val).hom
  have hn' := congrArg (fun q => q.app (op V) (m ⊗ₜ[Γ(X,U.ι ''ᵁ V)] n)) hn
  change (((PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).map
    (modulePresheafTensorRestrict U M.val N.val).hom).val.app (op V))
    (((moduleSheafificationRestrict U.ι).hom.app (presheaf M N)).val.app (op V)
      (pure M N (U.ι ''ᵁ V) m n)) = _
  simp only [PresheafOfModules.comp_app] at h' hn'
  change (((moduleSheafificationRestrict U.ι).hom.app (presheaf M N)).val.app (op V))
    (pure M N (U.ι ''ᵁ V) m n) = _ at h'
  rw [h']
  refine hn'.symm.trans ?_
  change (((adj U.toScheme).unit.app (presheaf (M.restrict U.ι) (N.restrict U.ι))).app (op V))
    (((modulePresheafTensorRestrict U M.val N.val).hom.app (op V))
      (m ⊗ₜ[Γ(X,U.ι ''ᵁ V)] n)) = _
  exact congrArg (fun t => (((adj U.toScheme).unit.app
    (presheaf (M.restrict U.ι) (N.restrict U.ι))).app (op V)) t)
      (presheaf_restrict_pure U M N V m n)

lemma restrict_pure_inv (U : X.Opens) (M N : X.Modules) (V : U.toScheme.Opens)
    (m : M.val.obj (op (U.ι ''ᵁ V))) (n : N.val.obj (op (U.ι ''ᵁ V))) :
    (moduleTensorRestrict U M N).inv.app V (pure (M.restrict U.ι) (N.restrict U.ι) V m n) =
      pure M N (U.ι ''ᵁ V) m n := by
  have h := congrArg (fun t => (moduleTensorRestrict U M N).inv.app V t)
    (restrict_pure U M N V m n).symm
  refine h.trans ?_
  exact congrArg (fun q => q.app V (pure M N (U.ι ''ᵁ V) m n))
    (moduleTensorRestrict U M N).hom_inv_id

lemma restrict_hom_ext (U : X.Opens) {M N : X.Modules} {P : U.toScheme.Modules}
    {f g : (moduleTensor X M N).restrict U.ι ⟶ P}
    (h : ∀ (V : U.toScheme.Opens) (m : M.val.obj (op (U.ι ''ᵁ V)))
      (n : N.val.obj (op (U.ι ''ᵁ V))), f.app V (pure M N (U.ι ''ᵁ V) m n) =
      g.app V (pure M N (U.ι ''ᵁ V) m n)) : f = g := by
  apply (cancel_epi (moduleTensorRestrict U M N).inv).mp
  apply hom_ext (M := M.restrict U.ι) (N := N.restrict U.ι)
  intro V m n
  change f.app V ((moduleTensorRestrict U M N).inv.app V (pure _ _ V m n)) =
    g.app V ((moduleTensorRestrict U M N).inv.app V (pure _ _ V m n))
  exact (congrArg (fun x => f.app V x) (restrict_pure_inv U M N V m n)).trans
    ((h V m n).trans (congrArg (fun x => g.app V x) (restrict_pure_inv U M N V m n)).symm)

lemma restrict_map (U : X.Opens) {M N P Q : X.Modules}
    (a : M ⟶ P) (b : N ⟶ Q) :
    (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap a b) ≫
      (moduleTensorRestrict U P Q).hom =
    (moduleTensorRestrict U M N).hom ≫
      moduleTensorMap ((Scheme.Modules.restrictFunctor U.ι).map a)
        ((Scheme.Modules.restrictFunctor U.ι).map b) := by
  apply restrict_hom_ext U
  intro V m n
  change (moduleTensorRestrict U P Q).hom.app V
    ((moduleTensorMap a b).app (U.ι ''ᵁ V) (pure M N (U.ι ''ᵁ V) m n)) =
    (moduleTensorMap _ _).app V ((moduleTensorRestrict U M N).hom.app V
      (pure M N (U.ι ''ᵁ V) m n))
  exact (congrArg (fun x => (moduleTensorRestrict U P Q).hom.app V x)
    (map_pure a b (U.ι ''ᵁ V) m n)).trans
    ((restrict_pure U P Q V (a.app (U.ι ''ᵁ V) m) (b.app (U.ι ''ᵁ V) n)).trans
      ((map_pure ((Scheme.Modules.restrictFunctor U.ι).map a)
        ((Scheme.Modules.restrictFunctor U.ι).map b) V m n).symm.trans
        (congrArg (fun x => (moduleTensorMap ((Scheme.Modules.restrictFunctor U.ι).map a)
          ((Scheme.Modules.restrictFunctor U.ι).map b)).app V x)
          (restrict_pure U M N V m n)).symm))

lemma unit_pure (M : X.Modules) (U : X.Opens) (a : Γ(X,U)) (m : M.val.obj (op U)) :
    (moduleTensorUnit M).hom.app U (pure (structureSheaf X) M U a m) = a • m := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  have h := ((adj X).homEquiv _ _).apply_symm_apply (λ_ M.val).hom
  change (adj X).homEquiv _ M (moduleTensorUnit M).hom = (λ_ M.val).hom at h
  exact congrArg (fun q => q.app (op U) (a ⊗ₜ[Γ(X,U)] m)) h

lemma right_unit_pure (M : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) (a : Γ(X,U)) :
    (moduleTensorRightUnit M).hom.app U (pure M (structureSheaf X) U m a) = a • m := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  have h := ((adj X).homEquiv _ _).apply_symm_apply (ρ_ M.val).hom
  change (adj X).homEquiv _ M (moduleTensorRightUnit M).hom = (ρ_ M.val).hom at h
  exact congrArg (fun q => q.app (op U) (m ⊗ₜ[Γ(X,U)] a)) h

end PiExponentSeshadri.TensorPure

end

end OAI
