import OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficients

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

lemma tensor_unit_end {C : Type*} [Category C] [MonoidalCategory C]
    (f g : 𝟙_ C ⟶ 𝟙_ C) :
    (f ⊗ₘ g) ≫ (λ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom ≫ (f ≫ g) := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc, leftUnitor_naturality, ← Category.assoc,
    unitors_equal, rightUnitor_naturality, Category.assoc]

lemma moduleTensorUnit_scalar (f g : structureSheaf X ⟶ structureSheaf X) :
    moduleTensorMap f g ≫ (moduleTensorUnit (structureSheaf X)).hom =
      (moduleTensorUnit (structureSheaf X)).hom ≫ (f ≫ g) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let G : X.Modules ⥤ PresheafOfModules X.ringCatSheaf.obj :=
    SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  let ε : G ⋙ F ⟶ 𝟭 X.Modules :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit
  have h : (f.val ⊗ₘ g.val) ≫ (λ_ (structureSheaf X).val).hom =
      (λ_ (structureSheaf X).val).hom ≫ (f ≫ g).val := by
    let f₀ : 𝟙_ (PresheafOfModules X.ringCatSheaf.obj) ⟶
        𝟙_ (PresheafOfModules X.ringCatSheaf.obj) := f.val
    let g₀ : 𝟙_ (PresheafOfModules X.ringCatSheaf.obj) ⟶
        𝟙_ (PresheafOfModules X.ringCatSheaf.obj) := g.val
    exact tensor_unit_end f₀ g₀
  change F.map (f.val ⊗ₘ g.val) ≫ (F.map (λ_ (structureSheaf X).val).hom ≫ ε.app (structureSheaf X)) =
    (F.map (λ_ (structureSheaf X).val).hom ≫ ε.app (structureSheaf X)) ≫ (f ≫ g)
  erw [← Category.assoc, ← F.map_comp, h, F.map_comp, Category.assoc, Category.assoc]
  congr 1
  exact ε.naturality (f ≫ g)

def endPower (f : structureSheaf X ⟶ structureSheaf X) : ℕ → (structureSheaf X ⟶ structureSheaf X)
  | 0 => 𝟙 _
  | n + 1 => f ≫ endPower f n

lemma endValue_endPower (f : structureSheaf X ⟶ structureSheaf X) (n : ℕ) :
    endValue (endPower f n) = endValue f ^ n := by
  induction n with
  | zero =>
    change (1 : Γ(X, ⊤)) = endValue f ^ 0
    exact (pow_zero _).symm
  | succ n hn =>
    calc
      endValue (endPower f (n + 1)) = endValue f * endValue (endPower f n) :=
        endValue_comp f (endPower f n)
      _ = endValue f * endValue f ^ n := congrArg (endValue f * ·) hn
      _ = _ := (pow_succ' _ _).symm

lemma moduleTensorUnit_natural {M N : X.Modules} (g : M ⟶ N) :
    moduleTensorMap (𝟙 (structureSheaf X)) g ≫ (moduleTensorUnit N).hom =
      (moduleTensorUnit M).hom ≫ g := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let G : X.Modules ⥤ PresheafOfModules X.ringCatSheaf.obj :=
    SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  let ε : G ⋙ F ⟶ 𝟭 X.Modules :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit
  change F.map ((𝟙 (structureSheaf X).val) ⊗ₘ g.val) ≫
    (F.map (λ_ N.val).hom ≫ ε.app N) =
    (F.map (λ_ M.val).hom ≫ ε.app M) ≫ g
  have h : ((𝟙 (structureSheaf X).val) ⊗ₘ g.val) ≫ (λ_ N.val).hom =
      (λ_ M.val).hom ≫ g.val := by
    rw [id_tensorHom]
    exact leftUnitor_naturality g.val
  have hF : F.map (𝟙 (structureSheaf X).val ⊗ₘ g.val) ≫ F.map (λ_ N.val).hom =
      F.map (λ_ M.val).hom ≫ F.map g.val :=
    (F.map_comp _ _).symm.trans ((congrArg F.map h).trans (F.map_comp _ _))
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ ε.app N) hF).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (F.map (λ_ M.val).hom ≫ ·) (ε.naturality g)).trans ?_
  exact (Category.assoc _ _ _).symm

lemma modulePowMap_unitPower (f : structureSheaf X ⟶ structureSheaf X) (n : ℕ) :
    modulePowMap f n ≫ (unitPowerIso n).hom =
      (unitPowerIso n).hom ≫ endPower f n := by
  induction n with
  | zero =>
    change 𝟙 (structureSheaf X) ≫ 𝟙 (structureSheaf X) = 𝟙 (structureSheaf X) ≫ 𝟙 (structureSheaf X)
    rfl
  | succ n hn =>
    change moduleTensorMap f (modulePowMap f n) ≫
      ((moduleTensorUnit _).hom ≫ (unitPowerIso n).hom) =
        ((moduleTensorUnit _).hom ≫ (unitPowerIso n).hom) ≫ (f ≫ endPower f n)
    calc
      _ = moduleTensorMap f (modulePowMap f n) ≫
          moduleTensorMap (𝟙 (structureSheaf X)) (unitPowerIso n).hom ≫
            (moduleTensorUnit (structureSheaf X)).hom := by
        rw [moduleTensorUnit_natural]
      _ = moduleTensorMap f ((unitPowerIso n).hom ≫ endPower f n) ≫
            (moduleTensorUnit (structureSheaf X)).hom := by
        rw [← Category.assoc, ← moduleTensorMap_comp, Category.comp_id, hn]
      _ = moduleTensorMap (𝟙 (structureSheaf X)) (unitPowerIso n).hom ≫
          moduleTensorMap f (endPower f n) ≫ (moduleTensorUnit (structureSheaf X)).hom := by
        rw [← Category.assoc, ← moduleTensorMap_comp, Category.id_comp]
      _ = (moduleTensorUnit (modulePow X (structureSheaf X) n)).hom ≫
          (unitPowerIso n).hom ≫ (f ≫ endPower f n) := by
        rw [moduleTensorUnit_scalar, ← Category.assoc, moduleTensorUnit_natural,
          Category.assoc]
      _ = _ := by simp only [Category.assoc]

def globalPowerFrame {M : X.Modules} (e : M ≅ structureSheaf X) (n : ℕ) :
    modulePow X M n ≅ structureSheaf X :=
  (modulePowFunctor n).mapIso e ≪≫ unitPowerIso n

lemma powerSection_coefficient {M : X.Modules} (e : M ≅ structureSheaf X)
    (s : structureSheaf X ⟶ M) (n : ℕ) :
    coefficient (globalPowerFrame e n) (powerSection s n) = coefficient e s ^ n := by
  change endValue ((unitPowerIso n).inv ≫ modulePowMap s n ≫
    (modulePowMap e.hom n ≫ (unitPowerIso n).hom)) = _
  erw [← Category.assoc (modulePowMap s n), ← modulePowMap_comp,
    modulePowMap_unitPower, Iso.inv_hom_id_assoc, endValue_endPower]
  rfl

lemma frameChange_globalPowerFrame {M : X.Modules}
    (e f : M ≅ structureSheaf X) (n : ℕ) :
    (frameChange (globalPowerFrame e n) (globalPowerFrame f n) : Γ(X,⊤)) =
      (frameChange e f : Γ(X,⊤)) ^ n := by
  have h := powerSection_coefficient f e.inv n
  exact h

end
end PiExponentSeshadri.Geometry

end OAI
