import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.Restriction
import OAI.AlgebraicGeometry.Seshadri.Sheaves.Frames

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
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
  let ε := (PresheafOfModules.sheafificationAdjunction
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).counit
  have h : (f.val ⊗ₘ g.val) ≫ (λ_ (structureSheaf X).val).hom =
      (λ_ (structureSheaf X).val).hom ≫ (f ≫ g).val := by
    let f₀ : 𝟙_ (PresheafOfModules X.ringCatSheaf.obj) ⟶
        𝟙_ (PresheafOfModules X.ringCatSheaf.obj) := f.val
    let g₀ : 𝟙_ (PresheafOfModules X.ringCatSheaf.obj) ⟶
        𝟙_ (PresheafOfModules X.ringCatSheaf.obj) := g.val
    exact tensor_unit_end f₀ g₀
  change F.map (f.val ⊗ₘ g.val) ≫ (F.map (λ_ (structureSheaf X).val).hom ≫ ε.app (structureSheaf X)) =
    (F.map (λ_ (structureSheaf X).val).hom ≫ ε.app (structureSheaf X)) ≫ (f ≫ g)
  refine Eq.trans (F.map_comp_assoc _ _ _).symm ?_
  refine Eq.trans
    (congrArg (fun morphism => F.map morphism ≫ ε.app (structureSheaf X)) h) ?_
  refine Eq.trans (F.map_comp_assoc _ _ _) ?_
  refine Eq.trans
    (congrArg (fun morphism => F.map (λ_ (structureSheaf X).val).hom ≫ morphism)
      (ε.naturality (f ≫ g))) ?_
  exact (Category.assoc _ _ _).symm

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
  let ε := (PresheafOfModules.sheafificationAdjunction
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).counit
  change F.map ((𝟙 (structureSheaf X).val) ⊗ₘ g.val) ≫
    (F.map (λ_ N.val).hom ≫ ε.app N) =
    (F.map (λ_ M.val).hom ≫ ε.app M) ≫ g
  have h : ((𝟙 (structureSheaf X).val) ⊗ₘ g.val) ≫ (λ_ N.val).hom =
      (λ_ M.val).hom ≫ g.val := by
    rw [id_tensorHom]
    exact leftUnitor_naturality g.val
  refine Eq.trans (F.map_comp_assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun morphism => F.map morphism ≫ ε.app N) h) ?_
  refine Eq.trans (F.map_comp_assoc _ _ _) ?_
  refine Eq.trans
    (congrArg (fun morphism => F.map (λ_ M.val).hom ≫ morphism) (ε.naturality g)) ?_
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
  have section_power : powerSection s n ≫ (globalPowerFrame e n).hom =
      endPower (s ≫ e.hom) n := by
    change ((unitPowerIso n).inv ≫ modulePowMap s n) ≫
      (modulePowMap e.hom n ≫ (unitPowerIso n).hom) = _
    rw [Category.assoc, ← Category.assoc (modulePowMap s n), ← modulePowMap_comp,
      modulePowMap_unitPower, Iso.inv_hom_id_assoc]
  exact (congrArg (fun morphism : structureSheaf X ⟶ structureSheaf X =>
    endValue morphism) section_power).trans (endValue_endPower (s ≫ e.hom) n)

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

def powerRestrictionUnit (U : X.Opens) (n : ℕ) :
    structureSheaf U.toScheme ≅ structureSheaf U.toScheme :=
  (Scheme.Modules.restrictUnitIso U.ι).symm ≪≫
    (Scheme.Modules.restrictFunctor U.ι).mapIso (unitPowerIso n).symm ≪≫
      modulePowRestrict U (structureSheaf X) n ≪≫
        (modulePowFunctor n).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
          unitPowerIso n

lemma restrictPowerSection_factor (U : X.Opens) {M : X.Modules}
    (s : structureSheaf X ⟶ M) (n : ℕ) :
    restrictSection U.ι (powerSection s n) ≫ (modulePowRestrict U M n).hom =
      (powerRestrictionUnit U n).hom ≫
        powerSection (restrictSection U.ι s) n := by
  let restriction : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let unitIso : restriction.obj (structureSheaf X) ≅ structureSheaf U.toScheme :=
    Scheme.Modules.restrictUnitIso U.ι
  change (unitIso.inv ≫ restriction.map ((unitPowerIso n).inv ≫ modulePowMap s n)) ≫
      (modulePowRestrict U M n).hom =
    (unitIso.inv ≫ restriction.map (unitPowerIso n).inv ≫
      (modulePowRestrict U (structureSheaf X) n).hom ≫
      modulePowMap unitIso.hom n ≫
      (unitPowerIso n).hom) ≫
        ((unitPowerIso n).inv ≫ modulePowMap (unitIso.inv ≫ restriction.map s) n)
  rw [restriction.map_comp]
  simp only [Category.assoc]
  rw [modulePowRestrict_natural]
  rw [Iso.hom_inv_id_assoc, ← modulePowMap_comp]
  rw [unitIso.hom_inv_id_assoc]

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Frames
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma coefficient_injective {M : X.Modules} (e : M ≅ O X) :
    Function.Injective (coefficient e) := by
  intro s t h
  apply (cancel_mono e.hom).1
  exact endValue_injective h

lemma coefficient_precompose {M : X.Modules} (e : M ≅ O X)
    (a : O X ⟶ O X) (s : O X ⟶ M) :
    coefficient e (a ≫ s) = endValue a * coefficient e s := by
  change endValue ((a ≫ s) ≫ e.hom) = _
  rw [Category.assoc]
  exact endValue_comp a (s ≫ e.hom)

@[simp] lemma coefficient_scalarEnd {M : X.Modules} (e : M ≅ O X) (a : Γ(X, ⊤)) :
    coefficient e (scalarEnd a ≫ e.inv) = a := by
  simp only [coefficient, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    endValue_scalarEnd]

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

lemma affine_function_denom [IsAffine X] (a : Γ(X, ⊤))
    (f : Γ((X.basicOpen a).toScheme, ⊤)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ g : Γ(X, ⊤),
      (X.basicOpen a).ι.appTop g = f * (X.basicOpen a).ι.appTop a ^ n := by
  obtain ⟨N, g, hg⟩ := IsLocalization.Away.surj a f
  refine ⟨N, fun n hn => ⟨g * a ^ (n - N), ?_⟩⟩
  change algebraMap Γ(X, ⊤) Γ((X.basicOpen a).toScheme, ⊤) (g * a ^ (n - N)) =
    f * algebraMap Γ(X, ⊤) Γ((X.basicOpen a).toScheme, ⊤) a ^ n
  rw [map_mul, map_pow, ← hg, mul_assoc, ← pow_add, Nat.add_sub_of_le hn]

theorem framed_affine_power_extension [IsAffine X] {M : X.Modules}
    (e : M ≅ structureSheaf X) (s : structureSheaf X ⟶ M)
    (f : Γ((X.basicOpen (coefficient e s)).toScheme, ⊤)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : structureSheaf X ⟶ modulePow X M n,
      restrictSection (X.basicOpen (coefficient e s)).ι t =
        scalarEnd f ≫ restrictSection (X.basicOpen (coefficient e s)).ι (powerSection s n) := by
  obtain ⟨N, hN⟩ := affine_function_denom (coefficient e s) f
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨g, hg⟩ := hN n hn
  let eₙ := globalPowerFrame e n
  refine ⟨scalarEnd g ≫ eₙ.inv, ?_⟩
  apply coefficient_injective (restrictFrame (X.basicOpen (coefficient e s)).ι eₙ)
  let φ := (X.basicOpen (coefficient e s)).ι
  have hl : coefficient (restrictFrame φ eₙ) (restrictSection φ (scalarEnd g ≫ eₙ.inv)) =
      φ.appTop g :=
    (coefficient_restrict φ eₙ _).trans (congrArg φ.appTop (coefficient_scalarEnd eₙ g))
  have hr : coefficient (restrictFrame φ eₙ) (scalarEnd f ≫ restrictSection φ (powerSection s n)) =
      f * φ.appTop (coefficient e s) ^ n := by
    calc
      _ = endValue (scalarEnd f) * coefficient (restrictFrame φ eₙ)
          (restrictSection φ (powerSection s n)) := coefficient_precompose _ _ _
      _ = f * φ.appTop (coefficient eₙ (powerSection s n)) :=
        congrArg₂ (· * ·) (endValue_scalarEnd f) (coefficient_restrict φ eₙ _)
      _ = f * φ.appTop (coefficient e s ^ n) :=
        congrArg (fun x => f * φ.appTop x) (powerSection_coefficient e s n)
      _ = _ := congrArg (f * ·) (map_pow φ.appTop.hom _ n)
  exact hl.trans (hg.trans hr.symm)

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

def localPowerFrame (U : X.Opens) {M : X.Modules}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (n : ℕ) :
    (modulePow X M n).restrict U.ι ≅ structureSheaf U.toScheme :=
  modulePowRestrict U M n ≪≫ globalPowerFrame e n

lemma local_powerSection_coefficient (U : X.Opens) {M : X.Modules}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (s : structureSheaf X ⟶ M) (n : ℕ) :
    coefficient (localPowerFrame U e n) (restrictSection U.ι (powerSection s n)) =
      endValue (powerRestrictionUnit U n).hom *
        coefficient e (restrictSection U.ι s) ^ n := by
  change coefficient (globalPowerFrame e n)
    (restrictSection U.ι (powerSection s n) ≫ (modulePowRestrict U M n).hom) = _
  calc
    _ = coefficient (globalPowerFrame e n)
        ((powerRestrictionUnit U n).hom ≫ powerSection (restrictSection U.ι s) n) :=
      congrArg (coefficient (globalPowerFrame e n)) (restrictPowerSection_factor U s n)
    _ = endValue (powerRestrictionUnit U n).hom *
        coefficient (globalPowerFrame e n) (powerSection (restrictSection U.ι s) n) :=
      coefficient_precompose _ _ _
    _ = _ := congrArg (endValue (powerRestrictionUnit U n).hom * ·)
      (powerSection_coefficient e _ n)

lemma local_powerSection_coefficient_unit (U : X.Opens) (n : ℕ) :
    IsUnit (endValue (powerRestrictionUnit U n).hom) := by
  have h : IsIso (powerRestrictionUnit U n).hom := inferInstance
  exact (end_isIso_iff (powerRestrictionUnit U n).hom).mp h

end
end MaximalSeshadri.Geometry


end
end
end

end OAI
