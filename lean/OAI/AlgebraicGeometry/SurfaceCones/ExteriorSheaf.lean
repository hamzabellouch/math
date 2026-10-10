import Mathlib

namespace OAI

/-! Localization of bilinear and alternating forms. -/
noncomputable section
open LinearMap
namespace ActualExterior
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (U : Submonoid R) [IsLocalization U S]
variable {M M' N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [Module S M'] [IsScalarTower R S M']
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  (f : M →ₗ[R] M') [IsLocalizedModule U f]
include U S
lemma targetUnits (s : U) : IsUnit (algebraMap R (Module.End R N) s) := by
  let := isLocalizedModule_id U N S
  exact IsLocalizedModule.map_units (LinearMap.id : N →ₗ[R] N) s

/-- The localized linear-map universal property, linear in its input. -/
def liftLinear : (M →ₗ[R] N) →ₗ[R] (M' →ₗ[S] N) where
  toFun g := (IsLocalizedModule.lift U f g (targetUnits (S := S) U)).extendScalarsOfIsLocalization U S
  map_add' g h := by
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.ext U f (targetUnits (S := S) U)
    ext x
    simp only [LinearMap.restrictScalars_apply, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.extendScalarsOfIsLocalization_apply', IsLocalizedModule.lift_apply]
  map_smul' r g := by
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.ext U f (targetUnits (S := S) U)
    ext x
    simp only [LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.extendScalarsOfIsLocalization_apply', IsLocalizedModule.lift_apply,
      RingHom.id_apply]

@[simp] lemma liftLinear_apply (g : M →ₗ[R] N) (x : M) :
    liftLinear (S := S) U f g (f x) = g x := IsLocalizedModule.lift_apply U f g (targetUnits (S := S) U) x

/-- Extend a bilinear form in both arguments. -/
def liftBilinear (b : M →ₗ[R] M →ₗ[R] N) : M' →ₗ[S] M' →ₗ[S] N :=
  liftLinear (S := S) U f ((liftLinear (S := S) U f).comp b)

@[simp] lemma liftBilinear_apply (b : M →ₗ[R] M →ₗ[R] N) (x y : M) :
    liftBilinear (S := S) U f b (f x) (f y) = b x y := by
  simp only [liftBilinear, liftLinear_apply, LinearMap.comp_apply]

lemma liftBilinear_isAlt (b : M →ₗ[R] M →ₗ[R] N) (hb : b.IsAlt) :
    (liftBilinear (S := S) U f b).IsAlt := by
  intro x
  obtain ⟨⟨m,s⟩, hs⟩ := IsLocalizedModule.surj U f x
  have h : (algebraMap R S s)^2 • (liftBilinear (S := S) U f b x x) = 0 := by
    calc
      _ = liftBilinear (S := S) U f b
          (algebraMap R S s • x) (algebraMap R S s • x) := by
        simp only [map_smul, LinearMap.smul_apply, smul_smul, pow_two]
      _ = liftBilinear (S := S) U f b (f m) (f m) := by
        rw [algebraMap_smul]
        change liftBilinear (S := S) U f b (s • x) (s • x) = _
        rw [hs]
      _ = 0 := (liftBilinear_apply (S := S) U f b m m).trans (hb m)

  exact (IsLocalization.map_units S s).pow 2 |>.smul_left_cancel.mp (by simpa using h)
end ActualExterior

end

noncomputable section
namespace ActualExterior
variable {M : Type*}

lemma update_pair_zero [DecidableEq (Fin 2)] (x y z : M) :
    Function.update ![x,y] 0 z = ![z,y] := by
  ext i
  fin_cases i <;> simp
lemma update_pair_one [DecidableEq (Fin 2)] (x y z : M) :
    Function.update ![x,y] 1 z = ![x,z] := by
  ext i
  fin_cases i <;> simp

variable {R : Type*} [CommRing R] {N : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

def alternatingToBilinear (a : M [⋀^Fin 2]→ₗ[R] N) : M →ₗ[R] M →ₗ[R] N :=
  LinearMap.mk₂ R (fun x y => a ![x,y])
    (by intro x x' y; simpa only [update_pair_zero] using a.map_update_add ![0,y] 0 x x')
    (by intro r x y; simpa only [update_pair_zero] using a.map_update_smul ![0,y] 0 r x)
    (by intro x y y'; simpa only [update_pair_one] using a.map_update_add ![x,0] 1 y y')
    (by intro r x y; simpa only [update_pair_one] using a.map_update_smul ![x,0] 1 r y)

lemma alternatingToBilinear_isAlt (a : M [⋀^Fin 2]→ₗ[R] N) :
    (alternatingToBilinear a).IsAlt := by
  intro x
  exact a.map_eq_zero_of_eq ![x,x] (i := 0) (j := 1) (by simp) (by decide)

/-- Alternating bilinear maps expressed in the standard exterior
universal-property format. -/
def bilinearToAlternating (b : M →ₗ[R] M →ₗ[R] N) (hb : b.IsAlt) :
    M [⋀^Fin 2]→ₗ[R] N where
  toFun z := b (z 0) (z 1)
  map_update_add' z i x y := by
    fin_cases i
    · change b (Function.update z 0 (x+y) 0) (Function.update z 0 (x+y) 1) = _
      simp
    · change b (Function.update z 1 (x+y) 0) (Function.update z 1 (x+y) 1) = _
      simp
  map_update_smul' z i r x := by
    fin_cases i
    · change b (Function.update z 0 (r • x) 0) (Function.update z 0 (r • x) 1) = _
      simp
    · change b (Function.update z 1 (r • x) 0) (Function.update z 1 (r • x) 1) = _
      simp
  map_eq_zero_of_eq' z i j h hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change z 0 = z 1 at h
      rw [h]; exact hb (z 1)
    · change z 1 = z 0 at h
      rw [h]; exact hb (z 0)
    · exact (hij rfl).elim

@[simp] lemma bilinearToAlternating_apply (b : M →ₗ[R] M →ₗ[R] N) (hb) (z) :
    bilinearToAlternating b hb z = b (z 0) (z 1) := rfl
@[simp] lemma alternatingToBilinear_apply (a : M [⋀^Fin 2]→ₗ[R] N) (x y) :
    alternatingToBilinear a x y = a ![x,y] := rfl
lemma bilinearToAlternating_alternatingToBilinear (a : M [⋀^Fin 2]→ₗ[R] N) :
    bilinearToAlternating (alternatingToBilinear a) (alternatingToBilinear_isAlt a) = a := by
  ext z
  change a ![z 0,z 1] = a z
  congr 1
  ext i
  fin_cases i <;> rfl

variable {S : Type*} [CommRing S] [Algebra R S]
  (U : Submonoid R) [IsLocalization U S]
variable {M' : Type*} [AddCommGroup M'] [Module R M'] [Module S M'] [IsScalarTower R S M']
  [Module S N] [IsScalarTower R S N]
  (f : M →ₗ[R] M') [IsLocalizedModule U f]

def liftAlternatingTwo (a : M [⋀^Fin 2]→ₗ[R] N) : M' [⋀^Fin 2]→ₗ[S] N :=
  bilinearToAlternating (liftBilinear (S := S) U f (alternatingToBilinear a))
    (liftBilinear_isAlt U f _ (alternatingToBilinear_isAlt a))

@[simp] lemma liftAlternatingTwo_apply (a : M [⋀^Fin 2]→ₗ[R] N) (z : Fin 2 → M) :
    liftAlternatingTwo (S := S) U f a (f ∘ z) = a z := by
  rw [liftAlternatingTwo,bilinearToAlternating_apply]
  change liftBilinear (S := S) U f (alternatingToBilinear a) (f (z 0)) (f (z 1)) = a z
  rw [liftBilinear_apply,alternatingToBilinear_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

include U in
lemma alternatingTwo_ext_localized {a b : M' [⋀^Fin 2]→ₗ[S] N}
    (h : ∀ z : Fin 2 → M, a (f ∘ z) = b (f ∘ z)) : a = b := by
  have hbil : alternatingToBilinear a = alternatingToBilinear b := by
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.ext U f (targetUnits (S := S) U)
    apply LinearMap.ext
    intro x
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.ext U f (targetUnits (S := S) U)
    ext y
    change a ![f x, f y] = b ![f x, f y]
    have hz : f ∘ ![x,y] = ![f x,f y] := by ext i; fin_cases i <;> rfl
    simpa only [hz] using h ![x,y]
  ext z
  have hz := DFunLike.congr_fun (DFunLike.congr_fun hbil (z 0)) (z 1)
  have heta : ![z 0,z 1] = z := by ext i; fin_cases i <;> rfl
  simpa only [alternatingToBilinear_apply, heta] using hz

end ActualExterior


/-! Localization of second exterior powers. -/
namespace ActualExterior
open exteriorPower
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (U : Submonoid R) [IsLocalization U S]
  {M N P : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
  (f : M →ₗ[R] N) [IsLocalizedModule U f]

local instance : Module R (⋀[S]^2 N) := Module.compHom _ (algebraMap R S)
local instance : IsScalarTower R S (⋀[S]^2 N) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

def restrictAlternatingTwo (a : N [⋀^Fin 2]→ₗ[S] P) : N [⋀^Fin 2]→ₗ[R] P where
  __ := a.toMultilinearMap.restrictScalars R
  map_eq_zero_of_eq' := a.map_eq_zero_of_eq

@[simp] lemma restrictAlternatingTwo_apply (a : N [⋀^Fin 2]→ₗ[S] P) (z) :
    restrictAlternatingTwo (R := R) a z = a z := rfl

/-- Exterior vectors transform by the localization of their entries. -/
def localizationTwoMap : (⋀[R]^2 M) →ₗ[R] (⋀[S]^2 N) :=
  alternatingMapLinearEquiv
    ((@restrictAlternatingTwo R S _ _ _ N (⋀[S]^2 N) _ _ _ _ _ _ _
      (IsScalarTower.of_compHom R S _) (ιMulti S 2)).compLinearMap f)

@[simp] lemma localizationTwoMap_mk (z : Fin 2 → M) :
    localizationTwoMap (S := S) f (ιMulti R 2 z) = ιMulti S 2 (f ∘ z) := by
  simp only [localizationTwoMap, alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply, Function.comp_def]
  rfl

variable (g : (⋀[R]^2 M) →ₗ[R] P) [IsLocalizedModule U g]

def localizationTwoInverse : (⋀[S]^2 N) →ₗ[S] P :=
  alternatingMapLinearEquiv (liftAlternatingTwo (S := S) U f
    (g.compAlternatingMap (ιMulti R 2)))

omit [IsLocalizedModule U g] in
@[simp] lemma localizationTwoInverse_mk (z : Fin 2 → M) :
    localizationTwoInverse (S := S) U f g (ιMulti S 2 (f ∘ z)) = g (ιMulti R 2 z) := by
  simp only [localizationTwoInverse,alternatingMapLinearEquiv_apply_ιMulti,
    liftAlternatingTwo_apply, LinearMap.compAlternatingMap_apply]

def localizationTwoForward : P →ₗ[S] (⋀[S]^2 N) :=
  @liftLinear R S _ _ _ U _ (⋀[R]^2 M) P (⋀[S]^2 N) _ _ _ _ _ _ _ _ _
    (IsScalarTower.of_compHom R S _) g _ (localizationTwoMap (S := S) f)

omit [IsLocalizedModule U f] in
@[simp] lemma localizationTwoForward_mk (x : ⋀[R]^2 M) :
    localizationTwoForward (S := S) U f g (g x) = localizationTwoMap (S := S) f x :=
  @liftLinear_apply R S _ _ _ U _ (⋀[R]^2 M) P (⋀[S]^2 N) _ _ _ _ _ _ _ _ _
    (IsScalarTower.of_compHom R S _) g _ (localizationTwoMap (S := S) f) x

lemma localizationTwoInverse_forward :
    (localizationTwoInverse (S := S) U f g).comp (localizationTwoForward (S := S) U f g) = LinearMap.id := by
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.ext U g (targetUnits (S := S) U)
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro z
  simp only [LinearMap.comp_apply,LinearMap.restrictScalars_apply,
    LinearMap.compAlternatingMap_apply, localizationTwoForward_mk, localizationTwoMap_mk,
    localizationTwoInverse_mk, LinearMap.id_apply]

lemma localizationTwoForward_inverse :
    (localizationTwoForward (S := S) U f g).comp (localizationTwoInverse (S := S) U f g) = LinearMap.id := by
  apply exteriorPower.linearMap_ext
  refine @alternatingTwo_ext_localized M R _ (⋀[S]^2 N) _ _ _ _ S _ _ U _ N
    _ _ _ _ _ (IsScalarTower.of_compHom R S _) f _ _ _ ?_
  intro z
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    localizationTwoInverse_mk, localizationTwoForward_mk, localizationTwoMap_mk,
    LinearMap.id_apply]

def localizationTwoEquiv : P ≃ₗ[S] (⋀[S]^2 N) :=
  LinearEquiv.ofLinearMap (localizationTwoForward (S := S) U f g)
    (localizationTwoInverse (S := S) U f g)
    (localizationTwoForward_inverse U f g) (localizationTwoInverse_forward U f g)

lemma localizationTwoEquiv_comp :
    ((@LinearEquiv.restrictScalars R S P (⋀[S]^2 N) _ _ _ _ _ _ _ _
      (@LinearMap.IsScalarTower.compatibleSMul P (⋀[S]^2 N) _ _ R S _ _ _ _ _ _ _
        (IsScalarTower.of_compHom R S _)) (localizationTwoEquiv (S := S) U f g))).toLinearMap.comp g =
      localizationTwoMap (S := S) f := by
  apply LinearMap.ext
  intro x
  exact localizationTwoForward_mk U f g x

/- The exterior map is a localization map; the auxiliary localized
module is used only to prove that universal property. -/
include g in
lemma localizationTwoMap_isLocalized : IsLocalizedModule U (localizationTwoMap (S := S) f) := by
  rw [← localizationTwoEquiv_comp U f g]
  exact IsLocalizedModule.of_linearEquiv U g ((@LinearEquiv.restrictScalars R S P (⋀[S]^2 N) _ _ _ _ _ _ _ _
      (@LinearMap.IsScalarTower.compatibleSMul P (⋀[S]^2 N) _ _ R S _ _ _ _ _ _ _
        (IsScalarTower.of_compHom R S _)) (localizationTwoEquiv (S := S) U f g)))

end ActualExterior


open CategoryTheory
namespace ActualExterior
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
  (φ : A →+* B) (M : ModuleCat.{u} A) (N : ModuleCat.{u} B)
  (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (n : ℕ)

def scalarAlternating : M.AlternatingMap
    ((ModuleCat.restrictScalars φ).obj (N.exteriorPower n)) n where
  toFun z := exteriorPower.ιMulti B n (fun i => (f (z i) : N))
  map_update_add' := by
    intro _ z i x y
    change exteriorPower.ιMulti B n ((f.hom : M → N) ∘ Function.update z i (x + y)) =
      exteriorPower.ιMulti B n ((f.hom : M → N) ∘ Function.update z i x) +
        exteriorPower.ιMulti B n ((f.hom : M → N) ∘ Function.update z i y)
    rw [Function.comp_update, Function.comp_update, Function.comp_update]
    erw [map_add, AlternatingMap.map_update_add]
  map_update_smul' := by
    intro _ z i a x
    change exteriorPower.ιMulti B n ((f.hom : M → N) ∘ Function.update z i (a • x)) =
      φ a • exteriorPower.ιMulti B n ((f.hom : M → N) ∘ Function.update z i x)
    rw [Function.comp_update, Function.comp_update]
    erw [map_smul]
    exact (exteriorPower.ιMulti B n).map_update_smul _ i _ _
  map_eq_zero_of_eq' := by
    intro z i j h hij
    exact (exteriorPower.ιMulti B n).map_eq_zero_of_eq _ (congrArg f h) hij

end ActualExterior

end

/-! Exterior powers of presheaves of modules. -/
noncomputable section
open CategoryTheory Opposite
namespace ActualExterior
universe u v
variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
local instance (X : Cᵒᵖ) : CommRing ((R ⋙ forget₂ CommRingCat RingCat).obj X) :=
  inferInstanceAs (CommRing (R.obj X))
variable (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (n : ℕ)

/-- Restriction of exterior vectors, using the given semilinear
restriction maps of the module presheaf. -/
def powerMap {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (M.obj X).exteriorPower n ⟶
      (ModuleCat.restrictScalars (R.map f).hom).obj ((M.obj Y).exteriorPower n) :=
  ModuleCat.exteriorPower.desc (scalarAlternating (R.map f).hom (M.obj X) (M.obj Y) (M.map f) n)

@[simp] lemma powerMap_ι {X Y : Cᵒᵖ} (f : X ⟶ Y) (z : Fin n → M.obj X) :
    powerMap M n f (ModuleCat.exteriorPower.mk (M := M.obj X) z) =
      ModuleCat.exteriorPower.mk (M := M.obj Y) (fun i => (M.map f (z i) : M.obj Y)) :=
  ModuleCat.exteriorPower.desc_mk _ _

/-- Objectwise exterior powers of the sections and their maps. -/
def presheaf : PresheafOfModules.{u} (R ⋙ forget₂ _ _) where
  obj X := (M.obj X).exteriorPower n
  map f := powerMap M n f
  map_id X := by
    apply ModuleCat.exteriorPower.hom_ext
    ext z
    dsimp [ModuleCat.AlternatingMap.postcomp]
    change powerMap M n (𝟙 X) (ModuleCat.exteriorPower.mk (M := M.obj X) z) = _
    erw [powerMap_ι]
    change ModuleCat.exteriorPower.mk (M := M.obj X) (fun i => (M.map (𝟙 X) (z i) : M.obj X)) =
      ModuleCat.exteriorPower.mk (M := M.obj X) z
    apply congrArg (ModuleCat.exteriorPower.mk (M := M.obj X))
    funext i
    rw [M.map_id]; rfl
  map_comp {X Y Z} f g := by
    apply ModuleCat.exteriorPower.hom_ext
    ext z
    dsimp [ModuleCat.AlternatingMap.postcomp]
    change powerMap M n (f ≫ g) (ModuleCat.exteriorPower.mk (M := M.obj X) z) =
      powerMap M n g (powerMap M n f (ModuleCat.exteriorPower.mk (M := M.obj X) z))
    erw [powerMap_ι,powerMap_ι,powerMap_ι]
    apply congrArg (ModuleCat.exteriorPower.mk (M := M.obj Z))
    funext i
    exact M.map_comp_apply f g (z i)

end ActualExterior

end

/-! Exterior powers of sheaves of modules, constructed by sheafification. -/
noncomputable section
open CategoryTheory Opposite
namespace ActualExterior
universe u v
variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
local instance (X : Cᵒᵖ) : CommRing ((R ⋙ forget₂ CommRingCat RingCat).obj X) :=
  inferInstanceAs (CommRing (R.obj X))
variable {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (a : M ⟶ N) (n : ℕ)

lemma naturalityOnWedge {X Y : Cᵒᵖ} (f : X ⟶ Y) (z : Fin n → M.obj X) :
    ModuleCat.exteriorPower.map (a.app Y) n
      (powerMap M n f (ModuleCat.exteriorPower.mk (M := M.obj X) z)) =
      powerMap N n f (ModuleCat.exteriorPower.map (a.app X) n
        (ModuleCat.exteriorPower.mk (M := M.obj X) z)) := by
  let z' : Fin n → M.obj Y := fun i => M.map f (z i)
  let w : Fin n → N.obj X := fun i => a.app X (z i)
  have h₁ : ModuleCat.exteriorPower.map (a.app Y) n
      (powerMap M n f (ModuleCat.exteriorPower.mk (M := M.obj X) z)) =
      ModuleCat.exteriorPower.map (a.app Y) n
        (ModuleCat.exteriorPower.mk (M := M.obj Y) z') :=
    congrArg (ModuleCat.exteriorPower.map (a.app Y) n) (powerMap_ι M n f z)
  have h₂ : ModuleCat.exteriorPower.map (a.app Y) n
      (ModuleCat.exteriorPower.mk (M := M.obj Y) z') =
      ModuleCat.exteriorPower.mk (M := N.obj Y) (fun i => a.app Y (z' i)) :=
    ModuleCat.exteriorPower.map_mk (a.app Y) z'
  have h₃ : ModuleCat.exteriorPower.mk (M := N.obj Y) (fun i => a.app Y (z' i)) =
      ModuleCat.exteriorPower.mk (M := N.obj Y) (fun i => N.map f (w i)) := by
    apply congrArg (ModuleCat.exteriorPower.mk (M := N.obj Y))
    funext i
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp (a.naturality f)) (z i)
  have h₄ : ModuleCat.exteriorPower.mk (M := N.obj Y) (fun i => N.map f (w i)) =
      (powerMap N n f (ModuleCat.exteriorPower.mk (M := N.obj X) w) :
        (N.obj Y).exteriorPower n) := (powerMap_ι N n f w).symm
  have h₅ : (powerMap N n f (ModuleCat.exteriorPower.mk (M := N.obj X) w) :
        (N.obj Y).exteriorPower n) =
      powerMap N n f (ModuleCat.exteriorPower.map (a.app X) n
        (ModuleCat.exteriorPower.mk (M := M.obj X) z)) :=
    congrArg (fun x : (N.obj X).exteriorPower n => (powerMap N n f x : (N.obj Y).exteriorPower n))
      (ModuleCat.exteriorPower.map_mk (a.app X) z).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

def presheafMap : presheaf M n ⟶ presheaf N n where
  app X := ModuleCat.exteriorPower.map (a.app X) n
  naturality {X Y} f := by
    apply ModuleCat.exteriorPower.hom_ext
    ext z
    exact naturalityOnWedge a n f z


variable (R) in
def presheafFunctor (n : ℕ) : PresheafOfModules.{u} (R ⋙ forget₂ _ _) ⥤
    PresheafOfModules.{u} (R ⋙ forget₂ _ _) where
  obj M := presheaf M n
  map a := presheafMap a n
  map_id M := by
    ext X : 1
    apply ModuleCat.exteriorPower.hom_ext
    ext z
    exact ModuleCat.exteriorPower.map_mk (𝟙 (M.obj X)) z
  map_comp {M N P} a b := by
    ext X : 1
    apply ModuleCat.exteriorPower.hom_ext
    ext z
    change ModuleCat.exteriorPower.map ((a ≫ b).app X) n
      (ModuleCat.exteriorPower.mk (M := M.obj X) z) =
      ModuleCat.exteriorPower.map (b.app X) n
        (ModuleCat.exteriorPower.map (a.app X) n
          (ModuleCat.exteriorPower.mk z))
    exact (ModuleCat.exteriorPower.map_mk ((a ≫ b).app X) z).trans
      ((ModuleCat.exteriorPower.map_mk (b.app X) (fun i => a.app X (z i))).symm.trans
        (congrArg (ModuleCat.exteriorPower.map (b.app X) n)
          (ModuleCat.exteriorPower.map_mk (a.app X) z).symm))

open AlgebraicGeometry
abbrev schemeSheafification (X : Scheme.{u}) :
    PresheafOfModules.{u} X.ringCatSheaf.obj ⥤ X.Modules :=
  PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)

/-- The sheaf of exterior powers. -/
def sheafFunctor (X : Scheme.{u}) (n : ℕ) : X.Modules ⥤ X.Modules :=
  SheafOfModules.forget _ ⋙ presheafFunctor X.sheaf.obj n ⋙
    schemeSheafification X

end ActualExterior

end

noncomputable section
open CategoryTheory
namespace ActualExterior
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
  (φ : A →+* B) (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) (n : ℕ)

def semilinearMap (f : M →ₛₗ[φ] N) :
    M.exteriorPower n →ₛₗ[φ] N.exteriorPower n :=
  (ModuleCat.semilinearMapAddEquiv φ (M.exteriorPower n) (N.exteriorPower n)).symm
    (ModuleCat.exteriorPower.desc
      (scalarAlternating φ M N (ModuleCat.semilinearMapAddEquiv φ M N f) n))

@[simp] lemma semilinearMap_mk (f : M →ₛₗ[φ] N) (z : Fin n → M) :
    semilinearMap φ M N n f (ModuleCat.exteriorPower.mk (M := M) z) =
      ModuleCat.exteriorPower.mk (M := N) (f ∘ z) :=
  ModuleCat.exteriorPower.desc_mk _ _

/-- Extensionality for semilinear maps on the exterior power. -/
lemma semilinear_ext {P : ModuleCat.{u} B} {a b : M.exteriorPower n →ₛₗ[φ] P}
    (h : ∀ z : Fin n → M, a (ModuleCat.exteriorPower.mk z) =
      b (ModuleCat.exteriorPower.mk z)) : a = b := by
  apply (ModuleCat.semilinearMapAddEquiv φ (M.exteriorPower n) P).injective
  apply ModuleCat.exteriorPower.hom_ext
  ext z
  exact h z

variable (e : A ≃+* B)
local instance : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
local instance : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e

lemma semilinearMap_left_inverse (f : M ≃ₛₗ[e.toRingHom] N) :
    Function.LeftInverse (semilinearMap e.symm.toRingHom N M n f.symm.toLinearMap)
      (semilinearMap e.toRingHom M N n f.toLinearMap) := by
  intro x
  let a := semilinearMap e.toRingHom M N n f.toLinearMap
  let b := semilinearMap e.symm.toRingHom N M n f.symm.toLinearMap
  have h : b.comp a = LinearMap.id := by
    apply exteriorPower.linearMap_ext
    ext z
    change b (a (ModuleCat.exteriorPower.mk (M := M) z)) =
      ModuleCat.exteriorPower.mk (M := M) z
    simp only [a,b,semilinearMap_mk]
    congr 1
    funext i
    exact f.symm_apply_apply (z i)
  exact DFunLike.congr_fun h x

/-- exterior powers commute with semilinear coordinate
isomorphisms, including all open-restriction coefficient-ring isomorphisms. -/
def semilinearEquiv (f : M ≃ₛₗ[e.toRingHom] N) :
    M.exteriorPower n ≃ₛₗ[e.toRingHom] N.exteriorPower n where
  __ := semilinearMap e.toRingHom M N n f.toLinearMap
  invFun := semilinearMap e.symm.toRingHom N M n f.symm.toLinearMap
  left_inv := semilinearMap_left_inverse M N n e f
  right_inv := semilinearMap_left_inverse N M n e.symm f.symm

end ActualExterior

end

end OAI
