import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorLeftExact
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorProjective
import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionComplete
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.BalancedTensor
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
universe u
variable {k R S : Type u} [Field k] [Ring R] [Ring S] [Algebra k R]
variable {F G H : Type u}
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module S F]
  [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F] [IsScalarTower k Rᵐᵒᵖ F]
variable [AddCommGroup G] [Module k G] [Module Rᵐᵒᵖ G] [Module S G]
  [SMulCommClass k S G] [SMulCommClass S Rᵐᵒᵖ G] [IsScalarTower k Rᵐᵒᵖ G]
variable [AddCommGroup H] [Module k H] [Module Rᵐᵒᵖ H] [Module S H]
  [SMulCommClass k S H] [SMulCommClass S Rᵐᵒᵖ H] [IsScalarTower k Rᵐᵒᵖ H]

def mapLeftLinear (a : F →ₗ[Rᵐᵒᵖ] G) (ha : ∀ (s : S) f, a (s • f) = s • a f)
    (M : ModuleCat.{u} R) : BalancedTensor k R F M →ₗ[S] BalancedTensor k R G M where
  __ := (mapLeft (k := k) (M := M) a).toAddHom
  map_smul' s z := by
    change mapLeft (k := k) a (s • z) = s • mapLeft (k := k) a z
    induction z using induction_on with
    | zero => simp
    | tmul f m => simp only [smul_tmul, mapLeft_tmul, ha]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

@[simp] theorem mapLeftLinear_tmul (a : F →ₗ[Rᵐᵒᵖ] G)
    (ha : ∀ (s : S) f, a (s • f) = s • a f) (M : ModuleCat.{u} R) (f : F) (m : M) :
    mapLeftLinear (k := k) a ha M (tmul f m) = tmul (a f) m := rfl

def functor : ModuleCat.{u} R ⥤ ModuleCat.{u} S where
  obj M := ModuleCat.of S (BalancedTensor k R F M)
  map a := ModuleCat.ofHom (mapRight (k := k) (F := F) (S := S) a.hom)
  map_id M := by apply ModuleCat.hom_ext; exact mapRight_id
  map_comp a b := by apply ModuleCat.hom_ext; exact mapRight_comp a.hom b.hom

instance : (functor (k := k) (R := R) (S := S) (F := F)).Additive where
  map_add := by intros; apply ModuleCat.hom_ext; exact mapRight_add _ _

def naturalMap (a : F →ₗ[Rᵐᵒᵖ] G) (ha : ∀ (s : S) f, a (s • f) = s • a f) :
    functor (k := k) (R := R) (S := S) (F := F) ⟶ functor (k := k) (R := R) (S := S) (F := G) where
  app M := ModuleCat.ofHom (mapLeftLinear (k := k) a ha M)
  naturality M N b := by
    apply ModuleCat.hom_ext
    apply leftHom_ext
    intro f m
    rfl

variable {ι : Type*} {c : ComplexShape ι}

def complexMap (a : F →ₗ[Rᵐᵒᵖ] G) (ha : ∀ (s : S) f, a (s • f) = s • a f)
    (P : HomologicalComplex (ModuleCat.{u} R) c) :
    ((functor (k := k) (R := R) (S := S) (F := F)).mapHomologicalComplex c).obj P ⟶
      ((functor (k := k) (R := R) (S := S) (F := G)).mapHomologicalComplex c).obj P where
  f i := (naturalMap (k := k) a ha).app (P.X i)
  comm' i j _ := ((naturalMap (k := k) a ha).naturality (P.d i j)).symm

def complexSequence (a : F →ₗ[Rᵐᵒᵖ] G) (b : G →ₗ[Rᵐᵒᵖ] H)
    (ha : ∀ (s : S) f, a (s • f) = s • a f) (hb : ∀ (s : S) g, b (s • g) = s • b g)
    (hab : b.comp a = 0) (P : HomologicalComplex (ModuleCat.{u} R) c) :
    ShortComplex (HomologicalComplex (ModuleCat.{u} S) c) :=
  ShortComplex.mk (complexMap (k := k) a ha P) (complexMap (k := k) b hb P) (by
    ext i : 1
    apply ModuleCat.hom_ext
    apply leftHom_ext
    intro f m
    change tmul (b (a f)) m = 0
    rw [show b (a f) = 0 from LinearMap.congr_fun hab f, zero_tmul])

theorem complexSequence_shortExact (a : F →ₗ[Rᵐᵒᵖ] G) (b : G →ₗ[Rᵐᵒᵖ] H)
    (ha : ∀ (s : S) f, a (s • f) = s • a f) (hb : ∀ (s : S) g, b (s • g) = s • b g)
    (hab : b.comp a = 0) (hinj : Function.Injective a)
    (hex : Function.Exact a b) (hsurj : Function.Surjective b)
    (P : HomologicalComplex (ModuleCat.{u} R) c)
    [∀ i, Module.Finite R (P.X i)] [∀ i, Module.Projective R (P.X i)] :
    (complexSequence (k := k) a b ha hb hab P).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    exact mapLeft_exact a b hex
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact mapLeft_injective a hinj
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact mapLeft_surjective b hsurj

end ArExplicit.BalancedTensor

end

end OAI
