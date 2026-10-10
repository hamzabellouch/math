import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.DivisorPresheaves

namespace OAI

/-! Multiplier Sheaves. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace

namespace NumericalDimensionOne
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]

theorem divisorFunctionPresheaf_isSheaf (D : WeilDivisor X) :
    (divisorFunctionPresheaf D).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).mpr
  exact subpresheafToTypes.isSheaf (divisorFunctionLocal D)

theorem divisorFunctionLocal_iff {D : WeilDivisor X} {U : X.Opens} [Nonempty U]
    (f : U → X.functionField) :
    (divisorFunctionLocal D).pred f ↔
      ∃ a : X.functionField, (∀ x : U, f x = a) ∧ IsDivisorSectionOn D U a := by
  classical
  constructor
  · intro hf
    have hη : genericPoint X ∈ U :=
      (genericPoint_specializes (Classical.arbitrary U).1).mem_open U.isOpen
        (Classical.arbitrary U).2
    let a := f ⟨genericPoint X,hη⟩
    have hconst : ∀ x : U, f x = a := by
      intro x
      obtain ⟨V,hx,i,b,hb,hs⟩ := hf x
      have hηV : genericPoint X ∈ V :=
        (genericPoint_specializes x.1).mem_open V.isOpen hx
      exact (hb ⟨x,hx⟩).trans (hb ⟨genericPoint X,hηV⟩).symm
    refine ⟨a,hconst,?_⟩
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      intro p hp
      obtain ⟨V,hpV,i,b,hb,hs⟩ := hf ⟨p,hp⟩
      have hba : b = a := (hb ⟨p,hpV⟩).symm.trans (hconst (i ⟨p,hpV⟩))
      subst b
      rcases hs with hz | hs
      · exact (ha hz).elim
      · exact hs p hpV
  · intro h
    exact PrelocalPredicate.sheafifyOf (P := divisorFunctionPrelocal D) h

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace

namespace NumericalDimensionOne
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
noncomputable def divisorFunctionSheaf (D : WeilDivisor X) : TopCat.Sheaf AddCommGrpCat X :=
  ⟨divisorFunctionPresheaf D,divisorFunctionPresheaf_isSheaf D⟩

noncomputable def divisorSectionsToSheaf (D : WeilDivisor X) :
    divisorSections D →+ (divisorFunctionSheaf D).obj.obj (op (⊤ : X.Opens)) where
  toFun a := ⟨fun _ => a.1,PrelocalPredicate.sheafifyOf (P := divisorFunctionPrelocal D)
    ⟨a.1,fun _ => rfl,by
      rcases a.property with hz | hs
      · exact Or.inl hz
      · exact Or.inr (fun p _ => hs p)⟩⟩
  map_zero' := rfl
  map_add' := fun _ _ => rfl
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace

namespace NumericalDimensionOne
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]

theorem divisorSectionsToSheaf_bijective (D : WeilDivisor X) :
    Function.Bijective (divisorSectionsToSheaf D) := by
  constructor
  · intro a b h
    exact Subtype.ext (congrArg (fun s => s.1 ⟨genericPoint X,trivial⟩) h)
  · intro f
    obtain ⟨a,ha,hs⟩ := (divisorFunctionLocal_iff f.1).mp f.2
    have hsec : IsDivisorSection D a := by
      rcases hs with hz | hs
      · exact Or.inl hz
      · exact Or.inr (fun p => hs p trivial)
    refine ⟨⟨a,hsec⟩,?_⟩
    exact Subtype.ext (funext (fun x => (ha x).symm))

noncomputable def divisorGlobalSectionsEquiv (D : WeilDivisor X) :
    divisorSections D ≃+ (divisorFunctionSheaf D).obj.obj (op (⊤ : X.Opens)) :=
  AddEquiv.ofBijective (divisorSectionsToSheaf D) (divisorSectionsToSheaf_bijective D)

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace

namespace NumericalDimensionOne
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]

noncomputable def regularFunctionValues (U : X.Opens) : Γ(X,U) →+* (U → X.functionField) where
  toFun a x := algebraMap (X.presheaf.stalk x.1) X.functionField (X.presheaf.germ U x x.2 a)
  map_zero' := by ext x; simp
  map_one' := by ext x; simp
  map_add' := by intros; ext x; simp
  map_mul' := by intros; ext x; simp

omit [IsLocallyNoetherian X] [StalkwiseNormal X] in
lemma regularFunctionValues_eq [IsLocallyNoetherian X] [StalkwiseNormal X]
    (U : X.Opens) [Nonempty U] (a : Γ(X,U)) (x : U) :
    regularFunctionValues U a x = X.germToFunctionField U a :=
  X.algebraMap_germ_eq_germToFunctionField x.2 a

noncomputable instance divisorFunctionRingModule (U : X.Opens) : Module Γ(X,U) (U → X.functionField) :=
  Module.compHom _ (regularFunctionValues U)

omit [IsLocallyNoetherian X] [StalkwiseNormal X] in
lemma divisorFunction_smul_apply [IsLocallyNoetherian X] [StalkwiseNormal X]
    (U : X.Opens) (a : Γ(X,U)) (f : U → X.functionField) (x : U) :
    (a • f) x = regularFunctionValues U a x * f x := rfl

omit [StalkwiseNormal X] in
lemma divisorSectionOn_smul [StalkwiseNormal X] {D : WeilDivisor X} {U : X.Opens} [Nonempty U]
    (a : Γ(X,U)) {f : X.functionField} (hf : IsDivisorSectionOn D U f) :
    IsDivisorSectionOn D U (X.germToFunctionField U a * f) := by
  by_cases ha : a = 0
  · exact Or.inl (by simp [ha])
  rcases hf with rfl | hf
  · exact Or.inl (mul_zero _)
  right
  intro p hp
  have h := X.ord_le_smul (x := p.1) (U := U) hp ha f
  change X.ord f p.1 ≤ X.ord (X.germToFunctionField U a * f) p.1 at h
  have := hf p hp
  omega

lemma divisorFunctionLocal_smul (D : WeilDivisor X) (U : X.Opens)
    (a : Γ(X,U)) (f : U → X.functionField) (hf : (divisorFunctionLocal D).pred f) :
    (divisorFunctionLocal D).pred (a • f) := by
  classical
  by_cases hU : Nonempty U
  · let := hU
    obtain ⟨b,hb,hs⟩ := (divisorFunctionLocal_iff f).mp hf
    apply (divisorFunctionLocal_iff _).mpr
    refine ⟨X.germToFunctionField U a * b,?_,divisorSectionOn_smul a hs⟩
    intro x
    rw [divisorFunction_smul_apply,regularFunctionValues_eq,hb]
  · have hf0 : a • f = 0 := by
      funext x
      exact (hU ⟨x⟩).elim
    rw [hf0]
    exact divisorFunctionLocal_zero D U

noncomputable def divisorFunctionSubmodule (D : WeilDivisor X) (U : X.Opens) :
    Submodule Γ(X,U) (U → X.functionField) where
  carrier := {f | (divisorFunctionLocal D).pred f}
  zero_mem' := divisorFunctionLocal_zero D U
  add_mem' := divisorFunctionLocal_add D
  smul_mem' := divisorFunctionLocal_smul D U

lemma regularFunctionValues_res {U V : X.Opens} (i : U ⟶ V) (a : Γ(X,V)) (x : U) :
    regularFunctionValues U (X.presheaf.map i.op a) x = regularFunctionValues V a (i x) := by
  let : Nonempty U := ⟨x⟩
  let : Nonempty V := ⟨i x⟩
  rw [regularFunctionValues_eq,regularFunctionValues_eq,germToFunctionField_restrict]

noncomputable def divisorModulePresheaf (D : WeilDivisor X) :
    PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) where
  obj U := ModuleCat.of _ (divisorFunctionSubmodule D U.unop)
  map {U V} i := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (X.presheaf.map i).hom).obj
      (ModuleCat.of Γ(X,V.unop) (divisorFunctionSubmodule D V.unop)))
    { toFun := fun f => ⟨fun x => f.1 (i.unop x),
        (divisorFunctionLocal D).res i.unop f.1 f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a f
        apply Subtype.ext
        funext x
        change regularFunctionValues U.unop a (i.unop x) * f.1 (i.unop x) =
          regularFunctionValues V.unop (X.presheaf.map i a) x * f.1 (i.unop x)
        exact congrArg (fun z => z * f.1 (i.unop x))
          (regularFunctionValues_res i.unop a x).symm }

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace

namespace NumericalDimensionOne
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]

theorem divisorModulePresheaf_isSheaf (D : WeilDivisor X) :
    TopCat.Presheaf.IsSheaf (divisorModulePresheaf D).presheaf := by
  exact divisorFunctionPresheaf_isSheaf D

noncomputable def divisorModuleSheaf (D : WeilDivisor X) : SheafOfModules X.ringCatSheaf :=
  ⟨divisorModulePresheaf D,divisorModulePresheaf_isSheaf D⟩

noncomputable def divisorSectionsToModuleSheaf (D : WeilDivisor X) :
    divisorSections D →ₗ[Γ(X,⊤)] divisorFunctionSubmodule D (⊤ : X.Opens) where
  toFun := divisorSectionsToSheaf D
  map_add' := fun _ _ => rfl
  map_smul' := by
    intro a f
    apply Subtype.ext
    funext x
    change (X.germToFunctionField ⊤ a) * f.1 = regularFunctionValues ⊤ a x * f.1
    rw [regularFunctionValues_eq]

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace

namespace NumericalDimensionOne
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
noncomputable def cartierSheafChartMap {D : WeilDivisor X} {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] {g : X.functionField} (hg : g ≠ 0)
    (heq : ∀ p : PrimeDivisor X, p.1 ∈ U → D p = X.ord g p.1) :
    Γ(X,U) →ₗ[Γ(X,U)] divisorFunctionSubmodule D U where
  toFun a := ⟨fun _ => X.germToFunctionField U a / g,
    (divisorFunctionLocal_iff _).mpr
      ⟨X.germToFunctionField U a / g,fun _ => rfl,
        (cartier_local_section_iff hU hg heq _).mpr
          ⟨a,(div_mul_cancel₀ _ hg).symm⟩⟩⟩
  map_add' := by
    intro a b
    apply Subtype.ext
    funext x
    change X.germToFunctionField U (a+b) / g =
      X.germToFunctionField U a / g + X.germToFunctionField U b / g
    rw [map_add,add_div]
  map_smul' := by
    intro a b
    apply Subtype.ext
    funext x
    change X.germToFunctionField U (a*b) / g =
      regularFunctionValues U a x * (X.germToFunctionField U b / g)
    rw [regularFunctionValues_eq,map_mul,mul_div_assoc]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace

namespace NumericalDimensionOne
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]

theorem cartierSheafChartMap_bijective {D : WeilDivisor X} {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] {g : X.functionField} (hg : g ≠ 0)
    (heq : ∀ p : PrimeDivisor X, p.1 ∈ U → D p = X.ord g p.1) :
    Function.Bijective (cartierSheafChartMap hU hg heq) := by
  constructor
  · intro a b h
    have he := congrArg (fun s => s.1 (Classical.arbitrary U)) h
    change X.germToFunctionField U a / g = X.germToFunctionField U b / g at he
    apply X.germToFunctionField_injective U
    exact (div_left_inj' hg).mp he
  · intro f
    obtain ⟨b,hb,hs⟩ := (divisorFunctionLocal_iff f.1).mp f.2
    obtain ⟨a,ha⟩ := (cartier_local_section_iff hU hg heq b).mp hs
    refine ⟨a,?_⟩
    apply Subtype.ext
    funext x
    change X.germToFunctionField U a / g = f.1 x
    rw [ha,mul_div_cancel_right₀ b hg,hb]

noncomputable def cartierSheafChartEquiv {D : WeilDivisor X} {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] {g : X.functionField} (hg : g ≠ 0)
    (heq : ∀ p : PrimeDivisor X, p.1 ∈ U → D p = X.ord g p.1) :
    Γ(X,U) ≃ₗ[Γ(X,U)] divisorFunctionSubmodule D U :=
  LinearEquiv.ofBijective (cartierSheafChartMap hU hg heq)
    (cartierSheafChartMap_bijective hU hg heq)

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace

namespace NumericalDimensionOne
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]

def IsDivisorGerm (D : WeilDivisor X) (x : X) (f : X.functionField) : Prop :=
  ∃ U : X.Opens, x ∈ U ∧ IsDivisorSectionOn D U f

lemma isDivisorGerm_add {D : WeilDivisor X} {x : X} {f g : X.functionField}
    (hf : IsDivisorGerm D x f) (hg : IsDivisorGerm D x g) :
    IsDivisorGerm D x (f+g) := by
  obtain ⟨U,hxU,hf⟩ := hf
  obtain ⟨V,hxV,hg⟩ := hg
  exact ⟨U ⊓ V,⟨hxU,hxV⟩,divisorSectionOn_add
    (divisorSectionOn_res inf_le_left hf) (divisorSectionOn_res inf_le_right hg)⟩

lemma isDivisorGerm_smul {D : WeilDivisor X} {x : X}
    (a : X.presheaf.stalk x) {f : X.functionField} (hf : IsDivisorGerm D x f) :
    IsDivisorGerm D x (a • f) := by
  obtain ⟨U,hxU,hf⟩ := hf
  obtain ⟨V,hxV,b,rfl⟩ := X.presheaf.exists_germ_eq a
  let : Nonempty V := ⟨⟨x,hxV⟩⟩
  let : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x,hxU,hxV⟩⟩
  refine ⟨U ⊓ V,⟨hxU,hxV⟩,?_⟩
  change IsDivisorSectionOn D (U ⊓ V)
    (algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ V x hxV b) * f)
  rw [X.algebraMap_germ_eq_germToFunctionField hxV b]
  rw [← germToFunctionField_restrict (homOfLE (inf_le_right : U ⊓ V ≤ V)) b]
  exact divisorSectionOn_smul _ (divisorSectionOn_res inf_le_left hf)

noncomputable def divisorRationalStalk (D : WeilDivisor X) (x : X) :
    Submodule (X.presheaf.stalk x) X.functionField where
  carrier := {f | IsDivisorGerm D x f}
  zero_mem' := ⟨⊤,trivial,Or.inl rfl⟩
  add_mem' := isDivisorGerm_add
  smul_mem' := isDivisorGerm_smul
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace

namespace NumericalDimensionOne
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]

theorem cartier_divisorGerm_iff {D : WeilDivisor X} {U : X.Opens}
    (_hU : IsAffineOpen U) {x : X} (hx : x ∈ U) {g : X.functionField} (hg : g ≠ 0)
    (heq : ∀ p : PrimeDivisor X, p.1 ∈ U → D p = X.ord g p.1)
    (f : X.functionField) :
    IsDivisorGerm D x f ↔ ∃ a : X.presheaf.stalk x,
      algebraMap (X.presheaf.stalk x) X.functionField a = f*g := by
  constructor
  · rintro ⟨V,hxV,hf⟩
    obtain ⟨W,hW,hxW,hWU⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ U ⊓ V from ⟨hx,hxV⟩)
    let : Nonempty W := ⟨⟨x,hxW⟩⟩
    obtain ⟨a,ha⟩ := (cartier_local_section_iff hW hg
      (fun p hp => heq p (hWU hp).1) f).mp
      (divisorSectionOn_res (le_trans hWU inf_le_right) hf)
    exact ⟨X.presheaf.germ W x hxW a,by
      rw [X.algebraMap_germ_eq_germToFunctionField hxW a,ha]⟩
  · rintro ⟨a,ha⟩
    obtain ⟨V,hxV,b,rfl⟩ := X.presheaf.exists_germ_eq a
    let : Nonempty V := ⟨⟨x,hxV⟩⟩
    rw [X.algebraMap_germ_eq_germToFunctionField hxV b] at ha
    obtain ⟨W,hW,hxW,hWU⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ U ⊓ V from ⟨hx,hxV⟩)
    let : Nonempty W := ⟨⟨x,hxW⟩⟩
    refine ⟨W,hxW,(cartier_local_section_iff hW hg
      (fun p hp => heq p (hWU hp).1) f).mpr ?_⟩
    exact ⟨X.presheaf.map (homOfLE (show W ≤ V from fun _ hp => (hWU hp).2)).op b,by
      rw [germToFunctionField_restrict,ha]⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace

namespace NumericalDimensionOne
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
noncomputable def divisorStalkChartMap {D : WeilDivisor X} {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) {g : X.functionField} (hg : g ≠ 0)
    (heq : ∀ p : PrimeDivisor X, p.1 ∈ U → D p = X.ord g p.1) :
    X.presheaf.stalk x →ₗ[X.presheaf.stalk x] divisorRationalStalk D x where
  toFun a := ⟨algebraMap (X.presheaf.stalk x) X.functionField a / g,
    (cartier_divisorGerm_iff hU hx hg heq _).mpr ⟨a,(div_mul_cancel₀ _ hg).symm⟩⟩
  map_add' := by
    intro a b
    apply Subtype.ext
    change algebraMap (X.presheaf.stalk x) X.functionField (a+b) / g =
      algebraMap (X.presheaf.stalk x) X.functionField a / g +
        algebraMap (X.presheaf.stalk x) X.functionField b / g
    rw [map_add,add_div]
  map_smul' := by
    intro a b
    apply Subtype.ext
    change algebraMap (X.presheaf.stalk x) X.functionField (a*b) / g =
      algebraMap (X.presheaf.stalk x) X.functionField a *
        (algebraMap (X.presheaf.stalk x) X.functionField b / g)
    rw [map_mul,mul_div_assoc]

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace

namespace NumericalDimensionOne
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
theorem divisorStalkChartMap_bijective {D : WeilDivisor X} {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) {g : X.functionField} (hg : g ≠ 0)
    (heq : ∀ p : PrimeDivisor X, p.1 ∈ U → D p = X.ord g p.1) :
    Function.Bijective (divisorStalkChartMap hU hx hg heq) := by
  constructor
  · intro a b hab
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    exact (div_left_inj' hg).mp (congrArg Subtype.val hab)
  · intro f
    obtain ⟨a,ha⟩ := (cartier_divisorGerm_iff hU hx hg heq f.1).mp f.2
    refine ⟨a,Subtype.ext ?_⟩
    change algebraMap (X.presheaf.stalk x) X.functionField a / g = f.1
    rw [ha,mul_div_cancel_right₀ _ hg]

noncomputable def divisorStalkChartEquiv {D : WeilDivisor X} {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) {g : X.functionField} (hg : g ≠ 0)
    (heq : ∀ p : PrimeDivisor X, p.1 ∈ U → D p = X.ord g p.1) :
    X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] divisorRationalStalk D x :=
  LinearEquiv.ofBijective (divisorStalkChartMap hU hx hg heq)
    (divisorStalkChartMap_bijective hU hx hg heq)

theorem cartier_divisorRationalStalk_flat {D : WeilDivisor X}
    (hD : IsCartierDivisor D) (x : X) :
    Module.Free (X.presheaf.stalk x) (divisorRationalStalk D x) ∧
      Module.Flat (X.presheaf.stalk x) (divisorRationalStalk D x) := by
  obtain ⟨U,hU,hx,g,hg,heq⟩ := hD x
  let e := divisorStalkChartEquiv hU hx hg heq
  let : Module.Free (X.presheaf.stalk x) (divisorRationalStalk D x) :=
    Module.Free.of_equiv e
  exact ⟨inferInstance,inferInstance⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace
open CategoryTheory.Limits

namespace NumericalDimensionOne
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]

noncomputable def divisorSectionGermValue (D : WeilDivisor X) {U : X.Opens}
    {x : X} (hx : x ∈ U) :
    divisorFunctionGroup D U →+ divisorRationalStalk D x where
  toFun f := ⟨f.1 ⟨x,hx⟩,by
    let : Nonempty U := ⟨⟨x,hx⟩⟩
    obtain ⟨a,ha,hs⟩ := (divisorFunctionLocal_iff f.1).mp f.2
    exact ⟨U,hx,by rw [ha]; exact hs⟩⟩
  map_zero' := rfl
  map_add' := fun _ _ => rfl

noncomputable def divisorSheafStalkMap (D : WeilDivisor X) (x : X) :
    (divisorFunctionPresheaf D).stalk x ⟶ AddCommGrpCat.of (divisorRationalStalk D x) :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ divisorFunctionPresheaf D)
    { pt := AddCommGrpCat.of (divisorRationalStalk D x)
      ι := { app := fun U => AddCommGrpCat.ofHom (divisorSectionGermValue D U.unop.2)
             naturality := by
               intro U V i
               ext f
               rfl } }

lemma divisorSheafStalkMap_germ (D : WeilDivisor X) {U : X.Opens}
    {x : X} (hx : x ∈ U) (f : divisorFunctionGroup D U) :
    divisorSheafStalkMap D x ((divisorFunctionPresheaf D).germ U x hx f) =
      divisorSectionGermValue D hx f := by
  change (colimit.ι ((OpenNhds.inclusion x).op ⋙ divisorFunctionPresheaf D)
    (op (⟨U,hx⟩ : OpenNhds x)) ≫ _) f = _
  dsimp only [divisorSheafStalkMap]
  rw [colimit.ι_desc]
  rfl
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace
open CategoryTheory.Limits

namespace NumericalDimensionOne
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]

theorem divisorSheafStalkMap_bijective (D : WeilDivisor X) (x : X) :
    Function.Bijective (divisorSheafStalkMap D x) := by
  constructor
  · intro a b hab
    obtain ⟨U,hxU,f,rfl⟩ := (divisorFunctionPresheaf D).exists_germ_eq a
    obtain ⟨V,hxV,g,rfl⟩ := (divisorFunctionPresheaf D).exists_germ_eq b
    change divisorFunctionGroup D U at f
    change divisorFunctionGroup D V at g
    rw [divisorSheafStalkMap_germ D hxU f,divisorSheafStalkMap_germ D hxV g] at hab
    have hfg : f.1 ⟨x,hxU⟩ = g.1 ⟨x,hxV⟩ := congrArg Subtype.val hab
    let : Nonempty U := ⟨⟨x,hxU⟩⟩
    let : Nonempty V := ⟨⟨x,hxV⟩⟩
    obtain ⟨c,hc,hcs⟩ := (divisorFunctionLocal_iff f.1).mp f.2
    obtain ⟨d,hd,hds⟩ := (divisorFunctionLocal_iff g.1).mp g.2
    have hcd : c = d := by simpa only [hc,hd] using hfg
    have hr : (divisorFunctionPresheaf D).map
        (homOfLE (inf_le_left : U ⊓ V ≤ U)).op f =
      (divisorFunctionPresheaf D).map
        (homOfLE (inf_le_right : U ⊓ V ≤ V)).op g := by
      apply Subtype.ext
      funext y
      change f.1 ⟨y.1,y.2.1⟩ = g.1 ⟨y.1,y.2.2⟩
      rw [hc,hd,hcd]
    have hh := congrArg ((divisorFunctionPresheaf D).germ (U ⊓ V) x ⟨hxU,hxV⟩) hr
    exact ((divisorFunctionPresheaf D).germ_res_apply
      (homOfLE (inf_le_left : U ⊓ V ≤ U)) x ⟨hxU,hxV⟩ f).symm.trans
      (hh.trans ((divisorFunctionPresheaf D).germ_res_apply
        (homOfLE (inf_le_right : U ⊓ V ≤ V)) x ⟨hxU,hxV⟩ g))
  · intro f
    obtain ⟨U,hx,hs⟩ := f.2
    let : Nonempty U := ⟨⟨x,hx⟩⟩
    let s : divisorFunctionGroup D U := ⟨fun _ => f.1,
      (divisorFunctionLocal_iff _).mpr ⟨f.1,fun _ => rfl,hs⟩⟩
    refine ⟨(divisorFunctionPresheaf D).germ U x hx s,?_⟩
    exact (divisorSheafStalkMap_germ D hx s).trans (Subtype.ext rfl)

noncomputable def divisorSheafStalkEquiv (D : WeilDivisor X) (x : X) :
    (divisorFunctionPresheaf D).stalk x ≃+ divisorRationalStalk D x :=
  AddEquiv.ofBijective (divisorSheafStalkMap D x).hom (divisorSheafStalkMap_bijective D x)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace
open CategoryTheory.Limits

namespace NumericalDimensionOne

noncomputable def twistedMultiplierModuleSheaf {n : ℕ} (Y : CanonicalModel n)
    [StalkwiseNormal Y.scheme] (D : WeilDivisor Y.scheme)
    (Δ : QWeilDivisor Y.scheme) : SheafOfModules Y.scheme.ringCatSheaf :=
  (PresheafOfModules.sheafification (𝟙 Y.scheme.ringCatSheaf.obj)).obj
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (divisorModulePresheaf D)
      (multiplierModulePresheaf Y Δ))

noncomputable def twistedMultiplierSectionsEquivOfKlt {n : ℕ} {Y : CanonicalModel n}
    [StalkwiseNormal Y.scheme] (D : WeilDivisor Y.scheme)
    {Δ : QWeilDivisor Y.scheme} {U : Y.scheme.Opens}
    (h : IsKltBoundaryOn Y U Δ) {V : Y.scheme.Opens} (hVU : V ≤ U) :
    TensorProduct Γ(Y.scheme,V) (divisorFunctionSubmodule D V)
      (valuativeMultiplierIdeal Y Δ V) ≃ₗ[Γ(Y.scheme,V)] divisorFunctionSubmodule D V :=
  (TensorProduct.congr (LinearEquiv.refl _ _) (multiplierModuleEquivOfKlt h hVU)).trans
    (TensorProduct.rid _ _)
end NumericalDimensionOne

end OAI
