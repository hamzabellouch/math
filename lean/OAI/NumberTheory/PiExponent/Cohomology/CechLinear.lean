import OAI.NumberTheory.PiExponent.Cohomology.CechHigher
import OAI.NumberTheory.PiExponent.Cohomology.CurveEuler
import OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections

namespace OAI

namespace PiExponent.GeometrySupport.CechLinear

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.Geometry
open scoped BigOperators AlgebraicGeometry

universe v
variable {X : Scheme.{0}} {J : Type} (U : J → X.Opens)
  {K : Type v} [Field K]

private abbrev schemeFreeOpen (V : X.Opens) : X.Modules := freeOpen X.ringCatSheaf V

@[instance_reducible] private def freeOpenHomAddCommGroup (V : X.Opens) (M : X.Modules) :
    AddCommGroup (freeOpen X.ringCatSheaf V ⟶ M) :=
  inferInstanceAs (AddCommGroup (schemeFreeOpen V ⟶ M))

@[instance_reducible] private def higherCochainAddCommGroup (M : X.Modules) (q : ℕ) :
    AddCommGroup (CechHigher.Cochain X.ringCatSheaf U M q) :=
  inferInstanceAs (AddCommGroup (∀ t : Fin (q + 1) → J,
    schemeFreeOpen (CechHigher.intersection U t) ⟶ M))

attribute [local instance] freeOpenHomAddCommGroup higherCochainAddCommGroup

@[instance_reducible] private def freeOpenHomModule (V : X.Opens) (M : X.Modules) :
    Module Γ(X, ⊤) (freeOpen X.ringCatSheaf V ⟶ M) :=
  sheafHomModule X (schemeFreeOpen V) M

attribute [local instance] freeOpenHomModule

def Cochain (_ : K →+* Γ(X, ⊤)) (M : X.Modules) (q : ℕ) : Type :=
  CechHigher.Cochain X.ringCatSheaf U M q

instance cochainAddCommGroup (ρ : K →+* Γ(X, ⊤)) (M : X.Modules) (q : ℕ) :
    AddCommGroup (Cochain U ρ M q) :=
  inferInstanceAs (AddCommGroup (CechHigher.Cochain X.ringCatSheaf U M q))

instance cochainGlobalModule (ρ : K →+* Γ(X, ⊤)) (M : X.Modules) (q : ℕ) :
    Module Γ(X, ⊤) (Cochain U ρ M q) :=
  letI (t : Fin (q + 1) → J) :
      Module Γ(X, ⊤) (freeOpen X.ringCatSheaf (CechHigher.intersection U t) ⟶ M) :=
    sheafHomModule X _ M
  inferInstanceAs (Module Γ(X, ⊤) (CechHigher.Cochain X.ringCatSheaf U M q))

instance cochainModule (ρ : K →+* Γ(X, ⊤)) (M : X.Modules) (q : ℕ) :
    Module K (Cochain U ρ M q) :=
  Module.compHom _ ρ

variable (ρ : K →+* Γ(X, ⊤)) (M : X.Modules)

def differentialLinear (q : ℕ) : Cochain U ρ M q →ₗ[K] Cochain U ρ M (q + 1) where
  toFun := CechHigher.differential X.ringCatSheaf U M
  map_add' c e := by
    let D : Cochain U ρ M q → Cochain U ρ M (q + 1) :=
      CechHigher.differential X.ringCatSheaf U M
    have hsub (c e : Cochain U ρ M q) : D (c - e) = D c - D e :=
      CechHigher.differential_sub X.ringCatSheaf U M c e
    have hzero : D 0 = 0 := CechHigher.differential_zero X.ringCatSheaf U M
    have hn : D (-e) = -D e := by
      simpa only [zero_sub, hzero] using hsub 0 e
    change D (c + e) = D c + D e
    simpa only [sub_neg_eq_add, hn] using hsub c (-e)
  map_smul' r c := by
    let (A B : SheafOfModules.{0} X.ringCatSheaf) : Module Γ(X, ⊤) (A ⟶ B) := sheafHomModule X A B
    let : Linear Γ(X, ⊤) (SheafOfModules.{0} X.ringCatSheaf) := sheafLinear X
    funext t
    change (∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
      CechOne.restrictHom X.ringCatSheaf (CechHigher.faceLE U t k)
        (ρ r • c (t ∘ k.succAbove))) =
      ρ r • (∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
        CechOne.restrictHom X.ringCatSheaf (CechHigher.faceLE U t k)
          (c (t ∘ k.succAbove)))
    simp only [CechOne.restrictHom, Finset.smul_sum, smul_comm (ρ r)]
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun f : schemeFreeOpen (CechHigher.intersection U t) ⟶ M =>
      (-1 : ℤ) ^ k.val • f)
      (Linear.comp_smul (C := X.Modules) _ _ _
        (freeOpenMap X.ringCatSheaf (homOfLE (CechHigher.faceLE U t k))) (ρ r)
        (c (t ∘ k.succAbove)))

@[simp] theorem differentialLinear_apply (q : ℕ) (c : Cochain U ρ M q) :
    differentialLinear U ρ M q c = CechHigher.differential X.ringCatSheaf U M c := rfl

def cycles (q : ℕ) : Submodule K (Cochain U ρ M q) :=
  (differentialLinear U ρ M q).ker

@[simp] theorem mem_cycles (q : ℕ) (c : Cochain U ρ M q) :
    c ∈ cycles U ρ M q ↔ CechHigher.differential X.ringCatSheaf U M c = 0 := Iff.rfl

def boundaryToCycles (q : ℕ) : Cochain U ρ M q →ₗ[K] cycles U ρ M (q + 1) :=
  (differentialLinear U ρ M q).codRestrict (cycles U ρ M (q + 1))
    (fun c => CechHigher.differential_squared X.ringCatSheaf U M c)

@[simp] theorem boundaryToCycles_val (q : ℕ) (c : Cochain U ρ M q) :
    (boundaryToCycles U ρ M q c).val =
      CechHigher.differential X.ringCatSheaf U M c := rfl

variable {M} {N P : X.Modules}

def mapLinear (g : M ⟶ N) (q : ℕ) : Cochain U ρ M q →ₗ[K] Cochain U ρ N q where
  toFun := CechHigher.map X.ringCatSheaf U M g
  map_add' c e := by
    funext t
    change (c t + e t) ≫ g = c t ≫ g + e t ≫ g
    exact Preadditive.add_comp (C := SheafOfModules.{0} X.ringCatSheaf) _ _ _ (c t) (e t) g
  map_smul' r c := by
    let (A B : SheafOfModules.{0} X.ringCatSheaf) : Module Γ(X, ⊤) (A ⟶ B) := sheafHomModule X A B
    let : Linear Γ(X, ⊤) (SheafOfModules.{0} X.ringCatSheaf) := sheafLinear X
    funext t
    exact Linear.smul_comp (C := SheafOfModules.{0} X.ringCatSheaf) _ _ _ (ρ r) (c t) g

@[simp] theorem mapLinear_apply (g : M ⟶ N) (q : ℕ) (c : Cochain U ρ M q) :
    mapLinear U ρ g q c = CechHigher.map X.ringCatSheaf U M g c := rfl

@[simp] theorem mapLinear_comp (g : M ⟶ N) (h : N ⟶ P) (q : ℕ) :
    mapLinear U ρ (g ≫ h) q = (mapLinear U ρ h q).comp (mapLinear U ρ g q) := by
  apply LinearMap.ext
  intro c
  funext t
  exact (Category.assoc (c t) g h).symm

@[simp] theorem mapLinear_zero (q : ℕ) :
    mapLinear U ρ (0 : M ⟶ N) q = 0 := by
  apply LinearMap.ext
  intro c
  funext t
  exact comp_zero (C := SheafOfModules.{0} X.ringCatSheaf)

theorem mapLinear_differential (g : M ⟶ N) (q : ℕ) (c : Cochain U ρ M q) :
    mapLinear U ρ g (q + 1) (differentialLinear U ρ M q c) =
      differentialLinear U ρ N q (mapLinear U ρ g q c) :=
  CechHigher.map_differential X.ringCatSheaf U M g c

def mapCycles (g : M ⟶ N) (q : ℕ) : cycles U ρ M q →ₗ[K] cycles U ρ N q :=
  ((mapLinear U ρ g q).comp (cycles U ρ M q).subtype).codRestrict
    (cycles U ρ N q) (fun c => by
      change CechHigher.differential X.ringCatSheaf U N
        (CechHigher.map X.ringCatSheaf U M g c.val) = 0
      have hc : CechHigher.differential X.ringCatSheaf U M c.val = 0 := c.property
      exact (CechHigher.map_differential X.ringCatSheaf U M g c.val).symm.trans
        ((congrArg (fun c : Cochain U ρ M (q + 1) => CechHigher.map X.ringCatSheaf U M g c) hc).trans
          (CechHigher.map_zero X.ringCatSheaf U M g)))

@[simp] theorem mapCycles_val (g : M ⟶ N) (q : ℕ) (c : cycles U ρ M q) :
    (mapCycles U ρ g q c).val = mapLinear U ρ g q c.val := rfl

theorem mapCycles_boundary (g : M ⟶ N) (q : ℕ) (c : Cochain U ρ M q) :
    mapCycles U ρ g (q + 1) (boundaryToCycles U ρ M q c) =
      boundaryToCycles U ρ N q (mapLinear U ρ g q c) := by
  apply Subtype.ext
  exact mapLinear_differential U ρ g q c

variable (M)

theorem boundaryToCycles_surjective [hM : Injective M] (q : ℕ) :
    Function.Surjective (boundaryToCycles U ρ M q) := by
  intro c
  obtain ⟨b, hb⟩ := @FreeCechSections.injective_hasPrimitives _ J U X.ringCatSheaf M hM q
    c.val c.property
  exact ⟨b, Subtype.ext hb⟩

def primitive [Injective M] (q : ℕ) :
    cycles U ρ M (q + 1) →ₗ[K] Cochain U ρ M q :=
  Classical.choose ((boundaryToCycles U ρ M q).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (boundaryToCycles_surjective U ρ M q)))

@[simp] theorem boundaryToCycles_primitive [Injective M] (q : ℕ)
    (c : cycles U ρ M (q + 1)) :
    boundaryToCycles U ρ M q (primitive U ρ M q c) = c := by
  exact LinearMap.congr_fun (Classical.choose_spec
    ((boundaryToCycles U ρ M q).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (boundaryToCycles_surjective U ρ M q)))) c

@[simp] theorem primitive_spec [Injective M] (q : ℕ)
    (c : cycles U ρ M (q + 1)) :
    CechHigher.differential X.ringCatSheaf U M (primitive U ρ M q c) = c.val :=
  congrArg Subtype.val (boundaryToCycles_primitive U ρ M q c)

end
end PiExponent.GeometrySupport.CechLinear

end OAI
