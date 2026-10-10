import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequentialRepresentationColimit

namespace OAI

/-! # Normalized free generators in a sequential coefficient colimit -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]
namespace SequentialRepresentationDiagram.ColimitCocone
variable {D : SequentialRepresentationDiagram G} {A : Rep.{0} ℤ G}
  (c : D.ColimitCocone A)

abbrev freeDiagram (_c : D.ColimitCocone A) : SequentialRepresentationDiagram G := D.mapFunctor normalizedFreeFunctor

def freeLimitGenerator (i : ℕ) (x : D.obj i) : c.freeDiagram.ModuleLimit :=
  Module.DirectLimit.of ℤ[G] ℕ _ c.freeDiagram.moduleMap i
    ((normalizedFreeRepresentation (D.obj i)).ρ.asModuleEquiv.symm
      (normalizedFreeGenerator (D.obj i) x))

theorem freeLimitGenerator_transport (i j : ℕ) (hij : i ≤ j) (x : D.obj i) :
    c.freeLimitGenerator i x = c.freeLimitGenerator j ((D.map i j hij).hom x) := by
  unfold freeLimitGenerator
  have he := Module.DirectLimit.of_f (R := ℤ[G]) (ι := ℕ)
    (G := fun k => (c.freeDiagram.obj k).ρ.asModule) (f := c.freeDiagram.moduleMap)
    (hij := hij) (x := (normalizedFreeRepresentation (D.obj i)).ρ.asModuleEquiv.symm
      (normalizedFreeGenerator (D.obj i) x))
  have hg : c.freeDiagram.moduleMap i j hij
      ((normalizedFreeRepresentation (D.obj i)).ρ.asModuleEquiv.symm
        (normalizedFreeGenerator (D.obj i) x)) =
      (normalizedFreeRepresentation (D.obj j)).ρ.asModuleEquiv.symm
        (normalizedFreeGenerator (D.obj j) ((D.map i j hij).hom x)) := by
    apply (normalizedFreeRepresentation (D.obj j)).ρ.asModuleEquiv.injective
    exact normalizedFreeMap_generator (D.map i j hij) x
  rw [hg] at he
  exact he.symm

@[simp]
theorem freeLimitGenerator_zero (i : ℕ) : c.freeLimitGenerator i 0 = 0 := by
  simp [freeLimitGenerator]
  exact (Module.DirectLimit.of ℤ[G] ℕ _ c.freeDiagram.moduleMap i).map_zero

theorem freeLimitGenerator_eq (i j : ℕ) (x : D.obj i) (y : D.obj j)
    (hxy : (c.ι i).hom x = (c.ι j).hom y) :
    c.freeLimitGenerator i x = c.freeLimitGenerator j y := by
  let k := max i j
  let xk := (D.map i k (le_max_left i j)).hom x
  let yk := (D.map j k (le_max_right i j)).hom y
  have he : (c.ι k).hom (xk - yk) = 0 := by
    rw [map_sub]
    have hx := ConcreteCategory.congr_hom (c.comm i k (le_max_left i j)) x
    have hy := ConcreteCategory.congr_hom (c.comm j k (le_max_right i j)) y
    change (c.ι k).hom xk = (c.ι i).hom x at hx
    change (c.ι k).hom yk = (c.ι j).hom y at hy
    rw [hx, hy, hxy, sub_self]
  obtain ⟨l, hkl, hl⟩ := c.zero_exact k (xk - yk) he
  have hl' : (D.map k l hkl).hom xk = (D.map k l hkl).hom yk := by
    exact sub_eq_zero.mp (by simpa only [map_sub] using hl)
  rw [c.freeLimitGenerator_transport i k (le_max_left i j),
    c.freeLimitGenerator_transport j k (le_max_right i j)]
  change c.freeLimitGenerator k xk = c.freeLimitGenerator k yk
  rw [c.freeLimitGenerator_transport k l hkl, c.freeLimitGenerator_transport k l hkl, hl']

theorem freeLimitGenerator_eq_zero (i : ℕ) (x : D.obj i) (hx : (c.ι i).hom x = 0) :
    c.freeLimitGenerator i x = 0 := by
  have he := c.freeLimitGenerator_eq i i x 0 (by simpa using hx)
  simpa using he

def normalizedFreeModuleBasis (B : Rep.{0} ℤ G) :
    Module.Basis {b : B // b ≠ 0} ℤ[G] (normalizedFreeRepresentation B).ρ.asModule :=
  Representation.freeAsModuleBasis ℤ G {b : B // b ≠ 0}

def freeModuleGenerator (B : Rep.{0} ℤ G) (x : B) : (normalizedFreeRepresentation B).ρ.asModule :=
  (normalizedFreeRepresentation B).ρ.asModuleEquiv.symm (normalizedFreeGenerator B x)

@[simp]
theorem freeModuleGenerator_zero (B : Rep.{0} ℤ G) : freeModuleGenerator B 0 = 0 := by
  simp [freeModuleGenerator]

theorem freeModuleGenerator_basis (B : Rep.{0} ℤ G) (x : B) (hx : x ≠ 0) :
    freeModuleGenerator B x = normalizedFreeModuleBasis B ⟨x, hx⟩ := by
  unfold freeModuleGenerator
  rw [normalizedFreeGenerator_of_ne_zero B x hx]
  rfl

def freeModuleCocone (i : ℕ) : (c.freeDiagram.obj i).ρ.asModule →ₗ[ℤ[G]]
    (normalizedFreeRepresentation A).ρ.asModule :=
  representationModuleHomEquiv ℤ G _ _ (normalizedFreeMap (c.ι i))

def freeModuleLift : c.freeDiagram.ModuleLimit →ₗ[ℤ[G]]
    (normalizedFreeRepresentation A).ρ.asModule :=
  Module.DirectLimit.lift ℤ[G] ℕ _ _ c.freeModuleCocone (by
    intro i j h x
    change representationModuleHomEquiv ℤ G _ _
      (normalizedFreeMap (D.map i j h) ≫ normalizedFreeMap (c.ι j)) x =
        representationModuleHomEquiv ℤ G _ _ (normalizedFreeMap (c.ι i)) x
    rw [← normalizedFreeMap_comp, c.comm])

theorem freeModuleLift_generator (i : ℕ) (x : D.obj i) :
    c.freeModuleLift (c.freeLimitGenerator i x) = freeModuleGenerator A ((c.ι i).hom x) := by
  unfold freeModuleLift freeLimitGenerator
  refine (Module.DirectLimit.lift_of c.freeModuleCocone _ _).trans ?_
  apply (normalizedFreeRepresentation A).ρ.asModuleEquiv.injective
  exact normalizedFreeMap_generator (c.ι i) x

def freeChosenLift (a : {a : A // a ≠ 0}) : c.freeDiagram.ModuleLimit :=
  c.freeLimitGenerator (Classical.choose (c.surj a.1))
    (Classical.choose (Classical.choose_spec (c.surj a.1)))

def freeModuleInverse : (normalizedFreeRepresentation A).ρ.asModule →ₗ[ℤ[G]]
    c.freeDiagram.ModuleLimit :=
  (normalizedFreeModuleBasis A).constr ℤ c.freeChosenLift

@[simp]
theorem freeModuleInverse_basis (a : {a : A // a ≠ 0}) :
    c.freeModuleInverse (normalizedFreeModuleBasis A a) = c.freeChosenLift a :=
  (normalizedFreeModuleBasis A).constr_basis ℤ c.freeChosenLift a

@[simp]
theorem freeLimitGenerator_basis (i : ℕ) (a : {a : D.obj i // a ≠ 0}) :
    Module.DirectLimit.of ℤ[G] ℕ _ c.freeDiagram.moduleMap i
      (normalizedFreeModuleBasis (D.obj i) a) = c.freeLimitGenerator i a.1 := by
  change Module.DirectLimit.of ℤ[G] ℕ _ c.freeDiagram.moduleMap i
      (normalizedFreeModuleBasis (D.obj i) a) =
    Module.DirectLimit.of ℤ[G] ℕ _ c.freeDiagram.moduleMap i (freeModuleGenerator (D.obj i) a.1)
  rw [freeModuleGenerator_basis (D.obj i) a.1 a.2]

theorem freeModuleLift_chosen (a : {a : A // a ≠ 0}) :
    c.freeModuleLift (c.freeChosenLift a) = freeModuleGenerator A a.1 := by
  unfold freeChosenLift
  rw [c.freeModuleLift_generator, Classical.choose_spec (Classical.choose_spec (c.surj a.1))]

theorem freeModuleInverse_generator (i : ℕ) (x : D.obj i) :
    c.freeModuleInverse (freeModuleGenerator A ((c.ι i).hom x)) = c.freeLimitGenerator i x := by
  classical
  by_cases hx : (c.ι i).hom x = 0
  · rw [hx, freeModuleGenerator_zero, map_zero, c.freeLimitGenerator_eq_zero i x hx]
  · rw [freeModuleGenerator_basis A _ hx]
    rw [c.freeModuleInverse_basis]
    unfold freeChosenLift
    apply c.freeLimitGenerator_eq
    exact Classical.choose_spec (Classical.choose_spec (c.surj ((c.ι i).hom x)))

theorem freeModuleLift_bijective : Function.Bijective c.freeModuleLift := by
  have hleft : c.freeModuleInverse.comp c.freeModuleLift = LinearMap.id := by
    apply Module.DirectLimit.hom_ext
    intro i
    apply (normalizedFreeModuleBasis (D.obj i)).ext
    intro a
    have hb := c.freeLimitGenerator_basis i a
    have hq := c.freeModuleLift_generator i a.1
    have hi := c.freeModuleInverse_generator i a.1
    exact (congrArg (fun z => c.freeModuleInverse (c.freeModuleLift z)) hb).trans
      ((congrArg c.freeModuleInverse hq).trans (hi.trans hb.symm))
  have hright : c.freeModuleLift.comp c.freeModuleInverse = LinearMap.id := by
    apply (normalizedFreeModuleBasis A).ext
    intro a
    simp only [LinearMap.comp_apply, LinearMap.id_apply, c.freeModuleInverse_basis,
      c.freeModuleLift_chosen]
    exact freeModuleGenerator_basis A a.1 a.2
  have hl : Function.LeftInverse c.freeModuleInverse c.freeModuleLift := fun x =>
    LinearMap.congr_fun hleft x
  have hr : Function.RightInverse c.freeModuleInverse c.freeModuleLift := fun x =>
    LinearMap.congr_fun hright x
  exact ⟨hl.injective, hr.surjective⟩

@[simp]
theorem freeModuleLift_of (i : ℕ) (x : (c.freeDiagram.obj i).ρ.asModule) :
    c.freeModuleLift (Module.DirectLimit.of ℤ[G] ℕ _ c.freeDiagram.moduleMap i x) =
      c.freeModuleCocone i x := Module.DirectLimit.lift_of _ _ _

def normalizedFree : (D.mapFunctor normalizedFreeFunctor).ColimitCocone
    (normalizedFreeRepresentation A) where
  ι i := normalizedFreeMap (c.ι i)
  comm i j h := by
    change normalizedFreeMap (D.map i j h) ≫ normalizedFreeMap (c.ι j) =
      normalizedFreeMap (c.ι i)
    rw [← normalizedFreeMap_comp, c.comm]
  surj x := by
    obtain ⟨z, hz⟩ := c.freeModuleLift_bijective.2
      ((normalizedFreeRepresentation A).ρ.asModuleEquiv.symm x)
    obtain ⟨i, y, rfl⟩ := Module.DirectLimit.exists_of z
    refine ⟨i, (normalizedFreeRepresentation (D.obj i)).ρ.asModuleEquiv y, ?_⟩
    rw [c.freeModuleLift_of] at hz
    have he := congrArg (normalizedFreeRepresentation A).ρ.asModuleEquiv hz
    exact he
  zero_exact i x hx := by
    let y := (normalizedFreeRepresentation (D.obj i)).ρ.asModuleEquiv.symm x
    have hz : Module.DirectLimit.of ℤ[G] ℕ _ c.freeDiagram.moduleMap i y = 0 := by
      apply c.freeModuleLift_bijective.1
      calc
        _ = c.freeModuleCocone i y := c.freeModuleLift_of i y
        _ = 0 := by
          apply (normalizedFreeRepresentation A).ρ.asModuleEquiv.injective
          exact hx
        _ = c.freeModuleLift 0 := (map_zero c.freeModuleLift).symm
    obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact hz
    refine ⟨j, hij, ?_⟩
    have he := congrArg (normalizedFreeRepresentation (D.obj j)).ρ.asModuleEquiv hj
    exact he

end SequentialRepresentationDiagram.ColimitCocone
end PolycyclicRecognition

end

end OAI
