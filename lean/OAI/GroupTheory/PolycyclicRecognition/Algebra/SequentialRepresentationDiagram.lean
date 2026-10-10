import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SequentialResolutionVanishing
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalizedSyzygyFunctor

namespace OAI

/-! # Vanishing sequential systems and normalized syzygies

This packages only the sequential diagrams needed by the complete-cohomology
construction. Vanishing means that each element is killed at a later stage.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable (G : Type) [Group G]

structure SequentialRepresentationDiagram where
  obj : ℕ → Rep.{0} ℤ G
  map : ∀ i j, i ≤ j → (obj i ⟶ obj j)
  map_id : ∀ i, map i i le_rfl = 𝟙 _
  map_comp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
    map i j hij ≫ map j k hjk = map i k (hij.trans hjk)

namespace SequentialRepresentationDiagram
variable {G} (D : SequentialRepresentationDiagram G)

def Vanishes : Prop :=
  ∀ (i : ℕ) (x : D.obj i), ∃ (j : ℕ) (hij : i ≤ j), (D.map i j hij).hom x = 0

abbrev moduleMap (i j : ℕ) (h : i ≤ j) := coefficientModuleTransition D.obj D.map i j h

instance moduleMap_directed : DirectedSystem (fun i => (D.obj i).ρ.asModule)
    (fun i j h => D.moduleMap i j h) where
  map_self := by
    intro i x
    change representationModuleHomEquiv ℤ G (D.obj i) (D.obj i) (D.map i i le_rfl) x = x
    rw [D.map_id]
    rfl
  map_map := by
    intro k j i hij hjk x
    change representationModuleHomEquiv ℤ G (D.obj i) (D.obj k)
      (D.map i j hij ≫ D.map j k hjk) x = D.moduleMap i k (hij.trans hjk) x
    rw [D.map_comp]

abbrev ModuleLimit := Module.DirectLimit (fun i => (D.obj i).ρ.asModule) D.moduleMap

theorem vanishes_iff_limit_subsingleton : D.Vanishes ↔ Subsingleton D.ModuleLimit := by
  constructor
  · intro hD
    apply subsingleton_of_forall_eq (0 : D.ModuleLimit)
    intro z
    obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
    obtain ⟨j, hij, hj⟩ := hD i ((D.obj i).ρ.asModuleEquiv x)
    have he : D.moduleMap i j hij x = 0 := by
      apply (D.obj j).ρ.asModuleEquiv.injective
      exact hj
    have hc := Module.DirectLimit.of_f (R := ℤ[G]) (ι := ℕ)
      (G := fun i => (D.obj i).ρ.asModule) (f := D.moduleMap) (hij := hij) (x := x)
    rw [he, map_zero] at hc
    exact hc.symm
  · intro hD
    let := hD
    intro i x
    have hz : Module.DirectLimit.of ℤ[G] ℕ (fun i => (D.obj i).ρ.asModule) D.moduleMap i
        ((D.obj i).ρ.asModuleEquiv.symm x) = 0 := Subsingleton.elim _ _
    obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact hz
    refine ⟨j, hij, ?_⟩
    have he := congrArg (D.obj j).ρ.asModuleEquiv hj
    exact he

def mapFunctor (F : Rep.{0} ℤ G ⥤ Rep.{0} ℤ G) : SequentialRepresentationDiagram G where
  obj i := F.obj (D.obj i)
  map i j h := F.map (D.map i j h)
  map_id i := by rw [D.map_id, F.map_id]
  map_comp i j k hij hjk := by rw [← F.map_comp, D.map_comp]

theorem vanishes_normalizedFree (hD : D.Vanishes) :
    (D.mapFunctor normalizedFreeFunctor).Vanishes := by
  let E := D.mapFunctor normalizedFreeFunctor
  apply E.vanishes_iff_limit_subsingleton.mpr
  have hof (i : ℕ) : Module.DirectLimit.of ℤ[G] ℕ (fun i => (E.obj i).ρ.asModule)
      E.moduleMap i = 0 := by
    apply (Representation.freeAsModuleBasis ℤ G {a : D.obj i // a ≠ 0}).ext
    intro a
    obtain ⟨j, hij, hj⟩ := hD i a.1
    have hz : E.moduleMap i j hij
        (Representation.freeAsModuleBasis ℤ G {a : D.obj i // a ≠ 0} a) = 0 := by
      apply (E.obj j).ρ.asModuleEquiv.injective
      change (normalizedFreeMap (D.map i j hij)).hom
        (Finsupp.single a (MonoidAlgebra.single 1 1)) = 0
      rw [← normalizedFreeGenerator_of_ne_zero (D.obj i) a.1 a.2,
        normalizedFreeMap_generator, hj, normalizedFreeGenerator_zero]
    have hc := Module.DirectLimit.of_f (R := ℤ[G]) (ι := ℕ)
      (G := fun i => (E.obj i).ρ.asModule) (f := E.moduleMap) (hij := hij)
      (x := Representation.freeAsModuleBasis ℤ G {a : D.obj i // a ≠ 0} a)
    rw [hz, map_zero] at hc
    exact hc.symm
  apply subsingleton_of_forall_eq (0 : E.ModuleLimit)
  intro z
  obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
  rw [hof, LinearMap.zero_apply]

theorem vanishes_normalizedSyzygy (hD : D.Vanishes) :
    (D.mapFunctor normalizedSyzygyFunctor).Vanishes := by
  have hF := D.vanishes_normalizedFree hD
  intro i x
  obtain ⟨j, hij, hj⟩ := hF i ((kernel.ι (normalizedFreeAugmentation (D.obj i))).hom x)
  refine ⟨j, hij, ?_⟩
  apply (Rep.mono_iff_injective (kernel.ι (normalizedFreeAugmentation (D.obj j)))).mp
    inferInstance
  change (kernel.ι (normalizedFreeAugmentation (D.obj j))).hom
    ((normalizedSyzygyMap (D.map i j hij)).hom x) =
      (kernel.ι (normalizedFreeAugmentation (D.obj j))).hom 0
  have he := congrArg (fun u => u.hom x) (normalizedSyzygyMap_ι (D.map i j hij))
  change (kernel.ι (normalizedFreeAugmentation (D.obj j))).hom
    ((normalizedSyzygyMap (D.map i j hij)).hom x) =
      (normalizedFreeMap (D.map i j hij)).hom
        ((kernel.ι (normalizedFreeAugmentation (D.obj i))).hom x) at he
  rw [map_zero]
  exact he.trans hj

theorem vanishes_iteratedNormalizedSyzygy (hD : D.Vanishes) (n : ℕ) :
    (D.mapFunctor (iteratedNormalizedSyzygy n)).Vanishes := by
  induction n with
  | zero => exact hD
  | succ n ih =>
    exact (D.mapFunctor (iteratedNormalizedSyzygy n)).vanishes_normalizedSyzygy ih

end SequentialRepresentationDiagram
end PolycyclicRecognition

end

end OAI
