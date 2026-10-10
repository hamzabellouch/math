import OAI.GroupTheory.PolycyclicRecognition.Algebra.NoetherianComponents
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.GroupTheory.Index

namespace OAI

/-! # Closures and components using separately continuous multiplication

Polynomial matrix groups have this weaker topological structure. It is
enough to form subgroup closures and the normal identity component. In a
Noetherian space the latter has finite index.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type*} [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G] [ContinuousInv G]

def separateClosure (S : Subgroup G) : Subgroup G where
  carrier := closure (S : Set G)
  one_mem' := subset_closure S.one_mem
  mul_mem' hg hh := map_mem_closure₂'
    (fun g => continuous_const_mul g) (fun h => continuous_mul_const h) hg hh
    (fun _ hg _ hh => S.mul_mem hg hh)
  inv_mem' hg := map_mem_closure continuous_inv hg (fun _ ha => S.inv_mem ha)

theorem separateClosure_closed (S : Subgroup G) : IsClosed (separateClosure S : Set G) :=
  isClosed_closure

theorem separateClosure_mono {S T : Subgroup G} (h : S ≤ T) :
    separateClosure S ≤ separateClosure T := closure_mono h

theorem separateClosure_normal (S : Subgroup G) [S.Normal] : (separateClosure S).Normal where
  conj_mem a ha g := by
    change g * a * g⁻¹ ∈ closure (S : Set G)
    exact map_mem_closure (f := fun x : G => g * x * g⁻¹)
      ((continuous_const_mul g).mul_const g⁻¹) ha
      (fun _ hx => Subgroup.Normal.conj_mem inferInstance _ hx g)

def separateIdentityComponent (G : Type*) [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] [ContinuousInv G] : Subgroup G where
  carrier := connectedComponent (1 : G)
  one_mem' := mem_connectedComponent
  mul_mem' := by
    intro g h hg hh
    have hm := (continuous_const_mul g).mapsTo_connectedComponent 1 hh
    rw [connectedComponent_eq hg]
    simpa only [mul_one] using hm
  inv_mem' := by
    intro g hg
    have hm := continuous_inv.mapsTo_connectedComponent (1 : G) hg
    simpa only [inv_one] using hm

instance separateIdentityComponent_normal : (separateIdentityComponent G).Normal where
  conj_mem a ha g := by
    change g * a * g⁻¹ ∈ connectedComponent (1 : G)
    have hc : Continuous (fun x : G => g * x * g⁻¹) :=
      (continuous_const_mul g).mul_const g⁻¹
    have hm := hc.mapsTo_connectedComponent 1 ha
    simpa only [mul_one, mul_inv_cancel] using hm

theorem separateIdentityComponent_closed : IsClosed (separateIdentityComponent G : Set G) :=
  isClosed_connectedComponent

theorem separateIdentityComponent_preconnected :
    IsPreconnected (separateIdentityComponent G : Set G) := isPreconnected_connectedComponent

theorem separateIdentityComponent_finiteIndex [TopologicalSpace.NoetherianSpace G] :
    (separateIdentityComponent G).FiniteIndex := by
  let C := separateIdentityComponent G
  let : Finite (ConnectedComponents G) := finite_connectedComponents_of_noetherian
  let q : ConnectedComponents G → G ⧸ C := Quotient.lift
    (fun g => (g : G ⧸ C)) (by
      intro x y hxy
      apply QuotientGroup.eq_iff_div_mem.mpr
      change x / y ∈ connectedComponent (1 : G)
      have hx : x ∈ connectedComponent y := hxy ▸ mem_connectedComponent
      have hm := (continuous_mul_const y⁻¹).mapsTo_connectedComponent y hx
      simpa only [div_eq_mul_inv, mul_inv_cancel] using hm)
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C z
    exact ⟨ConnectedComponents.mk g, rfl⟩
  let : Finite (G ⧸ C) := Finite.of_surjective q hq
  exact Subgroup.finiteIndex_of_finite_quotient

end PolycyclicRecognition

end

end OAI
