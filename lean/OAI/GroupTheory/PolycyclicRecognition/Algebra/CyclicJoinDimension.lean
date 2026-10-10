import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicQuotientDimension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntegerQuotientStructure
import OAI.GroupTheory.PolycyclicRecognition.Analysis.GroupDimensionTransport
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Solvable

namespace OAI

/-! # Adjoining a lift of an infinite cyclic quotient

If the lift normalizes a subgroup of the kernel, its join with that subgroup
has precisely the expected kernel. This gives the dimension and solvability
bounds without imposing normality in the whole ambient group.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped Pointwise
variable {G : Type} [Group G] (q : G →* Multiplicative ℤ)
  (t : G) (ht : q t = Multiplicative.ofAdd 1) (A : Subgroup G)
include ht

theorem cyclicJoin_kernel_le (hA : A ≤ q.ker) (hnorm : t ∈ Subgroup.normalizer A) :
    (A ⊔ Subgroup.zpowers t) ⊓ q.ker ≤ A := by
  intro x hx
  have hp : x ∈ (A : Set G) * (Subgroup.zpowers t : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left A (Subgroup.zpowers t)
      (Subgroup.zpowers_le.mpr hnorm)]
    exact hx.1
  obtain ⟨a, ha, b, hb, hab⟩ := hp
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hqx : q x = 1 := hx.2
  have hqa : q a = 1 := hA ha
  have hn : n = 0 := by
    have h := congrArg Multiplicative.toAdd hqx
    rw [← hab, map_mul, hqa, one_mul, map_zpow, ht] at h
    simpa using h
  have he : x = a := by simpa [hn] using hab.symm
  rwa [he]

def cyclicJoinKernelMap (hA : A ≤ q.ker) (hnorm : t ∈ Subgroup.normalizer A) :
    (q.comp (A ⊔ Subgroup.zpowers t).subtype).ker →* A where
  toFun x := ⟨x.val.val, cyclicJoin_kernel_le q t ht A hA hnorm
    ⟨x.val.property, x.property⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem cyclicJoinKernelMap_injective (hA : A ≤ q.ker) (hnorm : t ∈ Subgroup.normalizer A) :
    Function.Injective (cyclicJoinKernelMap q t ht A hA hnorm) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun a : A => (a : G)) h

theorem cyclicJoin_finiteDimension (hA : A ≤ q.ker) (hnorm : t ∈ Subgroup.normalizer A)
    (hcd : HasFiniteIntegralCohomologicalDimension A) :
    HasFiniteIntegralCohomologicalDimension (A ⊔ Subgroup.zpowers t : Subgroup G) := by
  obtain ⟨d, hd⟩ := hcd
  let := hd
  let H := A ⊔ Subgroup.zpowers t
  let p : H →* Multiplicative ℤ := q.comp H.subtype
  let tH : H := ⟨t, (show Subgroup.zpowers t ≤ H from le_sup_right) (Subgroup.mem_zpowers t)⟩
  have htH : p tH = Multiplicative.ofAdd 1 := ht
  let := integerQuotient_isCyclic p tH htH
  let := integerQuotient_infinite p tH htH
  let := cohomologicalDimension_le_of_injective
    (cyclicJoinKernelMap q t ht A hA hnorm)
    (cyclicJoinKernelMap_injective q t ht A hA hnorm) d
  exact ⟨d + 1, cohomologicalDimension_le_of_infiniteCyclicQuotient p.ker d⟩

theorem cyclicJoin_solvable (hA : A ≤ q.ker) (hnorm : t ∈ Subgroup.normalizer A)
    [Group.IsSolvable A] : Group.IsSolvable (A ⊔ Subgroup.zpowers t : Subgroup G) := by
  let H := A ⊔ Subgroup.zpowers t
  let p : H →* Multiplicative ℤ := q.comp H.subtype
  let : Group.IsSolvable p.ker := Group.isSolvable_of_isSolvable_injective
    (cyclicJoinKernelMap_injective q t ht A hA hnorm)
  exact Group.isSolvable_of_ker_le_range p.ker.subtype p
    (by rw [Subgroup.range_subtype])

end PolycyclicRecognition

end

end OAI
