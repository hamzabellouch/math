import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteSumCompleteVanishing

namespace OAI

/-! # A countable coefficient sum as a sequential union of finite prefixes -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] DirectSum.instModule
attribute [local instance 2300] Submodule.module
variable {G : Type} [Group G]

def sumPrefixSubmodule (A : ℕ → Rep.{0} ℤ G) (n : ℕ) :
    Submodule ℤ (integralRepresentationSum A) where
  carrier := {x | ∀ i, n ≤ i → x i = 0}
  zero_mem' := by intro i _; rfl
  add_mem' := by
    intro x y hx hy i hi
    change x i + y i = 0
    rw [hx i hi, hy i hi, zero_add]
  smul_mem' := by
    intro r x hx i hi
    have h := congrArg (fun y : integralRepresentationSum A => y i)
      (int_smul_eq_zsmul (integralRepresentationSum A).hV2 r x)
    exact h.trans (by rw [DFinsupp.zsmul_apply, hx i hi, zsmul_zero])

theorem sumPrefixSubmodule_invariant (A : ℕ → Rep.{0} ℤ G) (n : ℕ) (g : G) :
    sumPrefixSubmodule A n ≤ (sumPrefixSubmodule A n).comap ((integralRepresentationSum A).ρ g) := by
  intro x hx i hi
  change (A i).ρ g (x i) = 0
  rw [hx i hi, map_zero]

abbrev sumPrefixRepresentation (A : ℕ → Rep.{0} ℤ G) (n : ℕ) : Rep.{0} ℤ G :=
  Rep.subrepresentation (integralRepresentationSum A) (sumPrefixSubmodule A n)
    (sumPrefixSubmodule_invariant A n)

def sumPrefixInclusion (A : ℕ → Rep.{0} ℤ G) (n : ℕ) :
    sumPrefixRepresentation A n ⟶ integralRepresentationSum A :=
  Rep.subtype _ _ _

def sumPrefixMap (A : ℕ → Rep.{0} ℤ G) (i j : ℕ) (h : i ≤ j) :
    sumPrefixRepresentation A i ⟶ sumPrefixRepresentation A j :=
  Rep.ofHom ⟨Submodule.inclusion (by
    intro x hx k hk
    exact hx k (h.trans hk)), fun _ => rfl⟩

def sumPrefixDiagram (A : ℕ → Rep.{0} ℤ G) : SequentialRepresentationDiagram G where
  obj := sumPrefixRepresentation A
  map := sumPrefixMap A
  map_id _i := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    rfl
  map_comp _i _j _k _hij _hjk := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    rfl

def sumPrefixColimit (A : ℕ → Rep.{0} ℤ G) :
    (sumPrefixDiagram A).ColimitCocone (integralRepresentationSum A) where
  ι := sumPrefixInclusion A
  comm _i _j _h := by
    change sumPrefixMap A _i _j _h ≫ sumPrefixInclusion A _j = sumPrefixInclusion A _i
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    rfl
  surj x := by
    classical
    let n := x.support.sup id + 1
    have hx : x ∈ sumPrefixSubmodule A n := by
      intro i hi
      by_contra hn
      have hm : i ∈ x.support := DFinsupp.mem_support_iff.mpr hn
      have hb : i ≤ x.support.sup id := Finset.le_sup (f := id) hm
      dsimp only [n] at hi
      omega
    exact ⟨n, ⟨x, hx⟩, rfl⟩
  zero_exact i x hx := by
    refine ⟨i, le_rfl, ?_⟩
    apply Subtype.ext
    change x.val = 0
    change x.val = 0 at hx
    exact hx

end PolycyclicRecognition

end

end OAI
