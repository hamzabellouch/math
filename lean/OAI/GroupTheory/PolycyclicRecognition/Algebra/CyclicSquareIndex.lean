import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegerSemidirectLattice
import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace OAI

/-! # Passing to the square of a cyclic automorphism at finite index -/

noncomputable section
namespace PolycyclicRecognition
variable {H : Type} [Group H]

def integerDoubleHom : Multiplicative ℤ →* Multiplicative ℤ where
  toFun n := Multiplicative.ofAdd (2 * n.toAdd)
  map_one' := by apply Multiplicative.ext; simp
  map_mul' n m := by apply Multiplicative.ext; exact mul_add 2 n.toAdd m.toAdd

theorem integerDoubleHom_injective : Function.Injective integerDoubleHom := by
  intro n m h
  apply Multiplicative.ext
  have he := congrArg Multiplicative.toAdd h
  change 2 * n.toAdd = 2 * m.toAdd at he
  omega

theorem integerDoubleHom_range_finiteIndex : integerDoubleHom.range.FiniteIndex := by
  let g := Multiplicative.ofAdd (1 : ℤ)
  have hg : Subgroup.zpowers g = ⊤ := by
    apply top_unique
    intro z _
    refine ⟨z.toAdd, ?_⟩
    apply Multiplicative.ext
    simp [g]
  have hr : integerDoubleHom.range = Subgroup.zpowers (g ^ (2 : ℤ)) := by
    rw [MonoidHom.range_eq_map, ← hg, MonoidHom.map_zpowers]
    congr 1
  refine ⟨?_⟩
  rw [hr, Subgroup.index_zpowers_zpow hg]
  exact ne_of_gt (Int.gcd_pos_of_ne_zero_left (orderOf g) (by norm_num : (2 : ℤ) ≠ 0))

def cyclicSquareMap (a : MulAut H) :
    (H ⋊[integerPowerAction (a ^ 2)] Multiplicative ℤ) →*
      (H ⋊[integerPowerAction a] Multiplicative ℤ) :=
  SemidirectProduct.map (MonoidHom.id H) integerDoubleHom (by
    intro n
    ext x
    change ((a ^ (2 : ℤ)) ^ n.toAdd) x = (a ^ (2 * n.toAdd)) x
    rw [← zpow_mul])

theorem cyclicSquareMap_injective (a : MulAut H) : Function.Injective (cyclicSquareMap a) := by
  intro x y h
  apply SemidirectProduct.ext
  · exact congrArg (fun z : H ⋊[integerPowerAction a] Multiplicative ℤ => z.left) h
  · exact integerDoubleHom_injective
      (congrArg (fun z : H ⋊[integerPowerAction a] Multiplicative ℤ => z.right) h)

theorem cyclicSquareMap_range (a : MulAut H) :
    (cyclicSquareMap a).range = integerDoubleHom.range.comap SemidirectProduct.rightHom := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.right, rfl⟩
  · rintro ⟨n, hn⟩
    refine ⟨⟨g.left, n⟩, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact hn

theorem cyclicSquareMap_range_finiteIndex (a : MulAut H) : (cyclicSquareMap a).range.FiniteIndex := by
  let := integerDoubleHom_range_finiteIndex
  rw [cyclicSquareMap_range]
  infer_instance

def cyclicSquareRangeEquiv (a : MulAut H) :
    (H ⋊[integerPowerAction (a ^ 2)] Multiplicative ℤ) ≃* (cyclicSquareMap a).range :=
  MulEquiv.ofBijective (cyclicSquareMap a).rangeRestrict ⟨by
    intro x y h
    exact cyclicSquareMap_injective a (congrArg Subtype.val h), by
    rintro ⟨g, x, rfl⟩
    exact ⟨x, rfl⟩⟩

end PolycyclicRecognition

end

end OAI
