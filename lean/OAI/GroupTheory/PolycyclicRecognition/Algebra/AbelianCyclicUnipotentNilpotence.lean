import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntegerQuotientCoordinates
import Mathlib.GroupTheory.Nilpotent

namespace OAI

/-! # Nilpotence of an abelian-by-cyclic group with unipotent action

The kernels of powers of the action difference lie in successive upper
central terms. The integer quotient adds just one final central step.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative commutatorElement
variable {G A : Type} [Group G] [AddCommGroup A]

theorem abelian_cyclic_kernel_mem_upperCentral
    (q : G →* Multiplicative ℤ) [IsMulCommutative q.ker]
    (t : G) (ht : q t = Multiplicative.ofAdd 1)
    (f : q.ker →* Multiplicative A) (hf : Function.Injective f)
    (T : Module.End ℤ A)
    (hT : ∀ x, (f (MulAut.conjNormal t x)).toAdd = T (f x).toAdd)
    (k : ℕ) (x : q.ker) (hx : ((T - 1) ^ k) (f x).toAdd = 0) :
    (x : G) ∈ Subgroup.upperCentralSeries G k := by
  induction k generalizing x with
  | zero =>
    have hfx : f x = 1 := by
      apply Multiplicative.toAdd.injective
      exact hx
    have hxe : x = 1 := hf (hfx.trans f.map_one.symm)
    simpa only [hxe, Subgroup.coe_one] using (Subgroup.upperCentralSeries G 0).one_mem
  | succ k ih =>
    let y := MulAut.conjNormal t x * x⁻¹
    have hfy : (f y).toAdd = (T - 1) (f x).toAdd := by
      change (f (MulAut.conjNormal t x * x⁻¹)).toAdd = T (f x).toAdd - (f x).toAdd
      simp only [map_mul, toAdd_mul, map_inv, toAdd_inv, hT, sub_eq_add_neg]
    have hy : (y : G) ∈ Subgroup.upperCentralSeries G k := by
      apply ih
      rw [hfy, ← Module.End.mul_apply, ← pow_succ]
      exact hx
    let π := QuotientGroup.mk' (Subgroup.upperCentralSeries G k)
    have htx : Commute (π t) (π x) := by
      apply commutatorElement_eq_one_iff_commute.mp
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hy
    have hnx (n : q.ker) : Commute (π n) (π x) := by
      exact (Commute.all n x).map (π.comp q.ker.subtype)
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro g
    apply (QuotientGroup.eq_one_iff _).mp
    change π ⁅(x : G), g⁆ = 1
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_commute.mpr
    rw [← integerQuotientPart_decompose q t ht g, map_mul, map_zpow]
    exact ((hnx (integerQuotientPart q t ht g)).symm).mul_right
      (htx.symm.zpow_right _)

theorem abelian_cyclic_nilpotent_of_unipotent
    (q : G →* Multiplicative ℤ) [IsMulCommutative q.ker]
    (t : G) (ht : q t = Multiplicative.ofAdd 1)
    (f : q.ker →* Multiplicative A) (hf : Function.Injective f)
    (T : Module.End ℤ A)
    (hT : ∀ x, (f (MulAut.conjNormal t x)).toAdd = T (f x).toAdd)
    (hnil : IsNilpotent (T - 1)) : Group.IsNilpotent G := by
  obtain ⟨k, hk⟩ := hnil
  have hN : q.ker ≤ Subgroup.upperCentralSeries G k := by
    intro x hx
    exact abelian_cyclic_kernel_mem_upperCentral q t ht f hf T hT k ⟨x, hx⟩ (by rw [hk]; rfl)
  refine ⟨k + 1, le_antisymm le_top ?_⟩
  intro x _
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  intro g
  apply hN
  change q ⁅x, g⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)

end PolycyclicRecognition

end

end OAI
