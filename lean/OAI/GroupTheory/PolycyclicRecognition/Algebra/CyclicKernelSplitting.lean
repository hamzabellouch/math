import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegerSemidirectLattice
import Mathlib.GroupTheory.GroupAction.ConjAct

namespace OAI

/-! # Splitting an actual infinite cyclic quotient -/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type*} [Group G]

def cyclicPowerHom (t : G) : Multiplicative ℤ →* G where
  toFun n := t ^ n.toAdd
  map_one' := zpow_zero t
  map_mul' n m := zpow_add t n.toAdd m.toAdd

def cyclicKernelLift (q : G →* Multiplicative ℤ) (t : G) :
    (q.ker ⋊[integerPowerAction (MulAut.conjNormal t)] Multiplicative ℤ) →* G :=
  SemidirectProduct.lift q.ker.subtype (cyclicPowerHom t) (by
    intro n
    ext x
    change (((MulAut.conjNormal t) ^ n.toAdd) x : G) =
      t ^ n.toAdd * (x : G) * (t ^ n.toAdd)⁻¹
    rw [← map_zpow]
    exact MulAut.conjNormal_apply _ _)

theorem cyclicKernelLift_apply (q : G →* Multiplicative ℤ) (t : G)
    (x : q.ker ⋊[integerPowerAction (MulAut.conjNormal t)] Multiplicative ℤ) :
    cyclicKernelLift q t x = (x.left : G) * t ^ x.right.toAdd := rfl

theorem cyclicKernelLift_height (q : G →* Multiplicative ℤ) (t : G)
    (ht : q t = Multiplicative.ofAdd 1)
    (x : q.ker ⋊[integerPowerAction (MulAut.conjNormal t)] Multiplicative ℤ) :
    q (cyclicKernelLift q t x) = x.right := by
  rw [cyclicKernelLift_apply, map_mul, x.left.property, one_mul, map_zpow, ht]
  apply Multiplicative.ext
  change x.right.toAdd • (1 : ℤ) = x.right.toAdd
  simp

def cyclicKernelEquiv (q : G →* Multiplicative ℤ) (t : G)
    (ht : q t = Multiplicative.ofAdd 1) :
    (q.ker ⋊[integerPowerAction (MulAut.conjNormal t)] Multiplicative ℤ) ≃* G :=
  MulEquiv.ofBijective (cyclicKernelLift q t) ⟨by
    intro x y h
    have hr : x.right = y.right := by
      rw [← cyclicKernelLift_height q t ht x, ← cyclicKernelLift_height q t ht y, h]
    apply SemidirectProduct.ext
    · apply Subtype.ext
      rw [cyclicKernelLift_apply, cyclicKernelLift_apply, hr] at h
      exact mul_right_cancel h
    · exact hr,
    by
      intro g
      let n := (q g).toAdd
      have hk : g * t ^ (-n) ∈ q.ker := by
        change q (g * t ^ (-n)) = 1
        rw [map_mul, map_zpow, ht]
        apply Multiplicative.ext
        change (q g).toAdd + (-n) • (1 : ℤ) = 0
        simp [n]
      refine ⟨⟨⟨g * t ^ (-n), hk⟩, q g⟩, ?_⟩
      rw [cyclicKernelLift_apply]
      change (g * t ^ (-n)) * t ^ n = g
      rw [zpow_neg, mul_assoc, inv_mul_cancel, mul_one]⟩

end PolycyclicRecognition

end

end OAI
