import OAI.GroupTheory.Thompson.Model
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Group.Subgroup.Basic

namespace OAI

/-!
# Actual homeomorphisms of the real unit interval

The wrapper supplies the composition group explicitly. In particular, its
multiplication is function composition in the order `(h * g) x = h (g x)`.
Its carrier is equivalent to the actual interval homeomorphisms, without
quotients or an abstract group action.
-/

namespace ThompsonNonamenability

@[simp] theorem coe_unitIntervalZero : (unitIntervalZero : ℝ) = 0 := rfl
@[simp] theorem coe_unitIntervalOne : (unitIntervalOne : ℝ) = 1 := rfl

namespace IntervalHomeomorph

@[ext] theorem ext {f g : IntervalHomeomorph} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk f =>
    cases g with
    | mk g =>
      congr 1
      exact Homeomorph.ext h

def homeomorphEquiv : IntervalHomeomorph ≃ (UnitInterval ≃ₜ UnitInterval) where
  toFun := toHomeomorph
  invFun := IntervalHomeomorph.mk
  left_inv f := by cases f; rfl
  right_inv _ := rfl

@[simp] theorem homeomorphEquiv_apply (f : IntervalHomeomorph) :
    homeomorphEquiv f = f.toHomeomorph := rfl

instance : Group IntervalHomeomorph where
  one := ⟨Homeomorph.refl UnitInterval⟩
  mul f g := ⟨g.toHomeomorph.trans f.toHomeomorph⟩
  inv f := ⟨f.toHomeomorph.symm⟩
  mul_assoc _ _ _ := ext fun _ => rfl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  inv_mul_cancel f := ext f.toHomeomorph.symm_apply_apply

@[simp] theorem one_apply (x : UnitInterval) : (1 : IntervalHomeomorph) x = x := rfl

@[simp] theorem mul_apply (h g : IntervalHomeomorph) (x : UnitInterval) :
    (h * g) x = h (g x) := rfl

@[simp] theorem inv_apply_apply (f : IntervalHomeomorph) (x : UnitInterval) :
    f⁻¹ (f x) = x := f.toHomeomorph.symm_apply_apply x

@[simp] theorem apply_inv_apply (f : IntervalHomeomorph) (x : UnitInterval) :
    f (f⁻¹ x) = x := f.toHomeomorph.apply_symm_apply x

theorem injective (f : IntervalHomeomorph) : Function.Injective f :=
  f.toHomeomorph.injective

theorem surjective (f : IntervalHomeomorph) : Function.Surjective f :=
  f.toHomeomorph.surjective

theorem continuous (f : IntervalHomeomorph) : Continuous f :=
  f.toHomeomorph.continuous

theorem strictMono_inv {f : IntervalHomeomorph} (hf : StrictMono f) :
    StrictMono (f⁻¹ : IntervalHomeomorph) := by
  intro x y hxy
  by_contra h
  have hyx : f⁻¹ y ≤ f⁻¹ x := le_of_not_gt h
  have h' := hf.monotone hyx
  simp only [apply_inv_apply] at h'
  exact (not_le_of_gt hxy) h'

theorem map_zero {f : IntervalHomeomorph} (hf : StrictMono f) :
    f unitIntervalZero = unitIntervalZero := by
  apply Subtype.ext
  apply le_antisymm
  have hx : unitIntervalZero ≤ f⁻¹ unitIntervalZero :=
    (f⁻¹ unitIntervalZero).property.1
  have h := hf.monotone hx
  simpa only [apply_inv_apply, Subtype.coe_le_coe] using h
  exact (f unitIntervalZero).property.1

theorem map_one {f : IntervalHomeomorph} (hf : StrictMono f) :
    f unitIntervalOne = unitIntervalOne := by
  apply Subtype.ext
  apply le_antisymm
  exact (f unitIntervalOne).property.2
  have hx : f⁻¹ unitIntervalOne ≤ unitIntervalOne :=
    (f⁻¹ unitIntervalOne).property.2
  have h := hf.monotone hx
  simpa only [apply_inv_apply, Subtype.coe_le_coe] using h

def increasingSubgroup : Subgroup IntervalHomeomorph where
  carrier := {f | StrictMono f}
  one_mem' := fun _ _ h => h
  mul_mem' hf hg := hf.comp hg
  inv_mem' hf := strictMono_inv hf

end IntervalHomeomorph

end ThompsonNonamenability

end OAI
