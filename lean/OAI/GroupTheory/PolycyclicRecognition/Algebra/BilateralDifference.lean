import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicCoinvariants
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Finsupp.LSum

namespace OAI

/-! # The difference operator on a bilateral direct sum

This is the algebraic calculation needed in the cyclic-extension duality
argument. It applies to arbitrary coefficient modules.
-/

noncomputable section
namespace PolycyclicRecognition

open Representation

variable (k M : Type*) [CommRing k] [AddCommGroup M] [Module k M]

def bilateralTranslation : Representation k (Multiplicative ℤ) (ℤ →₀ M) where
  toFun z := (Finsupp.domLCongr (Equiv.addLeft z.toAdd)).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro f
    ext i
    change f (-(0 : ℤ) + i) = f i
    simp
  map_mul' x y := by
    apply LinearMap.ext
    intro f
    ext i
    change f (-(x.toAdd + y.toAdd) + i) = f (-y.toAdd + (-x.toAdd + i))
    congr 1
    omega

@[simp] theorem bilateralTranslation_apply (z : Multiplicative ℤ) (f : ℤ →₀ M) (i : ℤ) :
    bilateralTranslation k M z f i = f (-z.toAdd + i) := rfl

@[simp] theorem bilateralTranslation_single (z : Multiplicative ℤ) (i : ℤ) (m : M) :
    bilateralTranslation k M z (Finsupp.single i m) = Finsupp.single (z.toAdd + i) m :=
  Finsupp.domLCongr_single _ _ _

def bilateralSum : (ℤ →₀ M) →ₗ[k] M :=
  Finsupp.lsum k fun _ => LinearMap.id

@[simp] theorem bilateralSum_single (i : ℤ) (m : M) :
    bilateralSum k M (Finsupp.single i m) = m := by simp [bilateralSum]

theorem bilateralSum_translation (z : Multiplicative ℤ) (f : ℤ →₀ M) :
    bilateralSum k M (bilateralTranslation k M z f) = bilateralSum k M f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single i m => simp

theorem bilateral_sub_sum_mem_coinvariants (f : ℤ →₀ M) :
    f - Finsupp.single 0 (bilateralSum k M f) ∈ Coinvariants.ker (bilateralTranslation k M) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [map_add, Finsupp.single_add]
      convert (Coinvariants.ker (bilateralTranslation k M)).add_mem hf hg using 1
      abel
  | single i m =>
      rw [bilateralSum_single]
      simpa using Coinvariants.sub_mem_ker (ρ := bilateralTranslation k M)
        (Multiplicative.ofAdd i) (Finsupp.single 0 m)

theorem bilateralSum_ker :
    LinearMap.ker (bilateralSum k M) = Coinvariants.ker (bilateralTranslation k M) := by
  apply le_antisymm
  · intro f hf
    have hz : bilateralSum k M f = 0 := hf
    simpa only [hz, Finsupp.single_zero, sub_zero] using bilateral_sub_sum_mem_coinvariants k M f
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨z, f⟩, rfl⟩
    change bilateralSum k M (bilateralTranslation k M z f - f) = 0
    rw [map_sub, bilateralSum_translation, sub_self]

theorem multiplicativeInt_generator (z : Multiplicative ℤ) :
    z ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ)) := by
  refine ⟨z.toAdd, ?_⟩
  apply Multiplicative.toAdd.injective
  simp

def bilateralDifference : (ℤ →₀ M) →ₗ[k] (ℤ →₀ M) :=
  bilateralTranslation k M (Multiplicative.ofAdd 1) - LinearMap.id

theorem bilateralSum_ker_eq_range :
    LinearMap.ker (bilateralSum k M) = LinearMap.range (bilateralDifference k M) :=
  (bilateralSum_ker k M).trans
    (cyclic_coinvariantsKer_eq_range _ _ multiplicativeInt_generator)

theorem bilateral_fixed_eq_zero (f : ℤ →₀ M)
    (hf : bilateralTranslation k M (Multiplicative.ofAdd 1) f = f) : f = 0 := by
  have hinv : f ∈ (bilateralTranslation k M).invariants :=
    (mem_invariants_iff_of_forall_mem_zpowers _ _ multiplicativeInt_generator f).mpr hf
  obtain ⟨a, ha⟩ := f.support.exists_notMem
  have hzero : f a = 0 := Finsupp.notMem_support_iff.mp ha
  ext b
  have hb := congrArg (fun u : ℤ →₀ M => u b)
    (hinv (Multiplicative.ofAdd (b - a)))
  simp only [bilateralTranslation_apply, toAdd_ofAdd] at hb
  have he : -(b - a) + b = a := by omega
  rw [he, hzero] at hb
  exact hb.symm

theorem bilateralDifference_injective : Function.Injective (bilateralDifference k M) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro f hf
  exact bilateral_fixed_eq_zero k M f (sub_eq_zero.mp hf)

theorem bilateralSum_surjective : Function.Surjective (bilateralSum k M) :=
  fun m => ⟨Finsupp.single 0 m, bilateralSum_single k M 0 m⟩

end PolycyclicRecognition

end

end OAI
