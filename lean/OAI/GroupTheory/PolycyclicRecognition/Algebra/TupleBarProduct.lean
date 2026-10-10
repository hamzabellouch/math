import OAI.GroupTheory.PolycyclicRecognition.Algebra.ListBarProductPrism
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ListBarDifferential
import Mathlib.Data.List.FinRange

namespace OAI

/-! # Degree-correct integral alternating cycles in the ordinary bar complex -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {A : Type} [CommGroup A]

def tupleBarProduct {n : ℕ} (v : Fin n → A) : (Fin n → A) →₀ ℤ :=
  (tupleBarListEquiv n).symm ⟨listBarProduct (List.ofFn v), by
    simpa only [List.length_ofFn] using listBarProduct_grade (List.ofFn v)⟩

omit [CommGroup A] in
@[simp] theorem tupleBarProduct_toList {n : ℕ} (v : Fin n → A) :
    tupleBarToList n (tupleBarProduct v) = listBarProduct (List.ofFn v) := by
  change (tupleBarListEquiv n ((tupleBarListEquiv n).symm _)).val = _
  rw [LinearEquiv.apply_symm_apply]

theorem tupleBarProduct_boundary {n : ℕ} (v : Fin (n + 1) → A) :
    groupHomology.inhomogeneousChains.d (integralTrivialCoefficient A) n (tupleBarProduct v) = 0 := by
  apply tupleBarToList_injective n
  rw [tupleBarToList_d, tupleBarProduct_toList, listBarProduct_cycle, map_zero]

def tupleBarProductCycle {n : ℕ} (v : Fin (n + 1) → A) :
    groupHomology.cycles (integralTrivialCoefficient A) (n + 1) :=
  groupHomology.cyclesMk (n + 1) n (ChainComplex.next_nat_succ n)
    (tupleBarProduct v) (by
      rw [groupHomology.inhomogeneousChains.d_def]
      exact tupleBarProduct_boundary v)

@[simp] theorem tupleBarProductCycle_val {n : ℕ} (v : Fin (n + 1) → A) :
    groupHomology.iCycles (integralTrivialCoefficient A) (n + 1)
      (tupleBarProductCycle v) = tupleBarProduct v :=
  groupHomology.iCycles_mk (ChainComplex.next_nat_succ n) _ (by
    rw [groupHomology.inhomogeneousChains.d_def]
    exact tupleBarProduct_boundary v)

def tupleBarProductClass {n : ℕ} (v : Fin (n + 1) → A) :
    groupHomology (integralTrivialCoefficient A) (n + 1) :=
  groupHomology.π (integralTrivialCoefficient A) (n + 1) (tupleBarProductCycle v)

omit [CommGroup A] in
theorem tupleBarProduct_eq_zero_of_not_injective {n : ℕ} (v : Fin n → A)
    (hv : ¬Function.Injective v) : tupleBarProduct v = 0 := by
  apply tupleBarToList_injective n
  rw [tupleBarProduct_toList, map_zero]
  exact listBarProduct_eq_zero_of_not_nodup _ (fun h => hv (List.nodup_ofFn.mp h))

theorem tupleBarProductClass_eq_zero_of_eq {n : ℕ} (v : Fin (n + 1) → A)
    {i j : Fin (n + 1)} (h : v i = v j) (hij : i ≠ j) : tupleBarProductClass v = 0 := by
  have hz : tupleBarProductCycle v = 0 := by
    apply (ModuleCat.mono_iff_injective
      (groupHomology.iCycles (integralTrivialCoefficient A) (n + 1))).mp inferInstance
    rw [tupleBarProductCycle_val, map_zero]
    exact tupleBarProduct_eq_zero_of_not_injective v (fun hv => hij (hv h))
  rw [tupleBarProductClass, hz, map_zero]

end PolycyclicRecognition

end

end OAI
