import OAI.GroupTheory.PolycyclicRecognition.Algebra.TupleBarProduct
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ListTupleUpdate
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HomologyBoundary

namespace OAI

/-! # Additivity of the higher integral bar class in every coordinate -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {A : Type} [CommGroup A]

def tupleBarProductPrism {n : ℕ} (v : Fin n → A) (i : Fin n) (a b : A) :
    (Fin (n + 1) → A) →₀ ℤ :=
  (tupleBarListEquiv (n + 1)).symm
    ⟨listBarProductPrism a b ((List.ofFn v).drop (i.val + 1)) ((List.ofFn v).take i.val), by
      have hl : ((List.ofFn v).take i.val).length +
          ((List.ofFn v).drop (i.val + 1)).length + 2 = n + 1 := by
        simp only [List.length_take, List.length_drop, List.length_ofFn]
        omega
      rw [← hl]
      exact listBarProductPrism_grade a b _ _⟩

omit [CommGroup A] in
@[simp] theorem tupleBarProductPrism_toList {n : ℕ} (v : Fin n → A) (i : Fin n) (a b : A) :
    tupleBarToList (n + 1) (tupleBarProductPrism v i a b) =
      listBarProductPrism a b ((List.ofFn v).drop (i.val + 1)) ((List.ofFn v).take i.val) := by
  change (tupleBarListEquiv (n + 1) ((tupleBarListEquiv (n + 1)).symm _)).val = _
  rw [LinearEquiv.apply_symm_apply]

theorem tupleBarProductPrism_boundary {n : ℕ} (v : Fin n → A) (i : Fin n) (a b : A) :
    groupHomology.inhomogeneousChains.d (integralTrivialCoefficient A) n
        (tupleBarProductPrism v i a b) =
      tupleBarProduct (Function.update v i (a * b)) -
        tupleBarProduct (Function.update v i a) - tupleBarProduct (Function.update v i b) := by
  apply tupleBarToList_injective n
  rw [tupleBarToList_d, tupleBarProductPrism_toList, map_sub, map_sub,
    tupleBarProduct_toList, tupleBarProduct_toList, tupleBarProduct_toList,
    listBarProductPrism_boundary, list_ofFn_update_split, list_ofFn_update_split,
    list_ofFn_update_split]

theorem tupleBarProductClass_update_mul {n : ℕ} (v : Fin (n + 1) → A)
    (i : Fin (n + 1)) (a b : A) :
    tupleBarProductClass (Function.update v i (a * b)) =
      tupleBarProductClass (Function.update v i a) + tupleBarProductClass (Function.update v i b) := by
  let C := groupHomology.inhomogeneousChains (integralTrivialCoefficient A)
  let z : C.cycles (n + 1) :=
    tupleBarProductCycle (Function.update v i (a * b)) -
      tupleBarProductCycle (Function.update v i a) - tupleBarProductCycle (Function.update v i b)
  have hz : C.homologyπ (n + 1) z = 0 := by
    apply homologyπ_eq_zero_of_boundary C (n + 1) z (tupleBarProductPrism v i a b)
    rw [groupHomology.inhomogeneousChains.d_def]
    change groupHomology.inhomogeneousChains.d (integralTrivialCoefficient A) (n + 1)
      (tupleBarProductPrism v i a b) =
      groupHomology.iCycles (integralTrivialCoefficient A) (n + 1)
        (tupleBarProductCycle (Function.update v i (a * b)) -
          tupleBarProductCycle (Function.update v i a) - tupleBarProductCycle (Function.update v i b))
    rw [map_sub, map_sub, tupleBarProductCycle_val, tupleBarProductCycle_val,
      tupleBarProductCycle_val]
    exact tupleBarProductPrism_boundary v i a b
  dsimp only [z] at hz
  rw [map_sub, map_sub] at hz
  change tupleBarProductClass (Function.update v i (a * b)) -
    tupleBarProductClass (Function.update v i a) - tupleBarProductClass (Function.update v i b) = 0 at hz
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hz)).trans (add_comm _ _)

end PolycyclicRecognition

end

end OAI
