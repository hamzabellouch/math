import OAI.NumberTheory.Ostmann.Arithmetic.CanonicalHistoryLeafBulkRows
import OAI.NumberTheory.Ostmann.Arithmetic.GroupHaarImage
import OAI.NumberTheory.Ostmann.Characters.BinaryHaar

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairedFrequencyAverageHaar
open Construction Characters CanonicalHistoryLeafBulk

def leafValue {G : Type*} : {l : ℕ} → BinaryHaar.Leaves G l → Tree.Leaves l → G
  | 0, z, _ => z
  | _l+1, z, path => if path 0 then leafValue z.2 (Fin.tail path)
      else leafValue z.1 (Fin.tail path)

def leavesOfValues {G : Type*} : (l : ℕ) → (Tree.Leaves l → G) → BinaryHaar.Leaves G l
  | 0, f => f (fun i => Fin.elim0 i)
  | l+1, f => (leavesOfValues l (fun path => f (Fin.cons false path)),
      leavesOfValues l (fun path => f (Fin.cons true path)))

@[simp] theorem leafValue_leavesOfValues {G : Type*} (l : ℕ)
    (f : Tree.Leaves l → G) (path : Tree.Leaves l) :
    leafValue (leavesOfValues l f) path = f path := by
  induction l with
  | zero =>
    change f _ = f _
    congr 1
    funext i
    exact Fin.elim0 i
  | succ l ih =>
    simp only [leavesOfValues, leafValue]
    split_ifs with hp
    · rw [ih]
      exact congrArg f (by simpa only [hp] using Fin.cons_self_tail path)
    · rw [ih]
      have hp' : path 0 = false := Bool.eq_false_iff.mpr hp
      exact congrArg f (by simpa only [hp'] using Fin.cons_self_tail path)

@[simp] theorem leavesOfValues_leafValue {G : Type*} (l : ℕ) (z : BinaryHaar.Leaves G l) :
    leavesOfValues l (leafValue z) = z := by
  induction l with
  | zero => rfl
  | succ l ih =>
    simp only [leavesOfValues]
    have hl : (fun path => leafValue z (Fin.cons false path)) = leafValue z.1 := by
      funext path
      simp [leafValue]
    have hr : (fun path => leafValue z (Fin.cons true path)) = leafValue z.2 := by
      funext path
      simp [leafValue]
    rw [hl, hr, ih, ih]

def leafValuesEquiv (G : Type*) (l : ℕ) : (Tree.Leaves l → G) ≃ BinaryHaar.Leaves G l where
  toFun := leavesOfValues l
  invFun := leafValue
  left_inv f := funext (leafValue_leavesOfValues l f)
  right_inv := leavesOfValues_leafValue l

def orderedLeavesEquiv (G : Type*) (l : ℕ) : (Fin (2^l) → G) ≃ BinaryHaar.Leaves G l :=
  (Equiv.arrowCongr (orderedLeafIndex l).symm (Equiv.refl G)).trans (leafValuesEquiv G l)

@[simp] theorem leafValue_orderedLeavesEquiv {G : Type*} (l : ℕ)
    (f : Fin (2^l) → G) (path : Tree.Leaves l) :
    leafValue (orderedLeavesEquiv G l f) path = f (orderedLeafIndex l path) := by
  exact leafValue_leavesOfValues l _ path

def blockProductHom (G : Type*) [CommGroup G] (m l : ℕ) :
    ((Fin (2^l) × Fin m) → G) →* (Fin (2^l) → G) where
  toFun x b := ∏ i : Fin m, x (b,i)
  map_one' := by funext b; simp
  map_mul' x y := by funext b; simp only [Pi.mul_apply, Finset.prod_mul_distrib]

theorem blockProductHom_surjective (G : Type*) [CommGroup G] (m l : ℕ) (hm : 0 < m) :
    Function.Surjective (blockProductHom G m l) := by
  classical
  intro y
  refine ⟨fun bi => if bi.2 = (⟨0,hm⟩ : Fin m) then y bi.1 else 1, ?_⟩
  funext b
  simp [blockProductHom]

def bulkLeaves {G : Type*} [CommGroup G] (m l : ℕ)
    (x : (Fin (2^l) × Fin m) → G) : BinaryHaar.Leaves G l :=
  orderedLeavesEquiv G l (blockProductHom G m l x)

@[simp] theorem leafValue_bulkLeaves {G : Type*} [CommGroup G] (m l : ℕ)
    (x : (Fin (2^l) × Fin m) → G) (path : Tree.Leaves l) :
    leafValue (bulkLeaves m l x) path = ∏ i : Fin m, x (orderedLeafIndex l path,i) := by
  exact leafValue_orderedLeavesEquiv l _ path

theorem leafValue_bulkLeaves_rows {G : Type*} [CommGroup G] (m l : ℕ)
    (f : Fin (2^l) → Fin m → ℕ) (φ : ℕ → G) (path : Tree.Leaves l) :
    leafValue (bulkLeaves m l (fun bi => φ (f bi.1 bi.2))) path =
      ((bulkBlock m l path (rows f)).map φ).prod := by
  rw [leafValue_bulkLeaves, bulkBlock_rows, List.map_ofFn, List.prod_ofFn]
  rfl

end Ostmann.Arithmetic.HistoryPairedFrequencyAverageHaar

end

end OAI
