import OAI.NumberTheory.Ostmann.Arithmetic.CanonicalHistoryLeafBulkBasic
import OAI.NumberTheory.Ostmann.Arithmetic.PermutationDiagramComparisonProducts
import OAI.NumberTheory.Ostmann.Arithmetic.TreePermutationHaar

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.CanonicalHistoryLeafBulk

def addressChange (l : ℕ) : Equiv.Perm (Fin (2^l)) :=
  (TreePermutationHaar.leafIndex l).symm.trans (orderedLeafIndex l)

def slotChange (l m : ℕ) : Equiv.Perm (Fin (2^l) × Fin m) :=
  (addressChange l).prodCongr (Equiv.refl _)

def haarPermutation {l m : ℕ} (σ : Equiv.Perm (Fin (2^l) × Fin m)) :
    Equiv.Perm (Fin (2^l) × Fin m) :=
  (slotChange l m).trans (σ.symm.trans (slotChange l m).symm)

def haarSamples {l m : ℕ} {G : Type*} (samples : Fin (2^l) × Fin m→G) :
    Fin (2^l) × Fin m→G := samples ∘ slotChange l m

@[simp] theorem haarSamples_left {l m : ℕ} {G : Type*}
    (samples : Fin (2^l) × Fin m→G) (path : Tree.Leaves l) (i : Fin m) :
    haarSamples samples (TreePermutationHaar.leafIndex l path,i)=
      samples (orderedLeafIndex l path,i) := by
  simp [haarSamples,slotChange,addressChange]

@[simp] theorem haarSamples_right {l m : ℕ} {G : Type*}
    (σ : Equiv.Perm (Fin (2^l) × Fin m))
    (samples : Fin (2^l) × Fin m→G) (path : Tree.Leaves l) (i : Fin m) :
    haarSamples samples ((haarPermutation σ).symm (TreePermutationHaar.leafIndex l path,i))=
      samples (σ (orderedLeafIndex l path,i)) := by
  change samples (slotChange l m ((slotChange l m).symm
    (σ (slotChange l m (TreePermutationHaar.leafIndex l path,i)))))=_
  rw [Equiv.apply_symm_apply]
  simp [slotChange,addressChange]

def orderedProducts {l m : ℕ} {G : Type*} [CommMonoid G]
    (σ : Equiv.Perm (Fin (2^l) × Fin m)) (samples : Fin (2^l) × Fin m→G) :
    (Tree.Leaves l→G) × (Tree.Leaves l→G) :=
  ((fun path => ∏i, samples (orderedLeafIndex l path,i)),
   (fun path => ∏i, samples (σ (orderedLeafIndex l path,i))))

theorem orderedProducts_eq_haar_rows {l m : ℕ} {G : Type*} [CommMonoid G]
    (σ : Equiv.Perm (Fin (2^l) × Fin m)) (samples : Fin (2^l) × Fin m→G) :
    orderedProducts σ samples=
      ((fun path => ∏i, haarSamples samples (TreePermutationHaar.leafIndex l path,i)),
       (fun path => ∏i, haarSamples samples
         ((haarPermutation σ).symm (TreePermutationHaar.leafIndex l path,i)))) := by
  simp [orderedProducts]

theorem orderedProducts_eq_slotLeaves {l m : ℕ} {F : Type*} [Field F]
    (σ : Equiv.Perm (Fin (2^l) × Fin m)) (samples : Fin (2^l) × Fin m→Fˣ) :
    orderedProducts σ samples=
      PermutationDiagramComparison.slotLeaves (haarPermutation σ) (haarSamples samples) :=
  orderedProducts_eq_haar_rows σ samples

theorem orderedProducts_eq_leafPairEquiv {l m : ℕ} {F : Type*} [Field F]
    (σ : Equiv.Perm (Fin (2^l) × Fin m)) (samples : Fin (2^l) × Fin m→Fˣ) :
    orderedProducts σ samples=TreePermutationHaar.leafPairEquiv
      (PermutationHaar.products (haarPermutation σ) (haarSamples samples)) :=
  (orderedProducts_eq_slotLeaves σ samples).trans
    (PermutationDiagramComparison.slotLeaves_eq_leafPairEquiv _ _)

theorem orderedProducts_coupled {l m : ℕ} {F : Type*} [Field F]
    (σ : Equiv.Perm (Fin (2^l) × Fin m)) (hm : 0 < m)
    (samples : Fin (2^l) × Fin m→Fˣ) :
    (TreePermutationHaar.leftPartition (haarPermutation σ)).coupled
      (TreePermutationHaar.rightPartition (haarPermutation σ) hm) (orderedProducts σ samples) := by
  rw [orderedProducts_eq_leafPairEquiv]
  exact (TreePermutationHaar.coupledEquiv (haarPermutation σ) hm
    (PermutationHaar.toCoupled (haarPermutation σ) hm (haarSamples samples))).property

end Ostmann.Arithmetic.CanonicalHistoryLeafBulk

end

end OAI
