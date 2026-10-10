import Mathlib
import OAI.Probability.BinarySweep.Trajectories.Trajectory
import OAI.Probability.BinarySweep.Conditional.PlacementBlocks

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
  (x : Placement H k 0) (g : ConditionalChoices H)

def augmentedPlacement (t : Fin (b+1)) : Placement H k t where
  toFun i := ⟨gridPartialSweep bits g.val t (x i).val, by
    rintro ⟨j,hj⟩
    have he := gridPartialSweep_path H g.val g.property t j
    have hx := (gridPartialSweep bits g.val t).injective (he.trans hj)
    exact (x i).property ⟨j,hx⟩⟩
  inj' i j hij := x.injective (Subtype.ext
    ((gridPartialSweep bits g.val t).injective (congrArg Subtype.val hij)))

lemma augmentedPosition_left (t : Fin (b+1)) (i : Fin h) :
    (augmentByChoice H x g).position t (Fin.castAdd k i) = H.position t i := by
  change gridPartialSweep bits g.val t (Fin.append _ _ (Fin.castAdd k i)) = _
  rw [Fin.append_left,gridPartialSweep_path H g.val g.property]

lemma augmentedPosition_right (t : Fin (b+1)) (i : Fin k) :
    (augmentByChoice H x g).position t (Fin.natAdd h i) = (augmentedPlacement H x g t i).val := by
  change gridPartialSweep bits g.val t (Fin.append _ _ (Fin.natAdd h i)) = _
  rw [Fin.append_right]; rfl

lemma augmentedPlacement_zero : augmentedPlacement H x g 0 = x := by
  apply Function.Embedding.ext
  intro index
  apply Subtype.ext
  change gridPartialSweep bits g.val 0 (x index).val = (x index).val
  rw [gridPartialSweep_zero, Equiv.Perm.one_apply]

lemma augmentedPlacement_last : augmentedPlacement H x g (Fin.last b) = placementBijection H k g x := by
  apply Function.Embedding.ext
  intro index
  apply Subtype.ext
  change gridPartialSweep bits g.val (Fin.last b) (x index).val =
    gridSweep bits g.val (x index).val
  rw [gridPartialSweep_last]

def augmentationFreeEquiv (t : Fin (b+1)) :
    FreeSlot (augmentByChoice H x g) t ≃ PlacementComplement (augmentedPlacement H x g t) where
  toFun w := ⟨⟨w.val, by
    rintro ⟨i,hi⟩
    exact w.property ⟨Fin.castAdd k i,(augmentedPosition_left H x g t i).trans hi⟩⟩,by
      rintro ⟨i,hi⟩
      exact w.property ⟨Fin.natAdd h i,(augmentedPosition_right H x g t i).trans
        (congrArg Subtype.val hi)⟩⟩
  invFun w := ⟨w.val.val,by
    rintro ⟨i,hi⟩
    induction i using Fin.addCases with
    | left i =>
      rw [augmentedPosition_left] at hi
      exact w.val.property ⟨i,hi⟩
    | right i =>
      rw [augmentedPosition_right] at hi
      exact w.property ⟨i,Subtype.ext hi⟩⟩
  left_inv w := rfl
  right_inv w := rfl

lemma augmentationFreeEquiv_val (t : Fin (b+1)) (w : FreeSlot (augmentByChoice H x g) t) :
    (augmentationFreeEquiv H x g t w).val.val = w.val := rfl

lemma augmented_gridSweep (g' : ConditionalChoices (augmentByChoice H x g))
    (w : FreeSlot (augmentByChoice H x g) 0) :
    (augmentationFreeEquiv H x g (Fin.last b)
      (remainingBijection (augmentByChoice H x g) g'.val g'.property w)).val =
      remainingBijection H g'.val
        ((augmentByChoice_extension H x g).pathEvent_mono g'.property)
        (augmentationFreeEquiv H x g 0 w).val := rfl

end BinaryCoordinateSweeps

end

end OAI
