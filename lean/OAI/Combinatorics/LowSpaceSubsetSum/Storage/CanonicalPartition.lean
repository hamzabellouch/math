import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSurvival
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.SamplerExecution

namespace OAI

/-! # Canonical consecutive labels for representation partitions

The base labeling is determined by the sorted mixer domain. Randomly
permuting these labels gives the analyzed uniform balanced partition, with
no choice of an arbitrary initial coloring required by the runtime.
-/

noncomputable section
namespace LowSpaceSubsetSum.CanonicalPartition

private def rankFiber (m g : ℕ) (j : Fin m) :
    {x : Fin (m * g) // (finProdFinEquiv.symm x).1 = j} ≃ Fin g where
  toFun x := (finProdFinEquiv.symm x.1).2
  invFun k := ⟨finProdFinEquiv (j, k), by simp⟩
  left_inv x := by
    apply Subtype.ext
    apply finProdFinEquiv.symm.injective
    change finProdFinEquiv.symm (finProdFinEquiv (j, (finProdFinEquiv.symm x.val).2)) =
      finProdFinEquiv.symm x.val
    rw [Equiv.symm_apply_apply]
    exact Prod.ext x.property.symm rfl
  right_inv k := by simp

variable {n : ℕ}

theorem size_eq (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (i : Fin 3) :
    (R.orderedMixers z i).card = RepresentationSetup.blockCount i * (2 * RepresentationSetup.blockHalf n i) := by
  rw [R.orderedMixers_card, ← R.blockCount_half i]
  ring

def ranks (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (i : Fin 3) :
    ↥(R.orderedMixers z i) ≃ Fin (RepresentationSetup.blockCount i * (2 * RepresentationSetup.blockHalf n i)) :=
  ((R.orderedMixers z i).orderIsoOfFin (size_eq R z i)).symm.toEquiv

def labels (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (i : Fin 3)
    (a : ↥(R.orderedMixers z i)) : Fin (RepresentationSetup.blockCount i) :=
  (finProdFinEquiv.symm (ranks R z i a)).1

private def labelFiber (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (i : Fin 3) (j : Fin (RepresentationSetup.blockCount i)) :
    {a : ↥(R.orderedMixers z i) // labels R z i a = j} ≃
      Fin (2 * RepresentationSetup.blockHalf n i) :=
  ((ranks R z i).subtypeEquivOfSubtype
    (p := fun x => (finProdFinEquiv.symm x).1 = j)).trans (rankFiber _ _ j)

def base (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (i : Fin 3) :
    R.Partition z i :=
  ⟨labels R z i, by
    funext j
    exact (Fintype.card_congr (labelFiber R z i j)).trans (Fintype.card_fin _)⟩

def coupling (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (i : Fin 3) :
    SamplerCoupling (R.Partition z i) :=
  ((permutationCoupling n (RepresentationSetup.blockCount i * (2 * RepresentationSetup.blockHalf n i))).map
    (Equiv.permCongr (ranks R z i).symm)).map (coloringOfPermutation (base R z i))

theorem coupling_uniform (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (i : Fin 3) :
    (coupling R z i).idealLaw = @FiniteLaw.uniform _ inferInstance ⟨base R z i⟩ := by
  rw [coupling, SamplerCoupling.map_idealLaw, SamplerCoupling.map_idealLaw,
    permutationCoupling_uniform, FiniteLaw.map_equiv_uniform]
  exact coloringOfPermutation_uniform (base R z i)

theorem coupling_failure (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (i : Fin 3) :
    (coupling R z i).failure ≤ mixerSize n / (2 : ℝ) ^ (n ^ 3) := by
  rw [coupling, SamplerCoupling.map_failure, SamplerCoupling.map_failure]
  have h := permutationCoupling_failure n
    (RepresentationSetup.blockCount i * (2 * RepresentationSetup.blockHalf n i))
  have hc : RepresentationSetup.blockCount i * (2 * RepresentationSetup.blockHalf n i) = mixerSize n := by
    rw [← size_eq R z i, R.orderedMixers_card, RepresentationSetup.halfSize]
    unfold mixerSize
    omega
  simpa only [hc] using h


def execution (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (i : Fin 3) :
    SamplerExecution.Execution (coupling R z i) :=
  SamplerExecution.map
    (SamplerExecution.map
      (SamplerExecution.permutation n (RepresentationSetup.blockCount i *
        (2 * RepresentationSetup.blockHalf n i)))
      (Equiv.permCongr (ranks R z i).symm))
    (coloringOfPermutation (base R z i))

theorem execution_bounded (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (i : Fin 3) :
    (execution R z i).Bounded (mixerSize n * n ^ 3) 0 := by
  have hc : RepresentationSetup.blockCount i * (2 * RepresentationSetup.blockHalf n i) = mixerSize n := by
    rw [← size_eq R z i, R.orderedMixers_card, RepresentationSetup.halfSize]
    unfold mixerSize
    omega
  unfold execution
  apply SamplerExecution.map_bounded
  apply SamplerExecution.map_bounded
  simpa only [hc] using SamplerExecution.permutation_bounded n
    (RepresentationSetup.blockCount i * (2 * RepresentationSetup.blockHalf n i))

end LowSpaceSubsetSum.CanonicalPartition

end

end OAI
