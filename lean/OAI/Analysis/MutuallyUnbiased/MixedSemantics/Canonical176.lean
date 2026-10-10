import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22528 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22528step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22528step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22528step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22528step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22528 raw22528Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22528 raw22528Labels = mixedMoment B raw22528step0 raw22528step0Labels := by
      have hz : ∀ j, raw22528 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22528step0 = (fun i j => raw22528 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22528step0 raw22528; decide +kernel
      have hl : raw22528step0Labels = raw22528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22528 raw22528Labels permutation434 hz
    mixedMoment B raw22528step0 raw22528step0Labels = mixedMoment B raw22528step1 raw22528step1Labels := by
      have hz : ∀ j, raw22528step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22528step1 = (fun i j => raw22528step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22528step1 raw22528step0; decide +kernel
      have hl : raw22528step1Labels = raw22528step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22528step0 raw22528step0Labels permutation56 hz
    mixedMoment B raw22528step1 raw22528step1Labels = mixedMoment B raw22528step2 raw22528step2Labels := by
      have ha : raw22528step2 = (fun i j => raw22528step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22528step2 raw22528step1; decide +kernel
      have hl : raw22528step2Labels = raw22528step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22528step1 raw22528step1Labels permutation8 permutation6
    mixedMoment B raw22528step2 raw22528step2Labels = mixedMoment B raw22528step3 raw22528step3Labels := by
      have ha : raw22528step3 = raw22528step2 := by apply Matrix.ext; unfold raw22528step3 raw22528step2; decide +kernel
      have hl : raw22528step2Labels = labelEmbedding9 ∘ raw22528step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22528step2 raw22528step2Labels raw22528step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw22529 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22529step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22529step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22529step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22529step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22529step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22529step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22529 raw22529Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22529 raw22529Labels = mixedMoment B raw22529step0 raw22529step0Labels := by
      have hz : ∀ j, raw22529 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22529step0 = (fun i j => raw22529 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22529step0 raw22529; decide +kernel
      have hl : raw22529step0Labels = raw22529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22529 raw22529Labels permutation346 hz
    mixedMoment B raw22529step0 raw22529step0Labels = mixedMoment B raw22529step1 raw22529step1Labels := by
      have hz : ∀ j, raw22529step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22529step1 = (fun i j => raw22529step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22529step1 raw22529step0; decide +kernel
      have hl : raw22529step1Labels = raw22529step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22529step0 raw22529step0Labels permutation56 hz
    mixedMoment B raw22529step1 raw22529step1Labels = mixedMoment B raw22529step2 raw22529step2Labels := by
      have ha : raw22529step2 = (fun i j => raw22529step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22529step2 raw22529step1; decide +kernel
      have hl : raw22529step2Labels = raw22529step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22529step1 raw22529step1Labels permutation8 permutation6
    mixedMoment B raw22529step2 raw22529step2Labels = mixedMoment B raw22529step3 raw22529step3Labels := by
      have ha : raw22529step3 = raw22529step2 := by apply Matrix.ext; unfold raw22529step3 raw22529step2; decide +kernel
      have hl : raw22529step2Labels = labelEmbedding9 ∘ raw22529step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22529step2 raw22529step2Labels raw22529step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw22530 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22530step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22530step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, -1, 2], ![-1, -1, 2]]
def raw22530step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22530step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw22530step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22530step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw22530step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22530 raw22530Labels = mixedMoment B node4628 node4628Labels := by
  calc
    mixedMoment B raw22530 raw22530Labels = mixedMoment B raw22530step0 raw22530step0Labels := by
      have hz : ∀ j, raw22530 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22530step0 = (fun i j => raw22530 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22530step0 raw22530; decide +kernel
      have hl : raw22530step0Labels = raw22530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22530 raw22530Labels permutation434 hz
    mixedMoment B raw22530step0 raw22530step0Labels = mixedMoment B raw22530step1 raw22530step1Labels := by
      have hz : ∀ j, raw22530step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22530step1 = (fun i j => raw22530step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22530step1 raw22530step0; decide +kernel
      have hl : raw22530step1Labels = raw22530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22530step0 raw22530step0Labels permutation80 hz
    mixedMoment B raw22530step1 raw22530step1Labels = mixedMoment B raw22530step2 raw22530step2Labels := by
      have hz : ∀ j, raw22530step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22530step2 = (fun i j => raw22530step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22530step2 raw22530step1; decide +kernel
      have hl : raw22530step2Labels = raw22530step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22530step1 raw22530step1Labels permutation14 hz
    mixedMoment B raw22530step2 raw22530step2Labels = mixedMoment B raw22530step3 raw22530step3Labels := by
      have ha : raw22530step3 = (fun i j => raw22530step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22530step3 raw22530step2; decide +kernel
      have hl : raw22530step3Labels = raw22530step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22530step2 raw22530step2Labels permutation2 permutation6
    mixedMoment B raw22530step3 raw22530step3Labels = mixedMoment B raw22530step4 raw22530step4Labels := by
      have ha : raw22530step4 = raw22530step3 := by apply Matrix.ext; unfold raw22530step4 raw22530step3; decide +kernel
      have hl : raw22530step3Labels = labelEmbedding9 ∘ raw22530step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22530step3 raw22530step3Labels raw22530step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4628 node4628Labels := by rfl

def raw22531 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22531step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22531step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22531step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 0, 2], ![1, -3, 2]]
def raw22531step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22531step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw22531step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22531step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw22531step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22531 raw22531Labels = mixedMoment B node4510 node4510Labels := by
  calc
    mixedMoment B raw22531 raw22531Labels = mixedMoment B raw22531step0 raw22531step0Labels := by
      have hz : ∀ j, raw22531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22531step0 = (fun i j => raw22531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22531step0 raw22531; decide +kernel
      have hl : raw22531step0Labels = raw22531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22531 raw22531Labels permutation434 hz
    mixedMoment B raw22531step0 raw22531step0Labels = mixedMoment B raw22531step1 raw22531step1Labels := by
      have hz : ∀ j, raw22531step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22531step1 = (fun i j => raw22531step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22531step1 raw22531step0; decide +kernel
      have hl : raw22531step1Labels = raw22531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22531step0 raw22531step0Labels permutation80 hz
    mixedMoment B raw22531step1 raw22531step1Labels = mixedMoment B raw22531step2 raw22531step2Labels := by
      have hz : ∀ j, raw22531step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22531step2 = (fun i j => raw22531step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22531step2 raw22531step1; decide +kernel
      have hl : raw22531step2Labels = raw22531step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22531step1 raw22531step1Labels permutation14 hz
    mixedMoment B raw22531step2 raw22531step2Labels = mixedMoment B raw22531step3 raw22531step3Labels := by
      have ha : raw22531step3 = (fun i j => raw22531step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22531step3 raw22531step2; decide +kernel
      have hl : raw22531step3Labels = raw22531step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22531step2 raw22531step2Labels permutation2 permutation6
    mixedMoment B raw22531step3 raw22531step3Labels = mixedMoment B raw22531step4 raw22531step4Labels := by
      have ha : raw22531step4 = raw22531step3 := by apply Matrix.ext; unfold raw22531step4 raw22531step3; decide +kernel
      have hl : raw22531step3Labels = labelEmbedding9 ∘ raw22531step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22531step3 raw22531step3Labels raw22531step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4510 node4510Labels := by rfl

def raw22532 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22532step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22532step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22532step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22532step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22532step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22532 raw22532Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw22532 raw22532Labels = mixedMoment B raw22532step0 raw22532step0Labels := by
      have hz : ∀ j, raw22532 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22532step0 = (fun i j => raw22532 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22532step0 raw22532; decide +kernel
      have hl : raw22532step0Labels = raw22532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22532 raw22532Labels permutation434 hz
    mixedMoment B raw22532step0 raw22532step0Labels = mixedMoment B raw22532step1 raw22532step1Labels := by
      have hz : ∀ j, raw22532step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22532step1 = (fun i j => raw22532step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22532step1 raw22532step0; decide +kernel
      have hl : raw22532step1Labels = raw22532step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22532step0 raw22532step0Labels permutation80 hz
    mixedMoment B raw22532step1 raw22532step1Labels = mixedMoment B raw22532step2 raw22532step2Labels := by
      have ha : raw22532step2 = (fun i j => raw22532step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22532step2 raw22532step1; decide +kernel
      have hl : raw22532step2Labels = raw22532step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22532step1 raw22532step1Labels permutation8 permutation6
    mixedMoment B raw22532step2 raw22532step2Labels = mixedMoment B raw22532step3 raw22532step3Labels := by
      have ha : raw22532step3 = raw22532step2 := by apply Matrix.ext; unfold raw22532step3 raw22532step2; decide +kernel
      have hl : raw22532step2Labels = labelEmbedding9 ∘ raw22532step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22532step2 raw22532step2Labels raw22532step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

def raw22533 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22533step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22533step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22533step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22533step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22533step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22533step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22533step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22533 raw22533Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw22533 raw22533Labels = mixedMoment B raw22533step0 raw22533step0Labels := by
      have hz : ∀ j, raw22533 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22533step0 = (fun i j => raw22533 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22533step0 raw22533; decide +kernel
      have hl : raw22533step0Labels = raw22533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22533 raw22533Labels permutation434 hz
    mixedMoment B raw22533step0 raw22533step0Labels = mixedMoment B raw22533step1 raw22533step1Labels := by
      have hz : ∀ j, raw22533step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22533step1 = (fun i j => raw22533step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22533step1 raw22533step0; decide +kernel
      have hl : raw22533step1Labels = raw22533step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22533step0 raw22533step0Labels permutation56 hz
    mixedMoment B raw22533step1 raw22533step1Labels = mixedMoment B raw22533step2 raw22533step2Labels := by
      have ha : raw22533step2 = (fun i j => raw22533step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22533step2 raw22533step1; decide +kernel
      have hl : raw22533step2Labels = raw22533step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22533step1 raw22533step1Labels permutation8 permutation6
    mixedMoment B raw22533step2 raw22533step2Labels = mixedMoment B raw22533step3 raw22533step3Labels := by
      have ha : raw22533step3 = raw22533step2 := by apply Matrix.ext; unfold raw22533step3 raw22533step2; decide +kernel
      have hl : raw22533step2Labels = labelEmbedding9 ∘ raw22533step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22533step2 raw22533step2Labels raw22533step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

def raw22534 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22534step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22534step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22534step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22534step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22534step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22534 raw22534Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw22534 raw22534Labels = mixedMoment B raw22534step0 raw22534step0Labels := by
      have hz : ∀ j, raw22534 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22534step0 = (fun i j => raw22534 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22534step0 raw22534; decide +kernel
      have hl : raw22534step0Labels = raw22534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22534 raw22534Labels permutation346 hz
    mixedMoment B raw22534step0 raw22534step0Labels = mixedMoment B raw22534step1 raw22534step1Labels := by
      have hz : ∀ j, raw22534step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22534step1 = (fun i j => raw22534step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22534step1 raw22534step0; decide +kernel
      have hl : raw22534step1Labels = raw22534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22534step0 raw22534step0Labels permutation56 hz
    mixedMoment B raw22534step1 raw22534step1Labels = mixedMoment B raw22534step2 raw22534step2Labels := by
      have ha : raw22534step2 = (fun i j => raw22534step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22534step2 raw22534step1; decide +kernel
      have hl : raw22534step2Labels = raw22534step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22534step1 raw22534step1Labels permutation8 permutation6
    mixedMoment B raw22534step2 raw22534step2Labels = mixedMoment B raw22534step3 raw22534step3Labels := by
      have ha : raw22534step3 = raw22534step2 := by apply Matrix.ext; unfold raw22534step3 raw22534step2; decide +kernel
      have hl : raw22534step2Labels = labelEmbedding9 ∘ raw22534step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22534step2 raw22534step2Labels raw22534step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

def raw22535 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22535step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22535step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22535step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-3, 1, 2], ![1, -3, 2]]
def raw22535step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22535step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw22535step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22535step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw22535step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22535 raw22535Labels = mixedMoment B node4626 node4626Labels := by
  calc
    mixedMoment B raw22535 raw22535Labels = mixedMoment B raw22535step0 raw22535step0Labels := by
      have hz : ∀ j, raw22535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22535step0 = (fun i j => raw22535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22535step0 raw22535; decide +kernel
      have hl : raw22535step0Labels = raw22535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22535 raw22535Labels permutation434 hz
    mixedMoment B raw22535step0 raw22535step0Labels = mixedMoment B raw22535step1 raw22535step1Labels := by
      have hz : ∀ j, raw22535step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22535step1 = (fun i j => raw22535step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22535step1 raw22535step0; decide +kernel
      have hl : raw22535step1Labels = raw22535step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22535step0 raw22535step0Labels permutation80 hz
    mixedMoment B raw22535step1 raw22535step1Labels = mixedMoment B raw22535step2 raw22535step2Labels := by
      have hz : ∀ j, raw22535step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22535step2 = (fun i j => raw22535step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22535step2 raw22535step1; decide +kernel
      have hl : raw22535step2Labels = raw22535step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22535step1 raw22535step1Labels permutation14 hz
    mixedMoment B raw22535step2 raw22535step2Labels = mixedMoment B raw22535step3 raw22535step3Labels := by
      have ha : raw22535step3 = (fun i j => raw22535step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22535step3 raw22535step2; decide +kernel
      have hl : raw22535step3Labels = raw22535step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22535step2 raw22535step2Labels permutation2 permutation6
    mixedMoment B raw22535step3 raw22535step3Labels = mixedMoment B raw22535step4 raw22535step4Labels := by
      have ha : raw22535step4 = raw22535step3 := by apply Matrix.ext; unfold raw22535step4 raw22535step3; decide +kernel
      have hl : raw22535step3Labels = labelEmbedding9 ∘ raw22535step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22535step3 raw22535step3Labels raw22535step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4626 node4626Labels := by rfl

def raw22536 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22536Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22536step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22536step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22536step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22536 raw22536Labels = mixedMoment B node1419 node1419Labels := by
  calc
    mixedMoment B raw22536 raw22536Labels = mixedMoment B raw22536step0 raw22536step0Labels := by
      have hz : ∀ j, raw22536 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22536step0 = (fun i j => raw22536 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22536step0 raw22536; decide +kernel
      have hl : raw22536step0Labels = raw22536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22536 raw22536Labels permutation434 hz
    mixedMoment B raw22536step0 raw22536step0Labels = mixedMoment B raw22536step1 raw22536step1Labels := by
      have hz : ∀ j, raw22536step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22536step1 = (fun i j => raw22536step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22536step1 raw22536step0; decide +kernel
      have hl : raw22536step1Labels = raw22536step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22536step0 raw22536step0Labels permutation80 hz
    mixedMoment B raw22536step1 raw22536step1Labels = mixedMoment B raw22536step2 raw22536step2Labels := by
      have ha : raw22536step2 = (fun i j => raw22536step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22536step2 raw22536step1; decide +kernel
      have hl : raw22536step2Labels = raw22536step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22536step1 raw22536step1Labels permutation8 permutation6
    _ = mixedMoment B node1419 node1419Labels := by rfl

def raw22537 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22537Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22537step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22537step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22537step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22537 raw22537Labels = mixedMoment B node1419 node1419Labels := by
  calc
    mixedMoment B raw22537 raw22537Labels = mixedMoment B raw22537step0 raw22537step0Labels := by
      have hz : ∀ j, raw22537 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22537step0 = (fun i j => raw22537 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22537step0 raw22537; decide +kernel
      have hl : raw22537step0Labels = raw22537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22537 raw22537Labels permutation434 hz
    mixedMoment B raw22537step0 raw22537step0Labels = mixedMoment B raw22537step1 raw22537step1Labels := by
      have hz : ∀ j, raw22537step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22537step1 = (fun i j => raw22537step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22537step1 raw22537step0; decide +kernel
      have hl : raw22537step1Labels = raw22537step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22537step0 raw22537step0Labels permutation56 hz
    mixedMoment B raw22537step1 raw22537step1Labels = mixedMoment B raw22537step2 raw22537step2Labels := by
      have ha : raw22537step2 = (fun i j => raw22537step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22537step2 raw22537step1; decide +kernel
      have hl : raw22537step2Labels = raw22537step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22537step1 raw22537step1Labels permutation8 permutation6
    _ = mixedMoment B node1419 node1419Labels := by rfl

def raw22538 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22538Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22538step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22538step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22538step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22538step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22538step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22538 raw22538Labels = mixedMoment B node1419 node1419Labels := by
  calc
    mixedMoment B raw22538 raw22538Labels = mixedMoment B raw22538step0 raw22538step0Labels := by
      have hz : ∀ j, raw22538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22538step0 = (fun i j => raw22538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22538step0 raw22538; decide +kernel
      have hl : raw22538step0Labels = raw22538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22538 raw22538Labels permutation346 hz
    mixedMoment B raw22538step0 raw22538step0Labels = mixedMoment B raw22538step1 raw22538step1Labels := by
      have hz : ∀ j, raw22538step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22538step1 = (fun i j => raw22538step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22538step1 raw22538step0; decide +kernel
      have hl : raw22538step1Labels = raw22538step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22538step0 raw22538step0Labels permutation56 hz
    mixedMoment B raw22538step1 raw22538step1Labels = mixedMoment B raw22538step2 raw22538step2Labels := by
      have ha : raw22538step2 = (fun i j => raw22538step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22538step2 raw22538step1; decide +kernel
      have hl : raw22538step2Labels = raw22538step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22538step1 raw22538step1Labels permutation8 permutation6
    _ = mixedMoment B node1419 node1419Labels := by rfl

def raw22539 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22539Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22539step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22539step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22539step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22539step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-3, 1, 2], ![0, -2, 2]]
def raw22539step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22539step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw22539step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22539 raw22539Labels = mixedMoment B node1454 node1454Labels := by
  calc
    mixedMoment B raw22539 raw22539Labels = mixedMoment B raw22539step0 raw22539step0Labels := by
      have hz : ∀ j, raw22539 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22539step0 = (fun i j => raw22539 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22539step0 raw22539; decide +kernel
      have hl : raw22539step0Labels = raw22539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22539 raw22539Labels permutation434 hz
    mixedMoment B raw22539step0 raw22539step0Labels = mixedMoment B raw22539step1 raw22539step1Labels := by
      have hz : ∀ j, raw22539step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22539step1 = (fun i j => raw22539step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22539step1 raw22539step0; decide +kernel
      have hl : raw22539step1Labels = raw22539step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22539step0 raw22539step0Labels permutation80 hz
    mixedMoment B raw22539step1 raw22539step1Labels = mixedMoment B raw22539step2 raw22539step2Labels := by
      have hz : ∀ j, raw22539step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22539step2 = (fun i j => raw22539step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22539step2 raw22539step1; decide +kernel
      have hl : raw22539step2Labels = raw22539step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22539step1 raw22539step1Labels permutation14 hz
    mixedMoment B raw22539step2 raw22539step2Labels = mixedMoment B raw22539step3 raw22539step3Labels := by
      have ha : raw22539step3 = (fun i j => raw22539step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22539step3 raw22539step2; decide +kernel
      have hl : raw22539step3Labels = raw22539step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22539step2 raw22539step2Labels permutation2 permutation6
    _ = mixedMoment B node1454 node1454Labels := by rfl

def raw22540 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22540Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22540step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22540step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22540step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 0, 2], ![-1, -1, 2]]
def raw22540step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22540step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -2, 0], ![2, -1, -1]]
def raw22540step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22540 raw22540Labels = mixedMoment B node1455 node1455Labels := by
  calc
    mixedMoment B raw22540 raw22540Labels = mixedMoment B raw22540step0 raw22540step0Labels := by
      have hz : ∀ j, raw22540 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22540step0 = (fun i j => raw22540 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22540step0 raw22540; decide +kernel
      have hl : raw22540step0Labels = raw22540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22540 raw22540Labels permutation434 hz
    mixedMoment B raw22540step0 raw22540step0Labels = mixedMoment B raw22540step1 raw22540step1Labels := by
      have hz : ∀ j, raw22540step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22540step1 = (fun i j => raw22540step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22540step1 raw22540step0; decide +kernel
      have hl : raw22540step1Labels = raw22540step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22540step0 raw22540step0Labels permutation80 hz
    mixedMoment B raw22540step1 raw22540step1Labels = mixedMoment B raw22540step2 raw22540step2Labels := by
      have hz : ∀ j, raw22540step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22540step2 = (fun i j => raw22540step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22540step2 raw22540step1; decide +kernel
      have hl : raw22540step2Labels = raw22540step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22540step1 raw22540step1Labels permutation14 hz
    mixedMoment B raw22540step2 raw22540step2Labels = mixedMoment B raw22540step3 raw22540step3Labels := by
      have ha : raw22540step3 = (fun i j => raw22540step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22540step3 raw22540step2; decide +kernel
      have hl : raw22540step3Labels = raw22540step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22540step2 raw22540step2Labels permutation2 permutation6
    _ = mixedMoment B node1455 node1455Labels := by rfl

def raw22541 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22541Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22541step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22541step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22541step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22541step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22541step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22541 raw22541Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw22541 raw22541Labels = mixedMoment B raw22541step0 raw22541step0Labels := by
      have hz : ∀ j, raw22541 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22541step0 = (fun i j => raw22541 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22541step0 raw22541; decide +kernel
      have hl : raw22541step0Labels = raw22541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22541 raw22541Labels permutation434 hz
    mixedMoment B raw22541step0 raw22541step0Labels = mixedMoment B raw22541step1 raw22541step1Labels := by
      have hz : ∀ j, raw22541step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22541step1 = (fun i j => raw22541step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22541step1 raw22541step0; decide +kernel
      have hl : raw22541step1Labels = raw22541step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22541step0 raw22541step0Labels permutation80 hz
    mixedMoment B raw22541step1 raw22541step1Labels = mixedMoment B raw22541step2 raw22541step2Labels := by
      have ha : raw22541step2 = (fun i j => raw22541step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22541step2 raw22541step1; decide +kernel
      have hl : raw22541step2Labels = raw22541step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22541step1 raw22541step1Labels permutation8 permutation6
    _ = mixedMoment B node1049 node1049Labels := by rfl

def raw22542 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22542Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22542step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22542 raw22542Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw22542 raw22542Labels = mixedMoment B raw22542step0 raw22542step0Labels := by
      have hz : ∀ j, raw22542 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22542step0 = (fun i j => raw22542 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22542step0 raw22542; decide +kernel
      have hl : raw22542step0Labels = raw22542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22542 raw22542Labels permutation434 hz
    mixedMoment B raw22542step0 raw22542step0Labels = mixedMoment B raw22542step1 raw22542step1Labels := by
      have ha : raw22542step1 = (fun i j => raw22542step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22542step1 raw22542step0; decide +kernel
      have hl : raw22542step1Labels = raw22542step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22542step0 raw22542step0Labels permutation38 permutation6
    _ = mixedMoment B node1219 node1219Labels := by rfl

def raw22543 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22543Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22543step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22543 raw22543Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw22543 raw22543Labels = mixedMoment B raw22543step0 raw22543step0Labels := by
      have hz : ∀ j, raw22543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22543step0 = (fun i j => raw22543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22543step0 raw22543; decide +kernel
      have hl : raw22543step0Labels = raw22543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22543 raw22543Labels permutation346 hz
    mixedMoment B raw22543step0 raw22543step0Labels = mixedMoment B raw22543step1 raw22543step1Labels := by
      have ha : raw22543step1 = (fun i j => raw22543step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22543step1 raw22543step0; decide +kernel
      have hl : raw22543step1Labels = raw22543step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22543step0 raw22543step0Labels permutation38 permutation6
    _ = mixedMoment B node1219 node1219Labels := by rfl

def raw22544 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22544Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22544step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22544step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22544step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22544step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22544 raw22544Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw22544 raw22544Labels = mixedMoment B raw22544step0 raw22544step0Labels := by
      have hz : ∀ j, raw22544 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22544step0 = (fun i j => raw22544 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22544step0 raw22544; decide +kernel
      have hl : raw22544step0Labels = raw22544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22544 raw22544Labels permutation434 hz
    mixedMoment B raw22544step0 raw22544step0Labels = mixedMoment B raw22544step1 raw22544step1Labels := by
      have hz : ∀ j, raw22544step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22544step1 = (fun i j => raw22544step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22544step1 raw22544step0; decide +kernel
      have hl : raw22544step1Labels = raw22544step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22544step0 raw22544step0Labels permutation80 hz
    mixedMoment B raw22544step1 raw22544step1Labels = mixedMoment B raw22544step2 raw22544step2Labels := by
      have ha : raw22544step2 = (fun i j => raw22544step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22544step2 raw22544step1; decide +kernel
      have hl : raw22544step2Labels = raw22544step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22544step1 raw22544step1Labels permutation8 permutation6
    _ = mixedMoment B node1273 node1273Labels := by rfl

def raw22545 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22545Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22545step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22545step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22545step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22545 raw22545Labels = mixedMoment B node1274 node1274Labels := by
  calc
    mixedMoment B raw22545 raw22545Labels = mixedMoment B raw22545step0 raw22545step0Labels := by
      have hz : ∀ j, raw22545 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22545step0 = (fun i j => raw22545 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22545step0 raw22545; decide +kernel
      have hl : raw22545step0Labels = raw22545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22545 raw22545Labels permutation434 hz
    mixedMoment B raw22545step0 raw22545step0Labels = mixedMoment B raw22545step1 raw22545step1Labels := by
      have hz : ∀ j, raw22545step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22545step1 = (fun i j => raw22545step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22545step1 raw22545step0; decide +kernel
      have hl : raw22545step1Labels = raw22545step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22545step0 raw22545step0Labels permutation80 hz
    mixedMoment B raw22545step1 raw22545step1Labels = mixedMoment B raw22545step2 raw22545step2Labels := by
      have ha : raw22545step2 = (fun i j => raw22545step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22545step2 raw22545step1; decide +kernel
      have hl : raw22545step2Labels = raw22545step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22545step1 raw22545step1Labels permutation8 permutation6
    _ = mixedMoment B node1274 node1274Labels := by rfl

def raw22546 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22546Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22546step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22546step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22546 raw22546Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw22546 raw22546Labels = mixedMoment B raw22546step0 raw22546step0Labels := by
      have hz : ∀ j, raw22546 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22546step0 = (fun i j => raw22546 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22546step0 raw22546; decide +kernel
      have hl : raw22546step0Labels = raw22546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22546 raw22546Labels permutation434 hz
    mixedMoment B raw22546step0 raw22546step0Labels = mixedMoment B raw22546step1 raw22546step1Labels := by
      have hz : ∀ j, raw22546step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22546step1 = (fun i j => raw22546step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22546step1 raw22546step0; decide +kernel
      have hl : raw22546step1Labels = raw22546step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22546step0 raw22546step0Labels permutation56 hz
    mixedMoment B raw22546step1 raw22546step1Labels = mixedMoment B raw22546step2 raw22546step2Labels := by
      have ha : raw22546step2 = (fun i j => raw22546step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22546step2 raw22546step1; decide +kernel
      have hl : raw22546step2Labels = raw22546step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22546step1 raw22546step1Labels permutation8 permutation6
    _ = mixedMoment B node1049 node1049Labels := by rfl

def raw22547 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22547Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22547step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22547step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22547 raw22547Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw22547 raw22547Labels = mixedMoment B raw22547step0 raw22547step0Labels := by
      have hz : ∀ j, raw22547 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22547step0 = (fun i j => raw22547 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22547step0 raw22547; decide +kernel
      have hl : raw22547step0Labels = raw22547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22547 raw22547Labels permutation434 hz
    mixedMoment B raw22547step0 raw22547step0Labels = mixedMoment B raw22547step1 raw22547step1Labels := by
      have ha : raw22547step1 = (fun i j => raw22547step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22547step1 raw22547step0; decide +kernel
      have hl : raw22547step1Labels = raw22547step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22547step0 raw22547step0Labels permutation32 permutation6
    _ = mixedMoment B node1219 node1219Labels := by rfl

def raw22548 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22548Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22548step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22548 raw22548Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw22548 raw22548Labels = mixedMoment B raw22548step0 raw22548step0Labels := by
      have hz : ∀ j, raw22548 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22548step0 = (fun i j => raw22548 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22548step0 raw22548; decide +kernel
      have hl : raw22548step0Labels = raw22548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22548 raw22548Labels permutation265 hz
    mixedMoment B raw22548step0 raw22548step0Labels = mixedMoment B raw22548step1 raw22548step1Labels := by
      have ha : raw22548step1 = (fun i j => raw22548step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22548step1 raw22548step0; decide +kernel
      have hl : raw22548step1Labels = raw22548step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22548step0 raw22548step0Labels permutation38 permutation6
    _ = mixedMoment B node1219 node1219Labels := by rfl

def raw22549 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22549Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22549step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22549step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22549step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22549 raw22549Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw22549 raw22549Labels = mixedMoment B raw22549step0 raw22549step0Labels := by
      have hz : ∀ j, raw22549 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22549step0 = (fun i j => raw22549 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22549step0 raw22549; decide +kernel
      have hl : raw22549step0Labels = raw22549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22549 raw22549Labels permutation434 hz
    mixedMoment B raw22549step0 raw22549step0Labels = mixedMoment B raw22549step1 raw22549step1Labels := by
      have hz : ∀ j, raw22549step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22549step1 = (fun i j => raw22549step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22549step1 raw22549step0; decide +kernel
      have hl : raw22549step1Labels = raw22549step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22549step0 raw22549step0Labels permutation56 hz
    mixedMoment B raw22549step1 raw22549step1Labels = mixedMoment B raw22549step2 raw22549step2Labels := by
      have ha : raw22549step2 = (fun i j => raw22549step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22549step2 raw22549step1; decide +kernel
      have hl : raw22549step2Labels = raw22549step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22549step1 raw22549step1Labels permutation8 permutation6
    _ = mixedMoment B node1273 node1273Labels := by rfl

def raw22550 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22550Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22550step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22550step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22550step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22550 raw22550Labels = mixedMoment B node1274 node1274Labels := by
  calc
    mixedMoment B raw22550 raw22550Labels = mixedMoment B raw22550step0 raw22550step0Labels := by
      have hz : ∀ j, raw22550 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22550step0 = (fun i j => raw22550 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22550step0 raw22550; decide +kernel
      have hl : raw22550step0Labels = raw22550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22550 raw22550Labels permutation434 hz
    mixedMoment B raw22550step0 raw22550step0Labels = mixedMoment B raw22550step1 raw22550step1Labels := by
      have hz : ∀ j, raw22550step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22550step1 = (fun i j => raw22550step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22550step1 raw22550step0; decide +kernel
      have hl : raw22550step1Labels = raw22550step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22550step0 raw22550step0Labels permutation56 hz
    mixedMoment B raw22550step1 raw22550step1Labels = mixedMoment B raw22550step2 raw22550step2Labels := by
      have ha : raw22550step2 = (fun i j => raw22550step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22550step2 raw22550step1; decide +kernel
      have hl : raw22550step2Labels = raw22550step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22550step1 raw22550step1Labels permutation8 permutation6
    _ = mixedMoment B node1274 node1274Labels := by rfl

def raw22551 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22551Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22551step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22551step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22551step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22551step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22551 raw22551Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw22551 raw22551Labels = mixedMoment B raw22551step0 raw22551step0Labels := by
      have hz : ∀ j, raw22551 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22551step0 = (fun i j => raw22551 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22551step0 raw22551; decide +kernel
      have hl : raw22551step0Labels = raw22551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22551 raw22551Labels permutation346 hz
    mixedMoment B raw22551step0 raw22551step0Labels = mixedMoment B raw22551step1 raw22551step1Labels := by
      have hz : ∀ j, raw22551step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22551step1 = (fun i j => raw22551step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22551step1 raw22551step0; decide +kernel
      have hl : raw22551step1Labels = raw22551step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22551step0 raw22551step0Labels permutation56 hz
    mixedMoment B raw22551step1 raw22551step1Labels = mixedMoment B raw22551step2 raw22551step2Labels := by
      have ha : raw22551step2 = (fun i j => raw22551step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22551step2 raw22551step1; decide +kernel
      have hl : raw22551step2Labels = raw22551step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22551step1 raw22551step1Labels permutation8 permutation6
    _ = mixedMoment B node1049 node1049Labels := by rfl

def raw22552 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22552Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22552step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22552 raw22552Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw22552 raw22552Labels = mixedMoment B raw22552step0 raw22552step0Labels := by
      have hz : ∀ j, raw22552 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22552step0 = (fun i j => raw22552 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22552step0 raw22552; decide +kernel
      have hl : raw22552step0Labels = raw22552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22552 raw22552Labels permutation346 hz
    mixedMoment B raw22552step0 raw22552step0Labels = mixedMoment B raw22552step1 raw22552step1Labels := by
      have ha : raw22552step1 = (fun i j => raw22552step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22552step1 raw22552step0; decide +kernel
      have hl : raw22552step1Labels = raw22552step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22552step0 raw22552step0Labels permutation32 permutation6
    _ = mixedMoment B node1219 node1219Labels := by rfl

def raw22553 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22553Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22553step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22553 raw22553Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw22553 raw22553Labels = mixedMoment B raw22553step0 raw22553step0Labels := by
      have hz : ∀ j, raw22553 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22553step0 = (fun i j => raw22553 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22553step0 raw22553; decide +kernel
      have hl : raw22553step0Labels = raw22553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22553 raw22553Labels permutation265 hz
    mixedMoment B raw22553step0 raw22553step0Labels = mixedMoment B raw22553step1 raw22553step1Labels := by
      have ha : raw22553step1 = (fun i j => raw22553step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22553step1 raw22553step0; decide +kernel
      have hl : raw22553step1Labels = raw22553step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22553step0 raw22553step0Labels permutation32 permutation6
    _ = mixedMoment B node1219 node1219Labels := by rfl

def raw22554 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22554Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22554step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22554step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22554step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22554 raw22554Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw22554 raw22554Labels = mixedMoment B raw22554step0 raw22554step0Labels := by
      have hz : ∀ j, raw22554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22554step0 = (fun i j => raw22554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22554step0 raw22554; decide +kernel
      have hl : raw22554step0Labels = raw22554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22554 raw22554Labels permutation346 hz
    mixedMoment B raw22554step0 raw22554step0Labels = mixedMoment B raw22554step1 raw22554step1Labels := by
      have hz : ∀ j, raw22554step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22554step1 = (fun i j => raw22554step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22554step1 raw22554step0; decide +kernel
      have hl : raw22554step1Labels = raw22554step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22554step0 raw22554step0Labels permutation56 hz
    mixedMoment B raw22554step1 raw22554step1Labels = mixedMoment B raw22554step2 raw22554step2Labels := by
      have ha : raw22554step2 = (fun i j => raw22554step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22554step2 raw22554step1; decide +kernel
      have hl : raw22554step2Labels = raw22554step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22554step1 raw22554step1Labels permutation8 permutation6
    _ = mixedMoment B node1273 node1273Labels := by rfl

def raw22555 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22555Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22555step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22555step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22555step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22555step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22555 raw22555Labels = mixedMoment B node1274 node1274Labels := by
  calc
    mixedMoment B raw22555 raw22555Labels = mixedMoment B raw22555step0 raw22555step0Labels := by
      have hz : ∀ j, raw22555 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22555step0 = (fun i j => raw22555 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22555step0 raw22555; decide +kernel
      have hl : raw22555step0Labels = raw22555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22555 raw22555Labels permutation346 hz
    mixedMoment B raw22555step0 raw22555step0Labels = mixedMoment B raw22555step1 raw22555step1Labels := by
      have hz : ∀ j, raw22555step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22555step1 = (fun i j => raw22555step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22555step1 raw22555step0; decide +kernel
      have hl : raw22555step1Labels = raw22555step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22555step0 raw22555step0Labels permutation56 hz
    mixedMoment B raw22555step1 raw22555step1Labels = mixedMoment B raw22555step2 raw22555step2Labels := by
      have ha : raw22555step2 = (fun i j => raw22555step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22555step2 raw22555step1; decide +kernel
      have hl : raw22555step2Labels = raw22555step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22555step1 raw22555step1Labels permutation8 permutation6
    _ = mixedMoment B node1274 node1274Labels := by rfl

def raw22556 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22556Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22556step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22556step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22556step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, -1, 2], ![0, -2, 2]]
def raw22556step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22556step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22556step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22556 raw22556Labels = mixedMoment B node1095 node1095Labels := by
  calc
    mixedMoment B raw22556 raw22556Labels = mixedMoment B raw22556step0 raw22556step0Labels := by
      have hz : ∀ j, raw22556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22556step0 = (fun i j => raw22556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22556step0 raw22556; decide +kernel
      have hl : raw22556step0Labels = raw22556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22556 raw22556Labels permutation434 hz
    mixedMoment B raw22556step0 raw22556step0Labels = mixedMoment B raw22556step1 raw22556step1Labels := by
      have hz : ∀ j, raw22556step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22556step1 = (fun i j => raw22556step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22556step1 raw22556step0; decide +kernel
      have hl : raw22556step1Labels = raw22556step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22556step0 raw22556step0Labels permutation80 hz
    mixedMoment B raw22556step1 raw22556step1Labels = mixedMoment B raw22556step2 raw22556step2Labels := by
      have hz : ∀ j, raw22556step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22556step2 = (fun i j => raw22556step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22556step2 raw22556step1; decide +kernel
      have hl : raw22556step2Labels = raw22556step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22556step1 raw22556step1Labels permutation14 hz
    mixedMoment B raw22556step2 raw22556step2Labels = mixedMoment B raw22556step3 raw22556step3Labels := by
      have ha : raw22556step3 = (fun i j => raw22556step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22556step3 raw22556step2; decide +kernel
      have hl : raw22556step3Labels = raw22556step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22556step2 raw22556step2Labels permutation2 permutation6
    _ = mixedMoment B node1095 node1095Labels := by rfl

def raw22557 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22557Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22557step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22557step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22557 raw22557Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw22557 raw22557Labels = mixedMoment B raw22557step0 raw22557step0Labels := by
      have hz : ∀ j, raw22557 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22557step0 = (fun i j => raw22557 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22557step0 raw22557; decide +kernel
      have hl : raw22557step0Labels = raw22557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22557 raw22557Labels permutation434 hz
    mixedMoment B raw22557step0 raw22557step0Labels = mixedMoment B raw22557step1 raw22557step1Labels := by
      have hz : ∀ j, raw22557step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22557step1 = (fun i j => raw22557step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22557step1 raw22557step0; decide +kernel
      have hl : raw22557step1Labels = raw22557step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22557step0 raw22557step0Labels permutation80 hz
    mixedMoment B raw22557step1 raw22557step1Labels = mixedMoment B raw22557step2 raw22557step2Labels := by
      have ha : raw22557step2 = (fun i j => raw22557step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22557step2 raw22557step1; decide +kernel
      have hl : raw22557step2Labels = raw22557step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22557step1 raw22557step1Labels permutation8 permutation6
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw22558 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22558Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22558step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22558step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22558step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22558step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22558 raw22558Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw22558 raw22558Labels = mixedMoment B raw22558step0 raw22558step0Labels := by
      have hz : ∀ j, raw22558 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22558step0 = (fun i j => raw22558 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22558step0 raw22558; decide +kernel
      have hl : raw22558step0Labels = raw22558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22558 raw22558Labels permutation434 hz
    mixedMoment B raw22558step0 raw22558step0Labels = mixedMoment B raw22558step1 raw22558step1Labels := by
      have hz : ∀ j, raw22558step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22558step1 = (fun i j => raw22558step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22558step1 raw22558step0; decide +kernel
      have hl : raw22558step1Labels = raw22558step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22558step0 raw22558step0Labels permutation56 hz
    mixedMoment B raw22558step1 raw22558step1Labels = mixedMoment B raw22558step2 raw22558step2Labels := by
      have ha : raw22558step2 = (fun i j => raw22558step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22558step2 raw22558step1; decide +kernel
      have hl : raw22558step2Labels = raw22558step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22558step1 raw22558step1Labels permutation8 permutation6
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw22559 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22559Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22559step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22559step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22559step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22559 raw22559Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw22559 raw22559Labels = mixedMoment B raw22559step0 raw22559step0Labels := by
      have hz : ∀ j, raw22559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22559step0 = (fun i j => raw22559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22559step0 raw22559; decide +kernel
      have hl : raw22559step0Labels = raw22559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22559 raw22559Labels permutation346 hz
    mixedMoment B raw22559step0 raw22559step0Labels = mixedMoment B raw22559step1 raw22559step1Labels := by
      have hz : ∀ j, raw22559step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22559step1 = (fun i j => raw22559step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22559step1 raw22559step0; decide +kernel
      have hl : raw22559step1Labels = raw22559step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22559step0 raw22559step0Labels permutation56 hz
    mixedMoment B raw22559step1 raw22559step1Labels = mixedMoment B raw22559step2 raw22559step2Labels := by
      have ha : raw22559step2 = (fun i j => raw22559step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22559step2 raw22559step1; decide +kernel
      have hl : raw22559step2Labels = raw22559step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22559step1 raw22559step1Labels permutation8 permutation6
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw22560 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22560Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22560step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22560step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22560step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, -1, 2], ![-1, -1, 2]]
def raw22560step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22560step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw22560step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22560 raw22560Labels = mixedMoment B node1312 node1312Labels := by
  calc
    mixedMoment B raw22560 raw22560Labels = mixedMoment B raw22560step0 raw22560step0Labels := by
      have hz : ∀ j, raw22560 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22560step0 = (fun i j => raw22560 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22560step0 raw22560; decide +kernel
      have hl : raw22560step0Labels = raw22560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22560 raw22560Labels permutation434 hz
    mixedMoment B raw22560step0 raw22560step0Labels = mixedMoment B raw22560step1 raw22560step1Labels := by
      have hz : ∀ j, raw22560step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22560step1 = (fun i j => raw22560step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22560step1 raw22560step0; decide +kernel
      have hl : raw22560step1Labels = raw22560step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22560step0 raw22560step0Labels permutation80 hz
    mixedMoment B raw22560step1 raw22560step1Labels = mixedMoment B raw22560step2 raw22560step2Labels := by
      have hz : ∀ j, raw22560step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22560step2 = (fun i j => raw22560step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22560step2 raw22560step1; decide +kernel
      have hl : raw22560step2Labels = raw22560step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22560step1 raw22560step1Labels permutation14 hz
    mixedMoment B raw22560step2 raw22560step2Labels = mixedMoment B raw22560step3 raw22560step3Labels := by
      have ha : raw22560step3 = (fun i j => raw22560step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22560step3 raw22560step2; decide +kernel
      have hl : raw22560step3Labels = raw22560step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22560step2 raw22560step2Labels permutation2 permutation6
    _ = mixedMoment B node1312 node1312Labels := by rfl

def raw22561 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22561Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22561step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22561step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22561step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 0, 2], ![1, -3, 2]]
def raw22561step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22561step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw22561step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22561 raw22561Labels = mixedMoment B node1094 node1094Labels := by
  calc
    mixedMoment B raw22561 raw22561Labels = mixedMoment B raw22561step0 raw22561step0Labels := by
      have hz : ∀ j, raw22561 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22561step0 = (fun i j => raw22561 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22561step0 raw22561; decide +kernel
      have hl : raw22561step0Labels = raw22561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22561 raw22561Labels permutation434 hz
    mixedMoment B raw22561step0 raw22561step0Labels = mixedMoment B raw22561step1 raw22561step1Labels := by
      have hz : ∀ j, raw22561step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22561step1 = (fun i j => raw22561step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22561step1 raw22561step0; decide +kernel
      have hl : raw22561step1Labels = raw22561step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22561step0 raw22561step0Labels permutation80 hz
    mixedMoment B raw22561step1 raw22561step1Labels = mixedMoment B raw22561step2 raw22561step2Labels := by
      have hz : ∀ j, raw22561step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22561step2 = (fun i j => raw22561step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22561step2 raw22561step1; decide +kernel
      have hl : raw22561step2Labels = raw22561step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22561step1 raw22561step1Labels permutation14 hz
    mixedMoment B raw22561step2 raw22561step2Labels = mixedMoment B raw22561step3 raw22561step3Labels := by
      have ha : raw22561step3 = (fun i j => raw22561step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22561step3 raw22561step2; decide +kernel
      have hl : raw22561step3Labels = raw22561step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22561step2 raw22561step2Labels permutation2 permutation6
    _ = mixedMoment B node1094 node1094Labels := by rfl

def raw22562 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22562Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22562step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22562step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22562step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22562 raw22562Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw22562 raw22562Labels = mixedMoment B raw22562step0 raw22562step0Labels := by
      have hz : ∀ j, raw22562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22562step0 = (fun i j => raw22562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22562step0 raw22562; decide +kernel
      have hl : raw22562step0Labels = raw22562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22562 raw22562Labels permutation434 hz
    mixedMoment B raw22562step0 raw22562step0Labels = mixedMoment B raw22562step1 raw22562step1Labels := by
      have hz : ∀ j, raw22562step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22562step1 = (fun i j => raw22562step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22562step1 raw22562step0; decide +kernel
      have hl : raw22562step1Labels = raw22562step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22562step0 raw22562step0Labels permutation80 hz
    mixedMoment B raw22562step1 raw22562step1Labels = mixedMoment B raw22562step2 raw22562step2Labels := by
      have ha : raw22562step2 = (fun i j => raw22562step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22562step2 raw22562step1; decide +kernel
      have hl : raw22562step2Labels = raw22562step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22562step1 raw22562step1Labels permutation8 permutation6
    _ = mixedMoment B node1245 node1245Labels := by rfl

def raw22563 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22563Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22563step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22563step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22563step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22563step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22563 raw22563Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw22563 raw22563Labels = mixedMoment B raw22563step0 raw22563step0Labels := by
      have hz : ∀ j, raw22563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22563step0 = (fun i j => raw22563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22563step0 raw22563; decide +kernel
      have hl : raw22563step0Labels = raw22563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22563 raw22563Labels permutation434 hz
    mixedMoment B raw22563step0 raw22563step0Labels = mixedMoment B raw22563step1 raw22563step1Labels := by
      have hz : ∀ j, raw22563step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22563step1 = (fun i j => raw22563step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22563step1 raw22563step0; decide +kernel
      have hl : raw22563step1Labels = raw22563step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22563step0 raw22563step0Labels permutation56 hz
    mixedMoment B raw22563step1 raw22563step1Labels = mixedMoment B raw22563step2 raw22563step2Labels := by
      have ha : raw22563step2 = (fun i j => raw22563step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22563step2 raw22563step1; decide +kernel
      have hl : raw22563step2Labels = raw22563step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22563step1 raw22563step1Labels permutation8 permutation6
    _ = mixedMoment B node1245 node1245Labels := by rfl

def raw22564 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22564Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22564step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22564step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22564step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22564 raw22564Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw22564 raw22564Labels = mixedMoment B raw22564step0 raw22564step0Labels := by
      have hz : ∀ j, raw22564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22564step0 = (fun i j => raw22564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22564step0 raw22564; decide +kernel
      have hl : raw22564step0Labels = raw22564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22564 raw22564Labels permutation346 hz
    mixedMoment B raw22564step0 raw22564step0Labels = mixedMoment B raw22564step1 raw22564step1Labels := by
      have hz : ∀ j, raw22564step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22564step1 = (fun i j => raw22564step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22564step1 raw22564step0; decide +kernel
      have hl : raw22564step1Labels = raw22564step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22564step0 raw22564step0Labels permutation56 hz
    mixedMoment B raw22564step1 raw22564step1Labels = mixedMoment B raw22564step2 raw22564step2Labels := by
      have ha : raw22564step2 = (fun i j => raw22564step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22564step2 raw22564step1; decide +kernel
      have hl : raw22564step2Labels = raw22564step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22564step1 raw22564step1Labels permutation8 permutation6
    _ = mixedMoment B node1245 node1245Labels := by rfl

def raw22565 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22565Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22565step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22565step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22565step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-3, 1, 2], ![1, -3, 2]]
def raw22565step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22565step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw22565step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22565 raw22565Labels = mixedMoment B node1310 node1310Labels := by
  calc
    mixedMoment B raw22565 raw22565Labels = mixedMoment B raw22565step0 raw22565step0Labels := by
      have hz : ∀ j, raw22565 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22565step0 = (fun i j => raw22565 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22565step0 raw22565; decide +kernel
      have hl : raw22565step0Labels = raw22565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22565 raw22565Labels permutation434 hz
    mixedMoment B raw22565step0 raw22565step0Labels = mixedMoment B raw22565step1 raw22565step1Labels := by
      have hz : ∀ j, raw22565step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22565step1 = (fun i j => raw22565step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22565step1 raw22565step0; decide +kernel
      have hl : raw22565step1Labels = raw22565step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22565step0 raw22565step0Labels permutation80 hz
    mixedMoment B raw22565step1 raw22565step1Labels = mixedMoment B raw22565step2 raw22565step2Labels := by
      have hz : ∀ j, raw22565step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22565step2 = (fun i j => raw22565step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22565step2 raw22565step1; decide +kernel
      have hl : raw22565step2Labels = raw22565step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22565step1 raw22565step1Labels permutation14 hz
    mixedMoment B raw22565step2 raw22565step2Labels = mixedMoment B raw22565step3 raw22565step3Labels := by
      have ha : raw22565step3 = (fun i j => raw22565step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22565step3 raw22565step2; decide +kernel
      have hl : raw22565step3Labels = raw22565step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22565step2 raw22565step2Labels permutation2 permutation6
    _ = mixedMoment B node1310 node1310Labels := by rfl

def raw22566 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22566step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22566step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, -1, 2], ![0, -2, 2]]
def raw22566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22566step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -1, 2], ![-2, 0, 2]]
def raw22566step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22566step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw22566step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22566 raw22566Labels = mixedMoment B node1755 node1755Labels := by
  calc
    mixedMoment B raw22566 raw22566Labels = mixedMoment B raw22566step0 raw22566step0Labels := by
      have hz : ∀ j, raw22566 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22566step0 = (fun i j => raw22566 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22566step0 raw22566; decide +kernel
      have hl : raw22566step0Labels = raw22566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22566 raw22566Labels permutation434 hz
    mixedMoment B raw22566step0 raw22566step0Labels = mixedMoment B raw22566step1 raw22566step1Labels := by
      have hz : ∀ j, raw22566step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22566step1 = (fun i j => raw22566step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22566step1 raw22566step0; decide +kernel
      have hl : raw22566step1Labels = raw22566step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22566step0 raw22566step0Labels permutation80 hz
    mixedMoment B raw22566step1 raw22566step1Labels = mixedMoment B raw22566step2 raw22566step2Labels := by
      have hz : ∀ j, raw22566step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22566step2 = (fun i j => raw22566step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22566step2 raw22566step1; decide +kernel
      have hl : raw22566step2Labels = raw22566step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22566step1 raw22566step1Labels permutation14 hz
    mixedMoment B raw22566step2 raw22566step2Labels = mixedMoment B raw22566step3 raw22566step3Labels := by
      have ha : raw22566step3 = (fun i j => raw22566step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22566step3 raw22566step2; decide +kernel
      have hl : raw22566step3Labels = raw22566step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22566step2 raw22566step2Labels permutation2 permutation4
    mixedMoment B raw22566step3 raw22566step3Labels = mixedMoment B raw22566step4 raw22566step4Labels := by
      have ha : raw22566step4 = -raw22566step3 := by apply Matrix.ext; change ∀ i j, raw22566step4 i j = -(raw22566step3 i j); unfold raw22566step4 raw22566step3; decide +kernel
      have hl : raw22566step4Labels = raw22566step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1755 node1755Labels := by rfl

def raw22567 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22567step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22567step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22567step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22567 raw22567Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw22567 raw22567Labels = mixedMoment B raw22567step0 raw22567step0Labels := by
      have hz : ∀ j, raw22567 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22567step0 = (fun i j => raw22567 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22567step0 raw22567; decide +kernel
      have hl : raw22567step0Labels = raw22567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22567 raw22567Labels permutation434 hz
    mixedMoment B raw22567step0 raw22567step0Labels = mixedMoment B raw22567step1 raw22567step1Labels := by
      have hz : ∀ j, raw22567step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22567step1 = (fun i j => raw22567step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22567step1 raw22567step0; decide +kernel
      have hl : raw22567step1Labels = raw22567step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22567step0 raw22567step0Labels permutation56 hz
    mixedMoment B raw22567step1 raw22567step1Labels = mixedMoment B raw22567step2 raw22567step2Labels := by
      have ha : raw22567step2 = (fun i j => raw22567step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22567step2 raw22567step1; decide +kernel
      have hl : raw22567step2Labels = raw22567step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22567step1 raw22567step1Labels permutation8 permutation4
    mixedMoment B raw22567step2 raw22567step2Labels = mixedMoment B raw22567step3 raw22567step3Labels := by
      have ha : raw22567step3 = -raw22567step2 := by apply Matrix.ext; change ∀ i j, raw22567step3 i j = -(raw22567step2 i j); unfold raw22567step3 raw22567step2; decide +kernel
      have hl : raw22567step3Labels = raw22567step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3301 node3301Labels := by rfl

def raw22568 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22568Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22568step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22568step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22568step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22568step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22568 raw22568Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw22568 raw22568Labels = mixedMoment B raw22568step0 raw22568step0Labels := by
      have hz : ∀ j, raw22568 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22568step0 = (fun i j => raw22568 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22568step0 raw22568; decide +kernel
      have hl : raw22568step0Labels = raw22568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22568 raw22568Labels permutation346 hz
    mixedMoment B raw22568step0 raw22568step0Labels = mixedMoment B raw22568step1 raw22568step1Labels := by
      have hz : ∀ j, raw22568step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22568step1 = (fun i j => raw22568step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22568step1 raw22568step0; decide +kernel
      have hl : raw22568step1Labels = raw22568step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22568step0 raw22568step0Labels permutation56 hz
    mixedMoment B raw22568step1 raw22568step1Labels = mixedMoment B raw22568step2 raw22568step2Labels := by
      have ha : raw22568step2 = (fun i j => raw22568step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22568step2 raw22568step1; decide +kernel
      have hl : raw22568step2Labels = raw22568step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22568step1 raw22568step1Labels permutation8 permutation4
    mixedMoment B raw22568step2 raw22568step2Labels = mixedMoment B raw22568step3 raw22568step3Labels := by
      have ha : raw22568step3 = -raw22568step2 := by apply Matrix.ext; change ∀ i j, raw22568step3 i j = -(raw22568step2 i j); unfold raw22568step3 raw22568step2; decide +kernel
      have hl : raw22568step3Labels = raw22568step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3301 node3301Labels := by rfl

def raw22569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22569step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22569step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22569step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22569step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22569step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22569 raw22569Labels = mixedMoment B node4186 node4186Labels := by
  calc
    mixedMoment B raw22569 raw22569Labels = mixedMoment B raw22569step0 raw22569step0Labels := by
      have hz : ∀ j, raw22569 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22569step0 = (fun i j => raw22569 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22569step0 raw22569; decide +kernel
      have hl : raw22569step0Labels = raw22569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22569 raw22569Labels permutation434 hz
    mixedMoment B raw22569step0 raw22569step0Labels = mixedMoment B raw22569step1 raw22569step1Labels := by
      have hz : ∀ j, raw22569step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22569step1 = (fun i j => raw22569step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22569step1 raw22569step0; decide +kernel
      have hl : raw22569step1Labels = raw22569step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22569step0 raw22569step0Labels permutation80 hz
    mixedMoment B raw22569step1 raw22569step1Labels = mixedMoment B raw22569step2 raw22569step2Labels := by
      have ha : raw22569step2 = (fun i j => raw22569step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22569step2 raw22569step1; decide +kernel
      have hl : raw22569step2Labels = raw22569step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22569step1 raw22569step1Labels permutation8 permutation3
    mixedMoment B raw22569step2 raw22569step2Labels = mixedMoment B raw22569step3 raw22569step3Labels := by
      have ha : raw22569step3 = raw22569step2 := by apply Matrix.ext; unfold raw22569step3 raw22569step2; decide +kernel
      have hl : raw22569step2Labels = labelEmbedding6 ∘ raw22569step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22569step2 raw22569step2Labels raw22569step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4186 node4186Labels := by rfl

def raw22570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22570step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22570step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22570step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22570 raw22570Labels = mixedMoment B node4554 node4554Labels := by
  calc
    mixedMoment B raw22570 raw22570Labels = mixedMoment B raw22570step0 raw22570step0Labels := by
      have hz : ∀ j, raw22570 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22570step0 = (fun i j => raw22570 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22570step0 raw22570; decide +kernel
      have hl : raw22570step0Labels = raw22570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22570 raw22570Labels permutation434 hz
    mixedMoment B raw22570step0 raw22570step0Labels = mixedMoment B raw22570step1 raw22570step1Labels := by
      have ha : raw22570step1 = (fun i j => raw22570step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22570step1 raw22570step0; decide +kernel
      have hl : raw22570step1Labels = raw22570step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22570step0 raw22570step0Labels permutation38 permutation3
    mixedMoment B raw22570step1 raw22570step1Labels = mixedMoment B raw22570step2 raw22570step2Labels := by
      have ha : raw22570step2 = raw22570step1 := by apply Matrix.ext; unfold raw22570step2 raw22570step1; decide +kernel
      have hl : raw22570step1Labels = labelEmbedding6 ∘ raw22570step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22570step1 raw22570step1Labels raw22570step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4554 node4554Labels := by rfl

def raw22571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22571step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22571step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22571step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22571 raw22571Labels = mixedMoment B node4554 node4554Labels := by
  calc
    mixedMoment B raw22571 raw22571Labels = mixedMoment B raw22571step0 raw22571step0Labels := by
      have hz : ∀ j, raw22571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22571step0 = (fun i j => raw22571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22571step0 raw22571; decide +kernel
      have hl : raw22571step0Labels = raw22571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22571 raw22571Labels permutation346 hz
    mixedMoment B raw22571step0 raw22571step0Labels = mixedMoment B raw22571step1 raw22571step1Labels := by
      have ha : raw22571step1 = (fun i j => raw22571step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22571step1 raw22571step0; decide +kernel
      have hl : raw22571step1Labels = raw22571step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22571step0 raw22571step0Labels permutation38 permutation3
    mixedMoment B raw22571step1 raw22571step1Labels = mixedMoment B raw22571step2 raw22571step2Labels := by
      have ha : raw22571step2 = raw22571step1 := by apply Matrix.ext; unfold raw22571step2 raw22571step1; decide +kernel
      have hl : raw22571step1Labels = labelEmbedding6 ∘ raw22571step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22571step1 raw22571step1Labels raw22571step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4554 node4554Labels := by rfl

def raw22572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22572step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22572step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22572 raw22572Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw22572 raw22572Labels = mixedMoment B raw22572step0 raw22572step0Labels := by
      have hz : ∀ j, raw22572 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22572step0 = (fun i j => raw22572 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22572step0 raw22572; decide +kernel
      have hl : raw22572step0Labels = raw22572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22572 raw22572Labels permutation434 hz
    mixedMoment B raw22572step0 raw22572step0Labels = mixedMoment B raw22572step1 raw22572step1Labels := by
      have hz : ∀ j, raw22572step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22572step1 = (fun i j => raw22572step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22572step1 raw22572step0; decide +kernel
      have hl : raw22572step1Labels = raw22572step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22572step0 raw22572step0Labels permutation80 hz
    mixedMoment B raw22572step1 raw22572step1Labels = mixedMoment B raw22572step2 raw22572step2Labels := by
      have ha : raw22572step2 = (fun i j => raw22572step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22572step2 raw22572step1; decide +kernel
      have hl : raw22572step2Labels = raw22572step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22572step1 raw22572step1Labels permutation9 permutation2
    _ = mixedMoment B node4624 node4624Labels := by rfl

def raw22573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22573step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22573step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22573step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22573 raw22573Labels = mixedMoment B node4186 node4186Labels := by
  calc
    mixedMoment B raw22573 raw22573Labels = mixedMoment B raw22573step0 raw22573step0Labels := by
      have hz : ∀ j, raw22573 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22573step0 = (fun i j => raw22573 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22573step0 raw22573; decide +kernel
      have hl : raw22573step0Labels = raw22573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22573 raw22573Labels permutation434 hz
    mixedMoment B raw22573step0 raw22573step0Labels = mixedMoment B raw22573step1 raw22573step1Labels := by
      have hz : ∀ j, raw22573step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22573step1 = (fun i j => raw22573step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22573step1 raw22573step0; decide +kernel
      have hl : raw22573step1Labels = raw22573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22573step0 raw22573step0Labels permutation56 hz
    mixedMoment B raw22573step1 raw22573step1Labels = mixedMoment B raw22573step2 raw22573step2Labels := by
      have ha : raw22573step2 = (fun i j => raw22573step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22573step2 raw22573step1; decide +kernel
      have hl : raw22573step2Labels = raw22573step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22573step1 raw22573step1Labels permutation8 permutation3
    mixedMoment B raw22573step2 raw22573step2Labels = mixedMoment B raw22573step3 raw22573step3Labels := by
      have ha : raw22573step3 = raw22573step2 := by apply Matrix.ext; unfold raw22573step3 raw22573step2; decide +kernel
      have hl : raw22573step2Labels = labelEmbedding6 ∘ raw22573step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22573step2 raw22573step2Labels raw22573step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4186 node4186Labels := by rfl

def raw22574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22574step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22574 raw22574Labels = mixedMoment B node4554 node4554Labels := by
  calc
    mixedMoment B raw22574 raw22574Labels = mixedMoment B raw22574step0 raw22574step0Labels := by
      have hz : ∀ j, raw22574 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22574step0 = (fun i j => raw22574 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22574step0 raw22574; decide +kernel
      have hl : raw22574step0Labels = raw22574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22574 raw22574Labels permutation434 hz
    mixedMoment B raw22574step0 raw22574step0Labels = mixedMoment B raw22574step1 raw22574step1Labels := by
      have ha : raw22574step1 = (fun i j => raw22574step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22574step1 raw22574step0; decide +kernel
      have hl : raw22574step1Labels = raw22574step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22574step0 raw22574step0Labels permutation32 permutation3
    mixedMoment B raw22574step1 raw22574step1Labels = mixedMoment B raw22574step2 raw22574step2Labels := by
      have ha : raw22574step2 = raw22574step1 := by apply Matrix.ext; unfold raw22574step2 raw22574step1; decide +kernel
      have hl : raw22574step1Labels = labelEmbedding6 ∘ raw22574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22574step1 raw22574step1Labels raw22574step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4554 node4554Labels := by rfl

def raw22575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22575step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22575step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22575step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22575step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22575 raw22575Labels = mixedMoment B node4554 node4554Labels := by
  calc
    mixedMoment B raw22575 raw22575Labels = mixedMoment B raw22575step0 raw22575step0Labels := by
      have hz : ∀ j, raw22575 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22575step0 = (fun i j => raw22575 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22575step0 raw22575; decide +kernel
      have hl : raw22575step0Labels = raw22575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22575 raw22575Labels permutation265 hz
    mixedMoment B raw22575step0 raw22575step0Labels = mixedMoment B raw22575step1 raw22575step1Labels := by
      have ha : raw22575step1 = (fun i j => raw22575step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22575step1 raw22575step0; decide +kernel
      have hl : raw22575step1Labels = raw22575step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22575step0 raw22575step0Labels permutation38 permutation3
    mixedMoment B raw22575step1 raw22575step1Labels = mixedMoment B raw22575step2 raw22575step2Labels := by
      have ha : raw22575step2 = raw22575step1 := by apply Matrix.ext; unfold raw22575step2 raw22575step1; decide +kernel
      have hl : raw22575step1Labels = labelEmbedding6 ∘ raw22575step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22575step1 raw22575step1Labels raw22575step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4554 node4554Labels := by rfl

def raw22576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22576step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22576step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22576step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22576step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22576step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22576 raw22576Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw22576 raw22576Labels = mixedMoment B raw22576step0 raw22576step0Labels := by
      have hz : ∀ j, raw22576 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22576step0 = (fun i j => raw22576 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22576step0 raw22576; decide +kernel
      have hl : raw22576step0Labels = raw22576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22576 raw22576Labels permutation434 hz
    mixedMoment B raw22576step0 raw22576step0Labels = mixedMoment B raw22576step1 raw22576step1Labels := by
      have hz : ∀ j, raw22576step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22576step1 = (fun i j => raw22576step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22576step1 raw22576step0; decide +kernel
      have hl : raw22576step1Labels = raw22576step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22576step0 raw22576step0Labels permutation56 hz
    mixedMoment B raw22576step1 raw22576step1Labels = mixedMoment B raw22576step2 raw22576step2Labels := by
      have ha : raw22576step2 = (fun i j => raw22576step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22576step2 raw22576step1; decide +kernel
      have hl : raw22576step2Labels = raw22576step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22576step1 raw22576step1Labels permutation9 permutation2
    _ = mixedMoment B node4624 node4624Labels := by rfl

def raw22577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22577step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22577step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22577step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22577step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22577step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22577step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22577 raw22577Labels = mixedMoment B node4186 node4186Labels := by
  calc
    mixedMoment B raw22577 raw22577Labels = mixedMoment B raw22577step0 raw22577step0Labels := by
      have hz : ∀ j, raw22577 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22577step0 = (fun i j => raw22577 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22577step0 raw22577; decide +kernel
      have hl : raw22577step0Labels = raw22577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22577 raw22577Labels permutation346 hz
    mixedMoment B raw22577step0 raw22577step0Labels = mixedMoment B raw22577step1 raw22577step1Labels := by
      have hz : ∀ j, raw22577step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22577step1 = (fun i j => raw22577step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22577step1 raw22577step0; decide +kernel
      have hl : raw22577step1Labels = raw22577step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22577step0 raw22577step0Labels permutation56 hz
    mixedMoment B raw22577step1 raw22577step1Labels = mixedMoment B raw22577step2 raw22577step2Labels := by
      have ha : raw22577step2 = (fun i j => raw22577step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22577step2 raw22577step1; decide +kernel
      have hl : raw22577step2Labels = raw22577step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22577step1 raw22577step1Labels permutation8 permutation3
    mixedMoment B raw22577step2 raw22577step2Labels = mixedMoment B raw22577step3 raw22577step3Labels := by
      have ha : raw22577step3 = raw22577step2 := by apply Matrix.ext; unfold raw22577step3 raw22577step2; decide +kernel
      have hl : raw22577step2Labels = labelEmbedding6 ∘ raw22577step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22577step2 raw22577step2Labels raw22577step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4186 node4186Labels := by rfl

def raw22578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22578step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22578step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22578step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22578step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22578 raw22578Labels = mixedMoment B node4554 node4554Labels := by
  calc
    mixedMoment B raw22578 raw22578Labels = mixedMoment B raw22578step0 raw22578step0Labels := by
      have hz : ∀ j, raw22578 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22578step0 = (fun i j => raw22578 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22578step0 raw22578; decide +kernel
      have hl : raw22578step0Labels = raw22578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22578 raw22578Labels permutation346 hz
    mixedMoment B raw22578step0 raw22578step0Labels = mixedMoment B raw22578step1 raw22578step1Labels := by
      have ha : raw22578step1 = (fun i j => raw22578step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22578step1 raw22578step0; decide +kernel
      have hl : raw22578step1Labels = raw22578step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22578step0 raw22578step0Labels permutation32 permutation3
    mixedMoment B raw22578step1 raw22578step1Labels = mixedMoment B raw22578step2 raw22578step2Labels := by
      have ha : raw22578step2 = raw22578step1 := by apply Matrix.ext; unfold raw22578step2 raw22578step1; decide +kernel
      have hl : raw22578step1Labels = labelEmbedding6 ∘ raw22578step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22578step1 raw22578step1Labels raw22578step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4554 node4554Labels := by rfl

def raw22579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22579step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22579step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22579step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22579step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22579step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22579 raw22579Labels = mixedMoment B node4554 node4554Labels := by
  calc
    mixedMoment B raw22579 raw22579Labels = mixedMoment B raw22579step0 raw22579step0Labels := by
      have hz : ∀ j, raw22579 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22579step0 = (fun i j => raw22579 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22579step0 raw22579; decide +kernel
      have hl : raw22579step0Labels = raw22579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22579 raw22579Labels permutation265 hz
    mixedMoment B raw22579step0 raw22579step0Labels = mixedMoment B raw22579step1 raw22579step1Labels := by
      have ha : raw22579step1 = (fun i j => raw22579step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22579step1 raw22579step0; decide +kernel
      have hl : raw22579step1Labels = raw22579step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22579step0 raw22579step0Labels permutation32 permutation3
    mixedMoment B raw22579step1 raw22579step1Labels = mixedMoment B raw22579step2 raw22579step2Labels := by
      have ha : raw22579step2 = raw22579step1 := by apply Matrix.ext; unfold raw22579step2 raw22579step1; decide +kernel
      have hl : raw22579step1Labels = labelEmbedding6 ∘ raw22579step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22579step1 raw22579step1Labels raw22579step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4554 node4554Labels := by rfl

def raw22580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22580step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22580step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22580step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22580 raw22580Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw22580 raw22580Labels = mixedMoment B raw22580step0 raw22580step0Labels := by
      have hz : ∀ j, raw22580 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22580step0 = (fun i j => raw22580 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22580step0 raw22580; decide +kernel
      have hl : raw22580step0Labels = raw22580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22580 raw22580Labels permutation346 hz
    mixedMoment B raw22580step0 raw22580step0Labels = mixedMoment B raw22580step1 raw22580step1Labels := by
      have hz : ∀ j, raw22580step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22580step1 = (fun i j => raw22580step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22580step1 raw22580step0; decide +kernel
      have hl : raw22580step1Labels = raw22580step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22580step0 raw22580step0Labels permutation56 hz
    mixedMoment B raw22580step1 raw22580step1Labels = mixedMoment B raw22580step2 raw22580step2Labels := by
      have ha : raw22580step2 = (fun i j => raw22580step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22580step2 raw22580step1; decide +kernel
      have hl : raw22580step2Labels = raw22580step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22580step1 raw22580step1Labels permutation9 permutation2
    _ = mixedMoment B node4624 node4624Labels := by rfl

def raw22581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22581step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![3, -2, -1], ![2, -1, -1]]
def raw22581step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22581step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw22581step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22581step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw22581step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22581 raw22581Labels = mixedMoment B node4191 node4191Labels := by
  calc
    mixedMoment B raw22581 raw22581Labels = mixedMoment B raw22581step0 raw22581step0Labels := by
      have hz : ∀ j, raw22581 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22581step0 = (fun i j => raw22581 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22581step0 raw22581; decide +kernel
      have hl : raw22581step0Labels = raw22581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22581 raw22581Labels permutation434 hz
    mixedMoment B raw22581step0 raw22581step0Labels = mixedMoment B raw22581step1 raw22581step1Labels := by
      have hz : ∀ j, raw22581step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22581step1 = (fun i j => raw22581step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22581step1 raw22581step0; decide +kernel
      have hl : raw22581step1Labels = raw22581step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22581step0 raw22581step0Labels permutation80 hz
    mixedMoment B raw22581step1 raw22581step1Labels = mixedMoment B raw22581step2 raw22581step2Labels := by
      have hz : ∀ j, raw22581step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22581step2 = (fun i j => raw22581step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22581step2 raw22581step1; decide +kernel
      have hl : raw22581step2Labels = raw22581step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22581step1 raw22581step1Labels permutation14 hz
    mixedMoment B raw22581step2 raw22581step2Labels = mixedMoment B raw22581step3 raw22581step3Labels := by
      have ha : raw22581step3 = (fun i j => raw22581step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22581step3 raw22581step2; decide +kernel
      have hl : raw22581step3Labels = raw22581step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22581step2 raw22581step2Labels permutation3 permutation3
    mixedMoment B raw22581step3 raw22581step3Labels = mixedMoment B raw22581step4 raw22581step4Labels := by
      have ha : raw22581step4 = raw22581step3 := by apply Matrix.ext; unfold raw22581step4 raw22581step3; decide +kernel
      have hl : raw22581step3Labels = labelEmbedding6 ∘ raw22581step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22581step3 raw22581step3Labels raw22581step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4191 node4191Labels := by rfl

def raw22582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22582step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22582step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22582step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22582step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22582step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22582step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22582 raw22582Labels = mixedMoment B node4558 node4558Labels := by
  calc
    mixedMoment B raw22582 raw22582Labels = mixedMoment B raw22582step0 raw22582step0Labels := by
      have hz : ∀ j, raw22582 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22582step0 = (fun i j => raw22582 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22582step0 raw22582; decide +kernel
      have hl : raw22582step0Labels = raw22582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22582 raw22582Labels permutation434 hz
    mixedMoment B raw22582step0 raw22582step0Labels = mixedMoment B raw22582step1 raw22582step1Labels := by
      have hz : ∀ j, raw22582step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22582step1 = (fun i j => raw22582step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22582step1 raw22582step0; decide +kernel
      have hl : raw22582step1Labels = raw22582step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22582step0 raw22582step0Labels permutation80 hz
    mixedMoment B raw22582step1 raw22582step1Labels = mixedMoment B raw22582step2 raw22582step2Labels := by
      have ha : raw22582step2 = (fun i j => raw22582step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22582step2 raw22582step1; decide +kernel
      have hl : raw22582step2Labels = raw22582step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22582step1 raw22582step1Labels permutation9 permutation3
    mixedMoment B raw22582step2 raw22582step2Labels = mixedMoment B raw22582step3 raw22582step3Labels := by
      have ha : raw22582step3 = raw22582step2 := by apply Matrix.ext; unfold raw22582step3 raw22582step2; decide +kernel
      have hl : raw22582step2Labels = labelEmbedding6 ∘ raw22582step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22582step2 raw22582step2Labels raw22582step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4558 node4558Labels := by rfl

def raw22583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22583step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22583step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22583step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22583 raw22583Labels = mixedMoment B node4558 node4558Labels := by
  calc
    mixedMoment B raw22583 raw22583Labels = mixedMoment B raw22583step0 raw22583step0Labels := by
      have hz : ∀ j, raw22583 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22583step0 = (fun i j => raw22583 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22583step0 raw22583; decide +kernel
      have hl : raw22583step0Labels = raw22583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22583 raw22583Labels permutation434 hz
    mixedMoment B raw22583step0 raw22583step0Labels = mixedMoment B raw22583step1 raw22583step1Labels := by
      have hz : ∀ j, raw22583step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22583step1 = (fun i j => raw22583step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22583step1 raw22583step0; decide +kernel
      have hl : raw22583step1Labels = raw22583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22583step0 raw22583step0Labels permutation56 hz
    mixedMoment B raw22583step1 raw22583step1Labels = mixedMoment B raw22583step2 raw22583step2Labels := by
      have ha : raw22583step2 = (fun i j => raw22583step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22583step2 raw22583step1; decide +kernel
      have hl : raw22583step2Labels = raw22583step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22583step1 raw22583step1Labels permutation9 permutation3
    mixedMoment B raw22583step2 raw22583step2Labels = mixedMoment B raw22583step3 raw22583step3Labels := by
      have ha : raw22583step3 = raw22583step2 := by apply Matrix.ext; unfold raw22583step3 raw22583step2; decide +kernel
      have hl : raw22583step2Labels = labelEmbedding6 ∘ raw22583step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22583step2 raw22583step2Labels raw22583step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4558 node4558Labels := by rfl

def raw22584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22584step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22584step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22584step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22584step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22584step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22584 raw22584Labels = mixedMoment B node4558 node4558Labels := by
  calc
    mixedMoment B raw22584 raw22584Labels = mixedMoment B raw22584step0 raw22584step0Labels := by
      have hz : ∀ j, raw22584 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22584step0 = (fun i j => raw22584 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22584step0 raw22584; decide +kernel
      have hl : raw22584step0Labels = raw22584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22584 raw22584Labels permutation346 hz
    mixedMoment B raw22584step0 raw22584step0Labels = mixedMoment B raw22584step1 raw22584step1Labels := by
      have hz : ∀ j, raw22584step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22584step1 = (fun i j => raw22584step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22584step1 raw22584step0; decide +kernel
      have hl : raw22584step1Labels = raw22584step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22584step0 raw22584step0Labels permutation56 hz
    mixedMoment B raw22584step1 raw22584step1Labels = mixedMoment B raw22584step2 raw22584step2Labels := by
      have ha : raw22584step2 = (fun i j => raw22584step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22584step2 raw22584step1; decide +kernel
      have hl : raw22584step2Labels = raw22584step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22584step1 raw22584step1Labels permutation9 permutation3
    mixedMoment B raw22584step2 raw22584step2Labels = mixedMoment B raw22584step3 raw22584step3Labels := by
      have ha : raw22584step3 = raw22584step2 := by apply Matrix.ext; unfold raw22584step3 raw22584step2; decide +kernel
      have hl : raw22584step2Labels = labelEmbedding6 ∘ raw22584step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22584step2 raw22584step2Labels raw22584step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4558 node4558Labels := by rfl

def raw22585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw22585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw22585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw22585step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22585step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![3, -2, -1], ![1, 0, -1]]
def raw22585step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22585step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw22585step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22585step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw22585step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22585 raw22585Labels = mixedMoment B node4625 node4625Labels := by
  calc
    mixedMoment B raw22585 raw22585Labels = mixedMoment B raw22585step0 raw22585step0Labels := by
      have hz : ∀ j, raw22585 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22585step0 = (fun i j => raw22585 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22585step0 raw22585; decide +kernel
      have hl : raw22585step0Labels = raw22585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22585 raw22585Labels permutation434 hz
    mixedMoment B raw22585step0 raw22585step0Labels = mixedMoment B raw22585step1 raw22585step1Labels := by
      have hz : ∀ j, raw22585step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22585step1 = (fun i j => raw22585step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22585step1 raw22585step0; decide +kernel
      have hl : raw22585step1Labels = raw22585step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22585step0 raw22585step0Labels permutation80 hz
    mixedMoment B raw22585step1 raw22585step1Labels = mixedMoment B raw22585step2 raw22585step2Labels := by
      have hz : ∀ j, raw22585step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22585step2 = (fun i j => raw22585step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22585step2 raw22585step1; decide +kernel
      have hl : raw22585step2Labels = raw22585step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22585step1 raw22585step1Labels permutation14 hz
    mixedMoment B raw22585step2 raw22585step2Labels = mixedMoment B raw22585step3 raw22585step3Labels := by
      have ha : raw22585step3 = (fun i j => raw22585step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22585step3 raw22585step2; decide +kernel
      have hl : raw22585step3Labels = raw22585step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22585step2 raw22585step2Labels permutation3 permutation3
    mixedMoment B raw22585step3 raw22585step3Labels = mixedMoment B raw22585step4 raw22585step4Labels := by
      have ha : raw22585step4 = raw22585step3 := by apply Matrix.ext; unfold raw22585step4 raw22585step3; decide +kernel
      have hl : raw22585step3Labels = labelEmbedding6 ∘ raw22585step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22585step3 raw22585step3Labels raw22585step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4625 node4625Labels := by rfl

def raw22586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22586step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22586 raw22586Labels = mixedMoment B node2969 node2969Labels := by
  calc
    mixedMoment B raw22586 raw22586Labels = mixedMoment B raw22586step0 raw22586step0Labels := by
      have hz : ∀ j, raw22586 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22586step0 = (fun i j => raw22586 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22586step0 raw22586; decide +kernel
      have hl : raw22586step0Labels = raw22586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22586 raw22586Labels permutation434 hz
    mixedMoment B raw22586step0 raw22586step0Labels = mixedMoment B raw22586step1 raw22586step1Labels := by
      have hz : ∀ j, raw22586step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22586step1 = (fun i j => raw22586step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22586step1 raw22586step0; decide +kernel
      have hl : raw22586step1Labels = raw22586step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22586step0 raw22586step0Labels permutation80 hz
    mixedMoment B raw22586step1 raw22586step1Labels = mixedMoment B raw22586step2 raw22586step2Labels := by
      have ha : raw22586step2 = (fun i j => raw22586step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22586step2 raw22586step1; decide +kernel
      have hl : raw22586step2Labels = raw22586step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22586step1 raw22586step1Labels permutation8 permutation3
    _ = mixedMoment B node2969 node2969Labels := by rfl

def raw22587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22587step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22587step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22587step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22587 raw22587Labels = mixedMoment B node2969 node2969Labels := by
  calc
    mixedMoment B raw22587 raw22587Labels = mixedMoment B raw22587step0 raw22587step0Labels := by
      have hz : ∀ j, raw22587 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22587step0 = (fun i j => raw22587 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22587step0 raw22587; decide +kernel
      have hl : raw22587step0Labels = raw22587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22587 raw22587Labels permutation434 hz
    mixedMoment B raw22587step0 raw22587step0Labels = mixedMoment B raw22587step1 raw22587step1Labels := by
      have hz : ∀ j, raw22587step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22587step1 = (fun i j => raw22587step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22587step1 raw22587step0; decide +kernel
      have hl : raw22587step1Labels = raw22587step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22587step0 raw22587step0Labels permutation56 hz
    mixedMoment B raw22587step1 raw22587step1Labels = mixedMoment B raw22587step2 raw22587step2Labels := by
      have ha : raw22587step2 = (fun i j => raw22587step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22587step2 raw22587step1; decide +kernel
      have hl : raw22587step2Labels = raw22587step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22587step1 raw22587step1Labels permutation8 permutation3
    _ = mixedMoment B node2969 node2969Labels := by rfl

def raw22588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22588step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22588step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22588step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22588 raw22588Labels = mixedMoment B node2969 node2969Labels := by
  calc
    mixedMoment B raw22588 raw22588Labels = mixedMoment B raw22588step0 raw22588step0Labels := by
      have hz : ∀ j, raw22588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22588step0 = (fun i j => raw22588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22588step0 raw22588; decide +kernel
      have hl : raw22588step0Labels = raw22588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22588 raw22588Labels permutation346 hz
    mixedMoment B raw22588step0 raw22588step0Labels = mixedMoment B raw22588step1 raw22588step1Labels := by
      have hz : ∀ j, raw22588step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22588step1 = (fun i j => raw22588step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22588step1 raw22588step0; decide +kernel
      have hl : raw22588step1Labels = raw22588step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22588step0 raw22588step0Labels permutation56 hz
    mixedMoment B raw22588step1 raw22588step1Labels = mixedMoment B raw22588step2 raw22588step2Labels := by
      have ha : raw22588step2 = (fun i j => raw22588step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22588step2 raw22588step1; decide +kernel
      have hl : raw22588step2Labels = raw22588step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22588step1 raw22588step1Labels permutation8 permutation3
    _ = mixedMoment B node2969 node2969Labels := by rfl

def raw22589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22589step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22589step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22589step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -1, -1], ![1, 0, -1]]
def raw22589step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22589step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw22589step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22589 raw22589Labels = mixedMoment B node3123 node3123Labels := by
  calc
    mixedMoment B raw22589 raw22589Labels = mixedMoment B raw22589step0 raw22589step0Labels := by
      have hz : ∀ j, raw22589 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22589step0 = (fun i j => raw22589 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22589step0 raw22589; decide +kernel
      have hl : raw22589step0Labels = raw22589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22589 raw22589Labels permutation434 hz
    mixedMoment B raw22589step0 raw22589step0Labels = mixedMoment B raw22589step1 raw22589step1Labels := by
      have hz : ∀ j, raw22589step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22589step1 = (fun i j => raw22589step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22589step1 raw22589step0; decide +kernel
      have hl : raw22589step1Labels = raw22589step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22589step0 raw22589step0Labels permutation80 hz
    mixedMoment B raw22589step1 raw22589step1Labels = mixedMoment B raw22589step2 raw22589step2Labels := by
      have hz : ∀ j, raw22589step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22589step2 = (fun i j => raw22589step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22589step2 raw22589step1; decide +kernel
      have hl : raw22589step2Labels = raw22589step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22589step1 raw22589step1Labels permutation14 hz
    mixedMoment B raw22589step2 raw22589step2Labels = mixedMoment B raw22589step3 raw22589step3Labels := by
      have ha : raw22589step3 = (fun i j => raw22589step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22589step3 raw22589step2; decide +kernel
      have hl : raw22589step3Labels = raw22589step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22589step2 raw22589step2Labels permutation3 permutation3
    _ = mixedMoment B node3123 node3123Labels := by rfl

def raw22590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22590step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22590step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22590 raw22590Labels = mixedMoment B node614 node614Labels := by
  calc
    mixedMoment B raw22590 raw22590Labels = mixedMoment B raw22590step0 raw22590step0Labels := by
      have hz : ∀ j, raw22590 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22590step0 = (fun i j => raw22590 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22590step0 raw22590; decide +kernel
      have hl : raw22590step0Labels = raw22590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22590 raw22590Labels permutation434 hz
    mixedMoment B raw22590step0 raw22590step0Labels = mixedMoment B raw22590step1 raw22590step1Labels := by
      have hz : ∀ j, raw22590step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22590step1 = (fun i j => raw22590step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22590step1 raw22590step0; decide +kernel
      have hl : raw22590step1Labels = raw22590step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22590step0 raw22590step0Labels permutation80 hz
    mixedMoment B raw22590step1 raw22590step1Labels = mixedMoment B raw22590step2 raw22590step2Labels := by
      have ha : raw22590step2 = (fun i j => raw22590step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22590step2 raw22590step1; decide +kernel
      have hl : raw22590step2Labels = raw22590step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22590step1 raw22590step1Labels permutation8 permutation3
    _ = mixedMoment B node614 node614Labels := by rfl

def raw22591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22591step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22591step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22591 raw22591Labels = mixedMoment B node1139 node1139Labels := by
  calc
    mixedMoment B raw22591 raw22591Labels = mixedMoment B raw22591step0 raw22591step0Labels := by
      have hz : ∀ j, raw22591 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22591step0 = (fun i j => raw22591 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22591step0 raw22591; decide +kernel
      have hl : raw22591step0Labels = raw22591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22591 raw22591Labels permutation434 hz
    mixedMoment B raw22591step0 raw22591step0Labels = mixedMoment B raw22591step1 raw22591step1Labels := by
      have ha : raw22591step1 = (fun i j => raw22591step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22591step1 raw22591step0; decide +kernel
      have hl : raw22591step1Labels = raw22591step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22591step0 raw22591step0Labels permutation38 permutation3
    _ = mixedMoment B node1139 node1139Labels := by rfl

def raw22592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22592step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22592step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22592 raw22592Labels = mixedMoment B node1139 node1139Labels := by
  calc
    mixedMoment B raw22592 raw22592Labels = mixedMoment B raw22592step0 raw22592step0Labels := by
      have hz : ∀ j, raw22592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22592step0 = (fun i j => raw22592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22592step0 raw22592; decide +kernel
      have hl : raw22592step0Labels = raw22592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22592 raw22592Labels permutation346 hz
    mixedMoment B raw22592step0 raw22592step0Labels = mixedMoment B raw22592step1 raw22592step1Labels := by
      have ha : raw22592step1 = (fun i j => raw22592step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22592step1 raw22592step0; decide +kernel
      have hl : raw22592step1Labels = raw22592step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22592step0 raw22592step0Labels permutation38 permutation3
    _ = mixedMoment B node1139 node1139Labels := by rfl

def raw22593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22593step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22593step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22593step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22593step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22593 raw22593Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw22593 raw22593Labels = mixedMoment B raw22593step0 raw22593step0Labels := by
      have hz : ∀ j, raw22593 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22593step0 = (fun i j => raw22593 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22593step0 raw22593; decide +kernel
      have hl : raw22593step0Labels = raw22593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22593 raw22593Labels permutation434 hz
    mixedMoment B raw22593step0 raw22593step0Labels = mixedMoment B raw22593step1 raw22593step1Labels := by
      have hz : ∀ j, raw22593step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22593step1 = (fun i j => raw22593step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22593step1 raw22593step0; decide +kernel
      have hl : raw22593step1Labels = raw22593step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22593step0 raw22593step0Labels permutation80 hz
    mixedMoment B raw22593step1 raw22593step1Labels = mixedMoment B raw22593step2 raw22593step2Labels := by
      have ha : raw22593step2 = (fun i j => raw22593step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22593step2 raw22593step1; decide +kernel
      have hl : raw22593step2Labels = raw22593step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22593step1 raw22593step1Labels permutation12 permutation3
    _ = mixedMoment B node1301 node1301Labels := by rfl

def raw22594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22594step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22594step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22594step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22594step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22594 raw22594Labels = mixedMoment B node614 node614Labels := by
  calc
    mixedMoment B raw22594 raw22594Labels = mixedMoment B raw22594step0 raw22594step0Labels := by
      have hz : ∀ j, raw22594 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22594step0 = (fun i j => raw22594 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22594step0 raw22594; decide +kernel
      have hl : raw22594step0Labels = raw22594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22594 raw22594Labels permutation434 hz
    mixedMoment B raw22594step0 raw22594step0Labels = mixedMoment B raw22594step1 raw22594step1Labels := by
      have hz : ∀ j, raw22594step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22594step1 = (fun i j => raw22594step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22594step1 raw22594step0; decide +kernel
      have hl : raw22594step1Labels = raw22594step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22594step0 raw22594step0Labels permutation56 hz
    mixedMoment B raw22594step1 raw22594step1Labels = mixedMoment B raw22594step2 raw22594step2Labels := by
      have ha : raw22594step2 = (fun i j => raw22594step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22594step2 raw22594step1; decide +kernel
      have hl : raw22594step2Labels = raw22594step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22594step1 raw22594step1Labels permutation8 permutation3
    _ = mixedMoment B node614 node614Labels := by rfl

def raw22595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22595step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22595step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22595 raw22595Labels = mixedMoment B node1139 node1139Labels := by
  calc
    mixedMoment B raw22595 raw22595Labels = mixedMoment B raw22595step0 raw22595step0Labels := by
      have hz : ∀ j, raw22595 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22595step0 = (fun i j => raw22595 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22595step0 raw22595; decide +kernel
      have hl : raw22595step0Labels = raw22595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22595 raw22595Labels permutation434 hz
    mixedMoment B raw22595step0 raw22595step0Labels = mixedMoment B raw22595step1 raw22595step1Labels := by
      have ha : raw22595step1 = (fun i j => raw22595step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22595step1 raw22595step0; decide +kernel
      have hl : raw22595step1Labels = raw22595step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22595step0 raw22595step0Labels permutation32 permutation3
    _ = mixedMoment B node1139 node1139Labels := by rfl

def raw22596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22596step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22596step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22596 raw22596Labels = mixedMoment B node1139 node1139Labels := by
  calc
    mixedMoment B raw22596 raw22596Labels = mixedMoment B raw22596step0 raw22596step0Labels := by
      have hz : ∀ j, raw22596 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22596step0 = (fun i j => raw22596 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22596step0 raw22596; decide +kernel
      have hl : raw22596step0Labels = raw22596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22596 raw22596Labels permutation265 hz
    mixedMoment B raw22596step0 raw22596step0Labels = mixedMoment B raw22596step1 raw22596step1Labels := by
      have ha : raw22596step1 = (fun i j => raw22596step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22596step1 raw22596step0; decide +kernel
      have hl : raw22596step1Labels = raw22596step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22596step0 raw22596step0Labels permutation38 permutation3
    _ = mixedMoment B node1139 node1139Labels := by rfl

def raw22597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22597step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22597step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22597step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22597step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22597 raw22597Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw22597 raw22597Labels = mixedMoment B raw22597step0 raw22597step0Labels := by
      have hz : ∀ j, raw22597 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22597step0 = (fun i j => raw22597 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22597step0 raw22597; decide +kernel
      have hl : raw22597step0Labels = raw22597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22597 raw22597Labels permutation434 hz
    mixedMoment B raw22597step0 raw22597step0Labels = mixedMoment B raw22597step1 raw22597step1Labels := by
      have hz : ∀ j, raw22597step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22597step1 = (fun i j => raw22597step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22597step1 raw22597step0; decide +kernel
      have hl : raw22597step1Labels = raw22597step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22597step0 raw22597step0Labels permutation56 hz
    mixedMoment B raw22597step1 raw22597step1Labels = mixedMoment B raw22597step2 raw22597step2Labels := by
      have ha : raw22597step2 = (fun i j => raw22597step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22597step2 raw22597step1; decide +kernel
      have hl : raw22597step2Labels = raw22597step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22597step1 raw22597step1Labels permutation12 permutation3
    _ = mixedMoment B node1301 node1301Labels := by rfl

def raw22598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22598step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22598step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22598 raw22598Labels = mixedMoment B node614 node614Labels := by
  calc
    mixedMoment B raw22598 raw22598Labels = mixedMoment B raw22598step0 raw22598step0Labels := by
      have hz : ∀ j, raw22598 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22598step0 = (fun i j => raw22598 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22598step0 raw22598; decide +kernel
      have hl : raw22598step0Labels = raw22598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22598 raw22598Labels permutation346 hz
    mixedMoment B raw22598step0 raw22598step0Labels = mixedMoment B raw22598step1 raw22598step1Labels := by
      have hz : ∀ j, raw22598step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22598step1 = (fun i j => raw22598step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22598step1 raw22598step0; decide +kernel
      have hl : raw22598step1Labels = raw22598step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22598step0 raw22598step0Labels permutation56 hz
    mixedMoment B raw22598step1 raw22598step1Labels = mixedMoment B raw22598step2 raw22598step2Labels := by
      have ha : raw22598step2 = (fun i j => raw22598step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22598step2 raw22598step1; decide +kernel
      have hl : raw22598step2Labels = raw22598step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22598step1 raw22598step1Labels permutation8 permutation3
    _ = mixedMoment B node614 node614Labels := by rfl

def raw22599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22599step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22599step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22599 raw22599Labels = mixedMoment B node1139 node1139Labels := by
  calc
    mixedMoment B raw22599 raw22599Labels = mixedMoment B raw22599step0 raw22599step0Labels := by
      have hz : ∀ j, raw22599 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22599step0 = (fun i j => raw22599 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22599step0 raw22599; decide +kernel
      have hl : raw22599step0Labels = raw22599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22599 raw22599Labels permutation346 hz
    mixedMoment B raw22599step0 raw22599step0Labels = mixedMoment B raw22599step1 raw22599step1Labels := by
      have ha : raw22599step1 = (fun i j => raw22599step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22599step1 raw22599step0; decide +kernel
      have hl : raw22599step1Labels = raw22599step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22599step0 raw22599step0Labels permutation32 permutation3
    _ = mixedMoment B node1139 node1139Labels := by rfl

def raw22600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22600step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22600step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22600 raw22600Labels = mixedMoment B node1139 node1139Labels := by
  calc
    mixedMoment B raw22600 raw22600Labels = mixedMoment B raw22600step0 raw22600step0Labels := by
      have hz : ∀ j, raw22600 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22600step0 = (fun i j => raw22600 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22600step0 raw22600; decide +kernel
      have hl : raw22600step0Labels = raw22600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22600 raw22600Labels permutation265 hz
    mixedMoment B raw22600step0 raw22600step0Labels = mixedMoment B raw22600step1 raw22600step1Labels := by
      have ha : raw22600step1 = (fun i j => raw22600step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22600step1 raw22600step0; decide +kernel
      have hl : raw22600step1Labels = raw22600step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22600step0 raw22600step0Labels permutation32 permutation3
    _ = mixedMoment B node1139 node1139Labels := by rfl

def raw22601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22601Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22601step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw22601step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22601step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22601 raw22601Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw22601 raw22601Labels = mixedMoment B raw22601step0 raw22601step0Labels := by
      have hz : ∀ j, raw22601 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22601step0 = (fun i j => raw22601 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22601step0 raw22601; decide +kernel
      have hl : raw22601step0Labels = raw22601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22601 raw22601Labels permutation346 hz
    mixedMoment B raw22601step0 raw22601step0Labels = mixedMoment B raw22601step1 raw22601step1Labels := by
      have hz : ∀ j, raw22601step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22601step1 = (fun i j => raw22601step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22601step1 raw22601step0; decide +kernel
      have hl : raw22601step1Labels = raw22601step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22601step0 raw22601step0Labels permutation56 hz
    mixedMoment B raw22601step1 raw22601step1Labels = mixedMoment B raw22601step2 raw22601step2Labels := by
      have ha : raw22601step2 = (fun i j => raw22601step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22601step2 raw22601step1; decide +kernel
      have hl : raw22601step2Labels = raw22601step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22601step1 raw22601step1Labels permutation12 permutation3
    _ = mixedMoment B node1301 node1301Labels := by rfl

def raw22602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22602Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22602step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22602step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22602step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22602step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![3, -2, -1], ![2, -1, -1]]
def raw22602step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22602step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw22602step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22602 raw22602Labels = mixedMoment B node619 node619Labels := by
  calc
    mixedMoment B raw22602 raw22602Labels = mixedMoment B raw22602step0 raw22602step0Labels := by
      have hz : ∀ j, raw22602 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22602step0 = (fun i j => raw22602 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22602step0 raw22602; decide +kernel
      have hl : raw22602step0Labels = raw22602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22602 raw22602Labels permutation434 hz
    mixedMoment B raw22602step0 raw22602step0Labels = mixedMoment B raw22602step1 raw22602step1Labels := by
      have hz : ∀ j, raw22602step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22602step1 = (fun i j => raw22602step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22602step1 raw22602step0; decide +kernel
      have hl : raw22602step1Labels = raw22602step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22602step0 raw22602step0Labels permutation80 hz
    mixedMoment B raw22602step1 raw22602step1Labels = mixedMoment B raw22602step2 raw22602step2Labels := by
      have hz : ∀ j, raw22602step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22602step2 = (fun i j => raw22602step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22602step2 raw22602step1; decide +kernel
      have hl : raw22602step2Labels = raw22602step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22602step1 raw22602step1Labels permutation14 hz
    mixedMoment B raw22602step2 raw22602step2Labels = mixedMoment B raw22602step3 raw22602step3Labels := by
      have ha : raw22602step3 = (fun i j => raw22602step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22602step3 raw22602step2; decide +kernel
      have hl : raw22602step3Labels = raw22602step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22602step2 raw22602step2Labels permutation3 permutation3
    _ = mixedMoment B node619 node619Labels := by rfl

def raw22603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22603Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22603step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22603step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22603step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22603 raw22603Labels = mixedMoment B node1144 node1144Labels := by
  calc
    mixedMoment B raw22603 raw22603Labels = mixedMoment B raw22603step0 raw22603step0Labels := by
      have hz : ∀ j, raw22603 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22603step0 = (fun i j => raw22603 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22603step0 raw22603; decide +kernel
      have hl : raw22603step0Labels = raw22603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22603 raw22603Labels permutation434 hz
    mixedMoment B raw22603step0 raw22603step0Labels = mixedMoment B raw22603step1 raw22603step1Labels := by
      have hz : ∀ j, raw22603step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22603step1 = (fun i j => raw22603step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22603step1 raw22603step0; decide +kernel
      have hl : raw22603step1Labels = raw22603step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22603step0 raw22603step0Labels permutation80 hz
    mixedMoment B raw22603step1 raw22603step1Labels = mixedMoment B raw22603step2 raw22603step2Labels := by
      have ha : raw22603step2 = (fun i j => raw22603step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22603step2 raw22603step1; decide +kernel
      have hl : raw22603step2Labels = raw22603step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22603step1 raw22603step1Labels permutation9 permutation3
    _ = mixedMoment B node1144 node1144Labels := by rfl

def raw22604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22604Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22604step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22604step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22604step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22604 raw22604Labels = mixedMoment B node1144 node1144Labels := by
  calc
    mixedMoment B raw22604 raw22604Labels = mixedMoment B raw22604step0 raw22604step0Labels := by
      have hz : ∀ j, raw22604 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22604step0 = (fun i j => raw22604 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22604step0 raw22604; decide +kernel
      have hl : raw22604step0Labels = raw22604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22604 raw22604Labels permutation434 hz
    mixedMoment B raw22604step0 raw22604step0Labels = mixedMoment B raw22604step1 raw22604step1Labels := by
      have hz : ∀ j, raw22604step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22604step1 = (fun i j => raw22604step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22604step1 raw22604step0; decide +kernel
      have hl : raw22604step1Labels = raw22604step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22604step0 raw22604step0Labels permutation56 hz
    mixedMoment B raw22604step1 raw22604step1Labels = mixedMoment B raw22604step2 raw22604step2Labels := by
      have ha : raw22604step2 = (fun i j => raw22604step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22604step2 raw22604step1; decide +kernel
      have hl : raw22604step2Labels = raw22604step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22604step1 raw22604step1Labels permutation9 permutation3
    _ = mixedMoment B node1144 node1144Labels := by rfl

def raw22605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22605Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22605step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw22605step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22605step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22605step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22605 raw22605Labels = mixedMoment B node1144 node1144Labels := by
  calc
    mixedMoment B raw22605 raw22605Labels = mixedMoment B raw22605step0 raw22605step0Labels := by
      have hz : ∀ j, raw22605 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22605step0 = (fun i j => raw22605 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22605step0 raw22605; decide +kernel
      have hl : raw22605step0Labels = raw22605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22605 raw22605Labels permutation346 hz
    mixedMoment B raw22605step0 raw22605step0Labels = mixedMoment B raw22605step1 raw22605step1Labels := by
      have hz : ∀ j, raw22605step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22605step1 = (fun i j => raw22605step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22605step1 raw22605step0; decide +kernel
      have hl : raw22605step1Labels = raw22605step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22605step0 raw22605step0Labels permutation56 hz
    mixedMoment B raw22605step1 raw22605step1Labels = mixedMoment B raw22605step2 raw22605step2Labels := by
      have ha : raw22605step2 = (fun i j => raw22605step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22605step2 raw22605step1; decide +kernel
      have hl : raw22605step2Labels = raw22605step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22605step1 raw22605step1Labels permutation9 permutation3
    _ = mixedMoment B node1144 node1144Labels := by rfl

def raw22606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw22606Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw22606step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22606step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw22606step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22606step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![3, -2, -1], ![1, 0, -1]]
def raw22606step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22606step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw22606step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22606 raw22606Labels = mixedMoment B node1304 node1304Labels := by
  calc
    mixedMoment B raw22606 raw22606Labels = mixedMoment B raw22606step0 raw22606step0Labels := by
      have hz : ∀ j, raw22606 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22606step0 = (fun i j => raw22606 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22606step0 raw22606; decide +kernel
      have hl : raw22606step0Labels = raw22606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22606 raw22606Labels permutation434 hz
    mixedMoment B raw22606step0 raw22606step0Labels = mixedMoment B raw22606step1 raw22606step1Labels := by
      have hz : ∀ j, raw22606step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22606step1 = (fun i j => raw22606step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22606step1 raw22606step0; decide +kernel
      have hl : raw22606step1Labels = raw22606step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22606step0 raw22606step0Labels permutation80 hz
    mixedMoment B raw22606step1 raw22606step1Labels = mixedMoment B raw22606step2 raw22606step2Labels := by
      have hz : ∀ j, raw22606step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22606step2 = (fun i j => raw22606step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22606step2 raw22606step1; decide +kernel
      have hl : raw22606step2Labels = raw22606step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22606step1 raw22606step1Labels permutation14 hz
    mixedMoment B raw22606step2 raw22606step2Labels = mixedMoment B raw22606step3 raw22606step3Labels := by
      have ha : raw22606step3 = (fun i j => raw22606step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22606step3 raw22606step2; decide +kernel
      have hl : raw22606step3Labels = raw22606step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22606step2 raw22606step2Labels permutation3 permutation3
    _ = mixedMoment B node1304 node1304Labels := by rfl

def raw22607 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22607step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22607step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22607step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22607 raw22607Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw22607 raw22607Labels = mixedMoment B raw22607step0 raw22607step0Labels := by
      have hz : ∀ j, raw22607 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22607step0 = (fun i j => raw22607 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22607step0 raw22607; decide +kernel
      have hl : raw22607step0Labels = raw22607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22607 raw22607Labels permutation434 hz
    mixedMoment B raw22607step0 raw22607step0Labels = mixedMoment B raw22607step1 raw22607step1Labels := by
      have hz : ∀ j, raw22607step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22607step1 = (fun i j => raw22607step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22607step1 raw22607step0; decide +kernel
      have hl : raw22607step1Labels = raw22607step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22607step0 raw22607step0Labels permutation80 hz
    mixedMoment B raw22607step1 raw22607step1Labels = mixedMoment B raw22607step2 raw22607step2Labels := by
      have ha : raw22607step2 = (fun i j => raw22607step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22607step2 raw22607step1; decide +kernel
      have hl : raw22607step2Labels = raw22607step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22607step1 raw22607step1Labels permutation8 permutation7
    mixedMoment B raw22607step2 raw22607step2Labels = mixedMoment B raw22607step3 raw22607step3Labels := by
      have ha : raw22607step3 = raw22607step2 := by apply Matrix.ext; unfold raw22607step3 raw22607step2; decide +kernel
      have hl : raw22607step2Labels = labelEmbedding10 ∘ raw22607step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22607step2 raw22607step2Labels raw22607step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

def raw22608 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22608step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22608step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22608step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22608step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22608step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22608 raw22608Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw22608 raw22608Labels = mixedMoment B raw22608step0 raw22608step0Labels := by
      have hz : ∀ j, raw22608 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22608step0 = (fun i j => raw22608 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22608step0 raw22608; decide +kernel
      have hl : raw22608step0Labels = raw22608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22608 raw22608Labels permutation434 hz
    mixedMoment B raw22608step0 raw22608step0Labels = mixedMoment B raw22608step1 raw22608step1Labels := by
      have hz : ∀ j, raw22608step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22608step1 = (fun i j => raw22608step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22608step1 raw22608step0; decide +kernel
      have hl : raw22608step1Labels = raw22608step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22608step0 raw22608step0Labels permutation56 hz
    mixedMoment B raw22608step1 raw22608step1Labels = mixedMoment B raw22608step2 raw22608step2Labels := by
      have ha : raw22608step2 = (fun i j => raw22608step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22608step2 raw22608step1; decide +kernel
      have hl : raw22608step2Labels = raw22608step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22608step1 raw22608step1Labels permutation8 permutation7
    mixedMoment B raw22608step2 raw22608step2Labels = mixedMoment B raw22608step3 raw22608step3Labels := by
      have ha : raw22608step3 = raw22608step2 := by apply Matrix.ext; unfold raw22608step3 raw22608step2; decide +kernel
      have hl : raw22608step2Labels = labelEmbedding10 ∘ raw22608step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22608step2 raw22608step2Labels raw22608step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

def raw22609 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22609step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22609step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22609step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22609step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22609step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22609step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22609 raw22609Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw22609 raw22609Labels = mixedMoment B raw22609step0 raw22609step0Labels := by
      have hz : ∀ j, raw22609 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22609step0 = (fun i j => raw22609 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22609step0 raw22609; decide +kernel
      have hl : raw22609step0Labels = raw22609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22609 raw22609Labels permutation346 hz
    mixedMoment B raw22609step0 raw22609step0Labels = mixedMoment B raw22609step1 raw22609step1Labels := by
      have hz : ∀ j, raw22609step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22609step1 = (fun i j => raw22609step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22609step1 raw22609step0; decide +kernel
      have hl : raw22609step1Labels = raw22609step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22609step0 raw22609step0Labels permutation56 hz
    mixedMoment B raw22609step1 raw22609step1Labels = mixedMoment B raw22609step2 raw22609step2Labels := by
      have ha : raw22609step2 = (fun i j => raw22609step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22609step2 raw22609step1; decide +kernel
      have hl : raw22609step2Labels = raw22609step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22609step1 raw22609step1Labels permutation8 permutation7
    mixedMoment B raw22609step2 raw22609step2Labels = mixedMoment B raw22609step3 raw22609step3Labels := by
      have ha : raw22609step3 = raw22609step2 := by apply Matrix.ext; unfold raw22609step3 raw22609step2; decide +kernel
      have hl : raw22609step2Labels = labelEmbedding10 ∘ raw22609step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22609step2 raw22609step2Labels raw22609step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

def raw22610 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22610step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -1, 2], ![-2, 0, 2]]
def raw22610step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22610step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22610step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22610step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22610step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22610 raw22610Labels = mixedMoment B node4511 node4511Labels := by
  calc
    mixedMoment B raw22610 raw22610Labels = mixedMoment B raw22610step0 raw22610step0Labels := by
      have hz : ∀ j, raw22610 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22610step0 = (fun i j => raw22610 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22610step0 raw22610; decide +kernel
      have hl : raw22610step0Labels = raw22610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22610 raw22610Labels permutation434 hz
    mixedMoment B raw22610step0 raw22610step0Labels = mixedMoment B raw22610step1 raw22610step1Labels := by
      have hz : ∀ j, raw22610step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22610step1 = (fun i j => raw22610step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22610step1 raw22610step0; decide +kernel
      have hl : raw22610step1Labels = raw22610step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22610step0 raw22610step0Labels permutation80 hz
    mixedMoment B raw22610step1 raw22610step1Labels = mixedMoment B raw22610step2 raw22610step2Labels := by
      have hz : ∀ j, raw22610step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22610step2 = (fun i j => raw22610step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22610step2 raw22610step1; decide +kernel
      have hl : raw22610step2Labels = raw22610step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22610step1 raw22610step1Labels permutation14 hz
    mixedMoment B raw22610step2 raw22610step2Labels = mixedMoment B raw22610step3 raw22610step3Labels := by
      have ha : raw22610step3 = (fun i j => raw22610step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22610step3 raw22610step2; decide +kernel
      have hl : raw22610step3Labels = raw22610step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22610step2 raw22610step2Labels permutation2 permutation7
    mixedMoment B raw22610step3 raw22610step3Labels = mixedMoment B raw22610step4 raw22610step4Labels := by
      have ha : raw22610step4 = raw22610step3 := by apply Matrix.ext; unfold raw22610step4 raw22610step3; decide +kernel
      have hl : raw22610step3Labels = labelEmbedding10 ∘ raw22610step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22610step3 raw22610step3Labels raw22610step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4511 node4511Labels := by rfl

def raw22611 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22611step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22611step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22611step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22611step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22611step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22611step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22611 raw22611Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw22611 raw22611Labels = mixedMoment B raw22611step0 raw22611step0Labels := by
      have hz : ∀ j, raw22611 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22611step0 = (fun i j => raw22611 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22611step0 raw22611; decide +kernel
      have hl : raw22611step0Labels = raw22611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22611 raw22611Labels permutation434 hz
    mixedMoment B raw22611step0 raw22611step0Labels = mixedMoment B raw22611step1 raw22611step1Labels := by
      have hz : ∀ j, raw22611step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22611step1 = (fun i j => raw22611step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22611step1 raw22611step0; decide +kernel
      have hl : raw22611step1Labels = raw22611step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22611step0 raw22611step0Labels permutation80 hz
    mixedMoment B raw22611step1 raw22611step1Labels = mixedMoment B raw22611step2 raw22611step2Labels := by
      have ha : raw22611step2 = (fun i j => raw22611step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22611step2 raw22611step1; decide +kernel
      have hl : raw22611step2Labels = raw22611step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22611step1 raw22611step1Labels permutation8 permutation6
    mixedMoment B raw22611step2 raw22611step2Labels = mixedMoment B raw22611step3 raw22611step3Labels := by
      have ha : raw22611step3 = raw22611step2 := by apply Matrix.ext; unfold raw22611step3 raw22611step2; decide +kernel
      have hl : raw22611step2Labels = labelEmbedding9 ∘ raw22611step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22611step2 raw22611step2Labels raw22611step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

def raw22612 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22612step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22612step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22612 raw22612Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw22612 raw22612Labels = mixedMoment B raw22612step0 raw22612step0Labels := by
      have hz : ∀ j, raw22612 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22612step0 = (fun i j => raw22612 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22612step0 raw22612; decide +kernel
      have hl : raw22612step0Labels = raw22612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22612 raw22612Labels permutation434 hz
    mixedMoment B raw22612step0 raw22612step0Labels = mixedMoment B raw22612step1 raw22612step1Labels := by
      have ha : raw22612step1 = (fun i j => raw22612step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22612step1 raw22612step0; decide +kernel
      have hl : raw22612step1Labels = raw22612step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22612step0 raw22612step0Labels permutation38 permutation6
    mixedMoment B raw22612step1 raw22612step1Labels = mixedMoment B raw22612step2 raw22612step2Labels := by
      have ha : raw22612step2 = raw22612step1 := by apply Matrix.ext; unfold raw22612step2 raw22612step1; decide +kernel
      have hl : raw22612step1Labels = labelEmbedding9 ∘ raw22612step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22612step1 raw22612step1Labels raw22612step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4593 node4593Labels := by rfl

def raw22613 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22613step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22613step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22613 raw22613Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw22613 raw22613Labels = mixedMoment B raw22613step0 raw22613step0Labels := by
      have hz : ∀ j, raw22613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22613step0 = (fun i j => raw22613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22613step0 raw22613; decide +kernel
      have hl : raw22613step0Labels = raw22613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22613 raw22613Labels permutation346 hz
    mixedMoment B raw22613step0 raw22613step0Labels = mixedMoment B raw22613step1 raw22613step1Labels := by
      have ha : raw22613step1 = (fun i j => raw22613step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22613step1 raw22613step0; decide +kernel
      have hl : raw22613step1Labels = raw22613step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22613step0 raw22613step0Labels permutation38 permutation6
    mixedMoment B raw22613step1 raw22613step1Labels = mixedMoment B raw22613step2 raw22613step2Labels := by
      have ha : raw22613step2 = raw22613step1 := by apply Matrix.ext; unfold raw22613step2 raw22613step1; decide +kernel
      have hl : raw22613step1Labels = labelEmbedding9 ∘ raw22613step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22613step1 raw22613step1Labels raw22613step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4593 node4593Labels := by rfl

def raw22614 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22614step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22614step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22614step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22614step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22614step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22614step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22614step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22614 raw22614Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22614 raw22614Labels = mixedMoment B raw22614step0 raw22614step0Labels := by
      have hz : ∀ j, raw22614 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22614step0 = (fun i j => raw22614 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22614step0 raw22614; decide +kernel
      have hl : raw22614step0Labels = raw22614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22614 raw22614Labels permutation434 hz
    mixedMoment B raw22614step0 raw22614step0Labels = mixedMoment B raw22614step1 raw22614step1Labels := by
      have hz : ∀ j, raw22614step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22614step1 = (fun i j => raw22614step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22614step1 raw22614step0; decide +kernel
      have hl : raw22614step1Labels = raw22614step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22614step0 raw22614step0Labels permutation80 hz
    mixedMoment B raw22614step1 raw22614step1Labels = mixedMoment B raw22614step2 raw22614step2Labels := by
      have ha : raw22614step2 = (fun i j => raw22614step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22614step2 raw22614step1; decide +kernel
      have hl : raw22614step2Labels = raw22614step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22614step1 raw22614step1Labels permutation8 permutation7
    mixedMoment B raw22614step2 raw22614step2Labels = mixedMoment B raw22614step3 raw22614step3Labels := by
      have ha : raw22614step3 = raw22614step2 := by apply Matrix.ext; unfold raw22614step3 raw22614step2; decide +kernel
      have hl : raw22614step2Labels = labelEmbedding10 ∘ raw22614step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22614step2 raw22614step2Labels raw22614step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw22615 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22615step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22615step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22615step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22615step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22615step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22615 raw22615Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw22615 raw22615Labels = mixedMoment B raw22615step0 raw22615step0Labels := by
      have hz : ∀ j, raw22615 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22615step0 = (fun i j => raw22615 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22615step0 raw22615; decide +kernel
      have hl : raw22615step0Labels = raw22615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22615 raw22615Labels permutation434 hz
    mixedMoment B raw22615step0 raw22615step0Labels = mixedMoment B raw22615step1 raw22615step1Labels := by
      have hz : ∀ j, raw22615step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22615step1 = (fun i j => raw22615step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22615step1 raw22615step0; decide +kernel
      have hl : raw22615step1Labels = raw22615step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22615step0 raw22615step0Labels permutation56 hz
    mixedMoment B raw22615step1 raw22615step1Labels = mixedMoment B raw22615step2 raw22615step2Labels := by
      have ha : raw22615step2 = (fun i j => raw22615step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22615step2 raw22615step1; decide +kernel
      have hl : raw22615step2Labels = raw22615step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22615step1 raw22615step1Labels permutation8 permutation6
    mixedMoment B raw22615step2 raw22615step2Labels = mixedMoment B raw22615step3 raw22615step3Labels := by
      have ha : raw22615step3 = raw22615step2 := by apply Matrix.ext; unfold raw22615step3 raw22615step2; decide +kernel
      have hl : raw22615step2Labels = labelEmbedding9 ∘ raw22615step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22615step2 raw22615step2Labels raw22615step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

def raw22616 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22616step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22616step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22616 raw22616Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw22616 raw22616Labels = mixedMoment B raw22616step0 raw22616step0Labels := by
      have hz : ∀ j, raw22616 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22616step0 = (fun i j => raw22616 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22616step0 raw22616; decide +kernel
      have hl : raw22616step0Labels = raw22616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22616 raw22616Labels permutation434 hz
    mixedMoment B raw22616step0 raw22616step0Labels = mixedMoment B raw22616step1 raw22616step1Labels := by
      have ha : raw22616step1 = (fun i j => raw22616step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22616step1 raw22616step0; decide +kernel
      have hl : raw22616step1Labels = raw22616step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22616step0 raw22616step0Labels permutation32 permutation6
    mixedMoment B raw22616step1 raw22616step1Labels = mixedMoment B raw22616step2 raw22616step2Labels := by
      have ha : raw22616step2 = raw22616step1 := by apply Matrix.ext; unfold raw22616step2 raw22616step1; decide +kernel
      have hl : raw22616step1Labels = labelEmbedding9 ∘ raw22616step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22616step1 raw22616step1Labels raw22616step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4593 node4593Labels := by rfl

def raw22617 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22617step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22617step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22617 raw22617Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw22617 raw22617Labels = mixedMoment B raw22617step0 raw22617step0Labels := by
      have hz : ∀ j, raw22617 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22617step0 = (fun i j => raw22617 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22617step0 raw22617; decide +kernel
      have hl : raw22617step0Labels = raw22617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22617 raw22617Labels permutation265 hz
    mixedMoment B raw22617step0 raw22617step0Labels = mixedMoment B raw22617step1 raw22617step1Labels := by
      have ha : raw22617step1 = (fun i j => raw22617step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22617step1 raw22617step0; decide +kernel
      have hl : raw22617step1Labels = raw22617step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22617step0 raw22617step0Labels permutation38 permutation6
    mixedMoment B raw22617step1 raw22617step1Labels = mixedMoment B raw22617step2 raw22617step2Labels := by
      have ha : raw22617step2 = raw22617step1 := by apply Matrix.ext; unfold raw22617step2 raw22617step1; decide +kernel
      have hl : raw22617step1Labels = labelEmbedding9 ∘ raw22617step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22617step1 raw22617step1Labels raw22617step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4593 node4593Labels := by rfl

def raw22618 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22618step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22618step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22618step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22618step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22618 raw22618Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22618 raw22618Labels = mixedMoment B raw22618step0 raw22618step0Labels := by
      have hz : ∀ j, raw22618 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22618step0 = (fun i j => raw22618 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22618step0 raw22618; decide +kernel
      have hl : raw22618step0Labels = raw22618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22618 raw22618Labels permutation434 hz
    mixedMoment B raw22618step0 raw22618step0Labels = mixedMoment B raw22618step1 raw22618step1Labels := by
      have hz : ∀ j, raw22618step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22618step1 = (fun i j => raw22618step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22618step1 raw22618step0; decide +kernel
      have hl : raw22618step1Labels = raw22618step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22618step0 raw22618step0Labels permutation56 hz
    mixedMoment B raw22618step1 raw22618step1Labels = mixedMoment B raw22618step2 raw22618step2Labels := by
      have ha : raw22618step2 = (fun i j => raw22618step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22618step2 raw22618step1; decide +kernel
      have hl : raw22618step2Labels = raw22618step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22618step1 raw22618step1Labels permutation8 permutation7
    mixedMoment B raw22618step2 raw22618step2Labels = mixedMoment B raw22618step3 raw22618step3Labels := by
      have ha : raw22618step3 = raw22618step2 := by apply Matrix.ext; unfold raw22618step3 raw22618step2; decide +kernel
      have hl : raw22618step2Labels = labelEmbedding10 ∘ raw22618step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22618step2 raw22618step2Labels raw22618step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw22619 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22619step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22619step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22619step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22619step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22619step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22619step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22619 raw22619Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw22619 raw22619Labels = mixedMoment B raw22619step0 raw22619step0Labels := by
      have hz : ∀ j, raw22619 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22619step0 = (fun i j => raw22619 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22619step0 raw22619; decide +kernel
      have hl : raw22619step0Labels = raw22619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22619 raw22619Labels permutation346 hz
    mixedMoment B raw22619step0 raw22619step0Labels = mixedMoment B raw22619step1 raw22619step1Labels := by
      have hz : ∀ j, raw22619step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22619step1 = (fun i j => raw22619step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22619step1 raw22619step0; decide +kernel
      have hl : raw22619step1Labels = raw22619step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22619step0 raw22619step0Labels permutation56 hz
    mixedMoment B raw22619step1 raw22619step1Labels = mixedMoment B raw22619step2 raw22619step2Labels := by
      have ha : raw22619step2 = (fun i j => raw22619step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22619step2 raw22619step1; decide +kernel
      have hl : raw22619step2Labels = raw22619step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22619step1 raw22619step1Labels permutation8 permutation6
    mixedMoment B raw22619step2 raw22619step2Labels = mixedMoment B raw22619step3 raw22619step3Labels := by
      have ha : raw22619step3 = raw22619step2 := by apply Matrix.ext; unfold raw22619step3 raw22619step2; decide +kernel
      have hl : raw22619step2Labels = labelEmbedding9 ∘ raw22619step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22619step2 raw22619step2Labels raw22619step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

def raw22620 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22620step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22620step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22620 raw22620Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw22620 raw22620Labels = mixedMoment B raw22620step0 raw22620step0Labels := by
      have hz : ∀ j, raw22620 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22620step0 = (fun i j => raw22620 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22620step0 raw22620; decide +kernel
      have hl : raw22620step0Labels = raw22620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22620 raw22620Labels permutation346 hz
    mixedMoment B raw22620step0 raw22620step0Labels = mixedMoment B raw22620step1 raw22620step1Labels := by
      have ha : raw22620step1 = (fun i j => raw22620step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22620step1 raw22620step0; decide +kernel
      have hl : raw22620step1Labels = raw22620step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22620step0 raw22620step0Labels permutation32 permutation6
    mixedMoment B raw22620step1 raw22620step1Labels = mixedMoment B raw22620step2 raw22620step2Labels := by
      have ha : raw22620step2 = raw22620step1 := by apply Matrix.ext; unfold raw22620step2 raw22620step1; decide +kernel
      have hl : raw22620step1Labels = labelEmbedding9 ∘ raw22620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22620step1 raw22620step1Labels raw22620step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4593 node4593Labels := by rfl

def raw22621 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22621step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22621step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22621 raw22621Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw22621 raw22621Labels = mixedMoment B raw22621step0 raw22621step0Labels := by
      have hz : ∀ j, raw22621 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22621step0 = (fun i j => raw22621 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22621step0 raw22621; decide +kernel
      have hl : raw22621step0Labels = raw22621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22621 raw22621Labels permutation265 hz
    mixedMoment B raw22621step0 raw22621step0Labels = mixedMoment B raw22621step1 raw22621step1Labels := by
      have ha : raw22621step1 = (fun i j => raw22621step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22621step1 raw22621step0; decide +kernel
      have hl : raw22621step1Labels = raw22621step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22621step0 raw22621step0Labels permutation32 permutation6
    mixedMoment B raw22621step1 raw22621step1Labels = mixedMoment B raw22621step2 raw22621step2Labels := by
      have ha : raw22621step2 = raw22621step1 := by apply Matrix.ext; unfold raw22621step2 raw22621step1; decide +kernel
      have hl : raw22621step1Labels = labelEmbedding9 ∘ raw22621step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22621step1 raw22621step1Labels raw22621step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4593 node4593Labels := by rfl

def raw22622 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22622step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22622step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22622step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22622step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22622step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22622 raw22622Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22622 raw22622Labels = mixedMoment B raw22622step0 raw22622step0Labels := by
      have hz : ∀ j, raw22622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22622step0 = (fun i j => raw22622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22622step0 raw22622; decide +kernel
      have hl : raw22622step0Labels = raw22622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22622 raw22622Labels permutation346 hz
    mixedMoment B raw22622step0 raw22622step0Labels = mixedMoment B raw22622step1 raw22622step1Labels := by
      have hz : ∀ j, raw22622step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22622step1 = (fun i j => raw22622step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22622step1 raw22622step0; decide +kernel
      have hl : raw22622step1Labels = raw22622step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22622step0 raw22622step0Labels permutation56 hz
    mixedMoment B raw22622step1 raw22622step1Labels = mixedMoment B raw22622step2 raw22622step2Labels := by
      have ha : raw22622step2 = (fun i j => raw22622step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22622step2 raw22622step1; decide +kernel
      have hl : raw22622step2Labels = raw22622step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22622step1 raw22622step1Labels permutation8 permutation7
    mixedMoment B raw22622step2 raw22622step2Labels = mixedMoment B raw22622step3 raw22622step3Labels := by
      have ha : raw22622step3 = raw22622step2 := by apply Matrix.ext; unfold raw22622step3 raw22622step2; decide +kernel
      have hl : raw22622step2Labels = labelEmbedding10 ∘ raw22622step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22622step2 raw22622step2Labels raw22622step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw22623 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22623step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22623step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22623step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, -2, 2], ![-1, -1, 2]]
def raw22623step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22623step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22623step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22623step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22623step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22623 raw22623Labels = mixedMoment B node4511 node4511Labels := by
  calc
    mixedMoment B raw22623 raw22623Labels = mixedMoment B raw22623step0 raw22623step0Labels := by
      have hz : ∀ j, raw22623 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22623step0 = (fun i j => raw22623 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22623step0 raw22623; decide +kernel
      have hl : raw22623step0Labels = raw22623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22623 raw22623Labels permutation434 hz
    mixedMoment B raw22623step0 raw22623step0Labels = mixedMoment B raw22623step1 raw22623step1Labels := by
      have hz : ∀ j, raw22623step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22623step1 = (fun i j => raw22623step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22623step1 raw22623step0; decide +kernel
      have hl : raw22623step1Labels = raw22623step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22623step0 raw22623step0Labels permutation80 hz
    mixedMoment B raw22623step1 raw22623step1Labels = mixedMoment B raw22623step2 raw22623step2Labels := by
      have hz : ∀ j, raw22623step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22623step2 = (fun i j => raw22623step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22623step2 raw22623step1; decide +kernel
      have hl : raw22623step2Labels = raw22623step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22623step1 raw22623step1Labels permutation14 hz
    mixedMoment B raw22623step2 raw22623step2Labels = mixedMoment B raw22623step3 raw22623step3Labels := by
      have ha : raw22623step3 = (fun i j => raw22623step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22623step3 raw22623step2; decide +kernel
      have hl : raw22623step3Labels = raw22623step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22623step2 raw22623step2Labels permutation3 permutation6
    mixedMoment B raw22623step3 raw22623step3Labels = mixedMoment B raw22623step4 raw22623step4Labels := by
      have ha : raw22623step4 = raw22623step3 := by apply Matrix.ext; unfold raw22623step4 raw22623step3; decide +kernel
      have hl : raw22623step3Labels = labelEmbedding9 ∘ raw22623step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22623step3 raw22623step3Labels raw22623step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4511 node4511Labels := by rfl

def raw22624 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22624step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22624step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22624step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22624step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22624step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22624step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22624 raw22624Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22624 raw22624Labels = mixedMoment B raw22624step0 raw22624step0Labels := by
      have hz : ∀ j, raw22624 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22624step0 = (fun i j => raw22624 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22624step0 raw22624; decide +kernel
      have hl : raw22624step0Labels = raw22624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22624 raw22624Labels permutation434 hz
    mixedMoment B raw22624step0 raw22624step0Labels = mixedMoment B raw22624step1 raw22624step1Labels := by
      have hz : ∀ j, raw22624step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22624step1 = (fun i j => raw22624step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22624step1 raw22624step0; decide +kernel
      have hl : raw22624step1Labels = raw22624step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22624step0 raw22624step0Labels permutation80 hz
    mixedMoment B raw22624step1 raw22624step1Labels = mixedMoment B raw22624step2 raw22624step2Labels := by
      have ha : raw22624step2 = (fun i j => raw22624step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22624step2 raw22624step1; decide +kernel
      have hl : raw22624step2Labels = raw22624step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22624step1 raw22624step1Labels permutation9 permutation6
    mixedMoment B raw22624step2 raw22624step2Labels = mixedMoment B raw22624step3 raw22624step3Labels := by
      have ha : raw22624step3 = raw22624step2 := by apply Matrix.ext; unfold raw22624step3 raw22624step2; decide +kernel
      have hl : raw22624step2Labels = labelEmbedding9 ∘ raw22624step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22624step2 raw22624step2Labels raw22624step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw22625 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22625step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22625step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22625step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22625step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22625step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22625step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22625 raw22625Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22625 raw22625Labels = mixedMoment B raw22625step0 raw22625step0Labels := by
      have hz : ∀ j, raw22625 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22625step0 = (fun i j => raw22625 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22625step0 raw22625; decide +kernel
      have hl : raw22625step0Labels = raw22625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22625 raw22625Labels permutation434 hz
    mixedMoment B raw22625step0 raw22625step0Labels = mixedMoment B raw22625step1 raw22625step1Labels := by
      have hz : ∀ j, raw22625step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22625step1 = (fun i j => raw22625step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22625step1 raw22625step0; decide +kernel
      have hl : raw22625step1Labels = raw22625step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22625step0 raw22625step0Labels permutation56 hz
    mixedMoment B raw22625step1 raw22625step1Labels = mixedMoment B raw22625step2 raw22625step2Labels := by
      have ha : raw22625step2 = (fun i j => raw22625step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22625step2 raw22625step1; decide +kernel
      have hl : raw22625step2Labels = raw22625step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22625step1 raw22625step1Labels permutation9 permutation6
    mixedMoment B raw22625step2 raw22625step2Labels = mixedMoment B raw22625step3 raw22625step3Labels := by
      have ha : raw22625step3 = raw22625step2 := by apply Matrix.ext; unfold raw22625step3 raw22625step2; decide +kernel
      have hl : raw22625step2Labels = labelEmbedding9 ∘ raw22625step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22625step2 raw22625step2Labels raw22625step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw22626 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22626step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22626step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22626step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22626step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22626step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22626step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22626 raw22626Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22626 raw22626Labels = mixedMoment B raw22626step0 raw22626step0Labels := by
      have hz : ∀ j, raw22626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22626step0 = (fun i j => raw22626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22626step0 raw22626; decide +kernel
      have hl : raw22626step0Labels = raw22626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22626 raw22626Labels permutation346 hz
    mixedMoment B raw22626step0 raw22626step0Labels = mixedMoment B raw22626step1 raw22626step1Labels := by
      have hz : ∀ j, raw22626step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22626step1 = (fun i j => raw22626step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22626step1 raw22626step0; decide +kernel
      have hl : raw22626step1Labels = raw22626step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22626step0 raw22626step0Labels permutation56 hz
    mixedMoment B raw22626step1 raw22626step1Labels = mixedMoment B raw22626step2 raw22626step2Labels := by
      have ha : raw22626step2 = (fun i j => raw22626step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22626step2 raw22626step1; decide +kernel
      have hl : raw22626step2Labels = raw22626step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22626step1 raw22626step1Labels permutation9 permutation6
    mixedMoment B raw22626step2 raw22626step2Labels = mixedMoment B raw22626step3 raw22626step3Labels := by
      have ha : raw22626step3 = raw22626step2 := by apply Matrix.ext; unfold raw22626step3 raw22626step2; decide +kernel
      have hl : raw22626step2Labels = labelEmbedding9 ∘ raw22626step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22626step2 raw22626step2Labels raw22626step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw22627 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22627step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22627step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22627step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -2, 2], ![-2, 0, 2]]
def raw22627step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22627step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw22627step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22627step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw22627step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22627 raw22627Labels = mixedMoment B node4627 node4627Labels := by
  calc
    mixedMoment B raw22627 raw22627Labels = mixedMoment B raw22627step0 raw22627step0Labels := by
      have hz : ∀ j, raw22627 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22627step0 = (fun i j => raw22627 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22627step0 raw22627; decide +kernel
      have hl : raw22627step0Labels = raw22627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22627 raw22627Labels permutation434 hz
    mixedMoment B raw22627step0 raw22627step0Labels = mixedMoment B raw22627step1 raw22627step1Labels := by
      have hz : ∀ j, raw22627step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22627step1 = (fun i j => raw22627step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22627step1 raw22627step0; decide +kernel
      have hl : raw22627step1Labels = raw22627step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22627step0 raw22627step0Labels permutation80 hz
    mixedMoment B raw22627step1 raw22627step1Labels = mixedMoment B raw22627step2 raw22627step2Labels := by
      have hz : ∀ j, raw22627step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22627step2 = (fun i j => raw22627step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22627step2 raw22627step1; decide +kernel
      have hl : raw22627step2Labels = raw22627step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22627step1 raw22627step1Labels permutation14 hz
    mixedMoment B raw22627step2 raw22627step2Labels = mixedMoment B raw22627step3 raw22627step3Labels := by
      have ha : raw22627step3 = (fun i j => raw22627step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22627step3 raw22627step2; decide +kernel
      have hl : raw22627step3Labels = raw22627step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22627step2 raw22627step2Labels permutation3 permutation6
    mixedMoment B raw22627step3 raw22627step3Labels = mixedMoment B raw22627step4 raw22627step4Labels := by
      have ha : raw22627step4 = raw22627step3 := by apply Matrix.ext; unfold raw22627step4 raw22627step3; decide +kernel
      have hl : raw22627step3Labels = labelEmbedding9 ∘ raw22627step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22627step3 raw22627step3Labels raw22627step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4627 node4627Labels := by rfl

def raw22628 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22628step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22628step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 0, 2], ![0, -2, 2]]
def raw22628step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22628step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw22628step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22628step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw22628step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22628 raw22628Labels = mixedMoment B node4627 node4627Labels := by
  calc
    mixedMoment B raw22628 raw22628Labels = mixedMoment B raw22628step0 raw22628step0Labels := by
      have hz : ∀ j, raw22628 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22628step0 = (fun i j => raw22628 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22628step0 raw22628; decide +kernel
      have hl : raw22628step0Labels = raw22628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22628 raw22628Labels permutation434 hz
    mixedMoment B raw22628step0 raw22628step0Labels = mixedMoment B raw22628step1 raw22628step1Labels := by
      have hz : ∀ j, raw22628step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22628step1 = (fun i j => raw22628step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22628step1 raw22628step0; decide +kernel
      have hl : raw22628step1Labels = raw22628step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22628step0 raw22628step0Labels permutation80 hz
    mixedMoment B raw22628step1 raw22628step1Labels = mixedMoment B raw22628step2 raw22628step2Labels := by
      have hz : ∀ j, raw22628step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22628step2 = (fun i j => raw22628step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22628step2 raw22628step1; decide +kernel
      have hl : raw22628step2Labels = raw22628step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22628step1 raw22628step1Labels permutation14 hz
    mixedMoment B raw22628step2 raw22628step2Labels = mixedMoment B raw22628step3 raw22628step3Labels := by
      have ha : raw22628step3 = (fun i j => raw22628step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22628step3 raw22628step2; decide +kernel
      have hl : raw22628step3Labels = raw22628step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22628step2 raw22628step2Labels permutation2 permutation6
    mixedMoment B raw22628step3 raw22628step3Labels = mixedMoment B raw22628step4 raw22628step4Labels := by
      have ha : raw22628step4 = raw22628step3 := by apply Matrix.ext; unfold raw22628step4 raw22628step3; decide +kernel
      have hl : raw22628step3Labels = labelEmbedding9 ∘ raw22628step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22628step3 raw22628step3Labels raw22628step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4627 node4627Labels := by rfl

def raw22629 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22629step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22629step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22629step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22629step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22629step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22629 raw22629Labels = mixedMoment B node1420 node1420Labels := by
  calc
    mixedMoment B raw22629 raw22629Labels = mixedMoment B raw22629step0 raw22629step0Labels := by
      have hz : ∀ j, raw22629 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22629step0 = (fun i j => raw22629 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22629step0 raw22629; decide +kernel
      have hl : raw22629step0Labels = raw22629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22629 raw22629Labels permutation434 hz
    mixedMoment B raw22629step0 raw22629step0Labels = mixedMoment B raw22629step1 raw22629step1Labels := by
      have hz : ∀ j, raw22629step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22629step1 = (fun i j => raw22629step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22629step1 raw22629step0; decide +kernel
      have hl : raw22629step1Labels = raw22629step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22629step0 raw22629step0Labels permutation80 hz
    mixedMoment B raw22629step1 raw22629step1Labels = mixedMoment B raw22629step2 raw22629step2Labels := by
      have ha : raw22629step2 = (fun i j => raw22629step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22629step2 raw22629step1; decide +kernel
      have hl : raw22629step2Labels = raw22629step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22629step1 raw22629step1Labels permutation8 permutation6
    _ = mixedMoment B node1420 node1420Labels := by rfl

def raw22630 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22630step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22630step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22630step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22630step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22630 raw22630Labels = mixedMoment B node1420 node1420Labels := by
  calc
    mixedMoment B raw22630 raw22630Labels = mixedMoment B raw22630step0 raw22630step0Labels := by
      have hz : ∀ j, raw22630 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22630step0 = (fun i j => raw22630 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22630step0 raw22630; decide +kernel
      have hl : raw22630step0Labels = raw22630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22630 raw22630Labels permutation434 hz
    mixedMoment B raw22630step0 raw22630step0Labels = mixedMoment B raw22630step1 raw22630step1Labels := by
      have hz : ∀ j, raw22630step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22630step1 = (fun i j => raw22630step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22630step1 raw22630step0; decide +kernel
      have hl : raw22630step1Labels = raw22630step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22630step0 raw22630step0Labels permutation56 hz
    mixedMoment B raw22630step1 raw22630step1Labels = mixedMoment B raw22630step2 raw22630step2Labels := by
      have ha : raw22630step2 = (fun i j => raw22630step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22630step2 raw22630step1; decide +kernel
      have hl : raw22630step2Labels = raw22630step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22630step1 raw22630step1Labels permutation8 permutation6
    _ = mixedMoment B node1420 node1420Labels := by rfl

def raw22631 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22631step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22631step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22631step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22631 raw22631Labels = mixedMoment B node1420 node1420Labels := by
  calc
    mixedMoment B raw22631 raw22631Labels = mixedMoment B raw22631step0 raw22631step0Labels := by
      have hz : ∀ j, raw22631 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22631step0 = (fun i j => raw22631 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22631step0 raw22631; decide +kernel
      have hl : raw22631step0Labels = raw22631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22631 raw22631Labels permutation346 hz
    mixedMoment B raw22631step0 raw22631step0Labels = mixedMoment B raw22631step1 raw22631step1Labels := by
      have hz : ∀ j, raw22631step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22631step1 = (fun i j => raw22631step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22631step1 raw22631step0; decide +kernel
      have hl : raw22631step1Labels = raw22631step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22631step0 raw22631step0Labels permutation56 hz
    mixedMoment B raw22631step1 raw22631step1Labels = mixedMoment B raw22631step2 raw22631step2Labels := by
      have ha : raw22631step2 = (fun i j => raw22631step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22631step2 raw22631step1; decide +kernel
      have hl : raw22631step2Labels = raw22631step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22631step1 raw22631step1Labels permutation8 permutation6
    _ = mixedMoment B node1420 node1420Labels := by rfl

def raw22632 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22632step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22632step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22632step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -1, 2], ![-2, 0, 2]]
def raw22632step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22632step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -2, 0], ![2, -1, -1]]
def raw22632step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22632 raw22632Labels = mixedMoment B node1455 node1455Labels := by
  calc
    mixedMoment B raw22632 raw22632Labels = mixedMoment B raw22632step0 raw22632step0Labels := by
      have hz : ∀ j, raw22632 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22632step0 = (fun i j => raw22632 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22632step0 raw22632; decide +kernel
      have hl : raw22632step0Labels = raw22632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22632 raw22632Labels permutation434 hz
    mixedMoment B raw22632step0 raw22632step0Labels = mixedMoment B raw22632step1 raw22632step1Labels := by
      have hz : ∀ j, raw22632step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22632step1 = (fun i j => raw22632step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22632step1 raw22632step0; decide +kernel
      have hl : raw22632step1Labels = raw22632step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22632step0 raw22632step0Labels permutation80 hz
    mixedMoment B raw22632step1 raw22632step1Labels = mixedMoment B raw22632step2 raw22632step2Labels := by
      have hz : ∀ j, raw22632step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22632step2 = (fun i j => raw22632step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22632step2 raw22632step1; decide +kernel
      have hl : raw22632step2Labels = raw22632step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22632step1 raw22632step1Labels permutation14 hz
    mixedMoment B raw22632step2 raw22632step2Labels = mixedMoment B raw22632step3 raw22632step3Labels := by
      have ha : raw22632step3 = (fun i j => raw22632step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22632step3 raw22632step2; decide +kernel
      have hl : raw22632step3Labels = raw22632step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22632step2 raw22632step2Labels permutation3 permutation6
    _ = mixedMoment B node1455 node1455Labels := by rfl

def raw22633 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22633step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22633step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22633 raw22633Labels = mixedMoment B node1050 node1050Labels := by
  calc
    mixedMoment B raw22633 raw22633Labels = mixedMoment B raw22633step0 raw22633step0Labels := by
      have hz : ∀ j, raw22633 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22633step0 = (fun i j => raw22633 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22633step0 raw22633; decide +kernel
      have hl : raw22633step0Labels = raw22633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22633 raw22633Labels permutation434 hz
    mixedMoment B raw22633step0 raw22633step0Labels = mixedMoment B raw22633step1 raw22633step1Labels := by
      have hz : ∀ j, raw22633step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22633step1 = (fun i j => raw22633step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22633step1 raw22633step0; decide +kernel
      have hl : raw22633step1Labels = raw22633step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22633step0 raw22633step0Labels permutation80 hz
    mixedMoment B raw22633step1 raw22633step1Labels = mixedMoment B raw22633step2 raw22633step2Labels := by
      have ha : raw22633step2 = (fun i j => raw22633step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22633step2 raw22633step1; decide +kernel
      have hl : raw22633step2Labels = raw22633step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22633step1 raw22633step1Labels permutation8 permutation6
    _ = mixedMoment B node1050 node1050Labels := by rfl

def raw22634 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22634 raw22634Labels = mixedMoment B node1220 node1220Labels := by
  calc
    mixedMoment B raw22634 raw22634Labels = mixedMoment B raw22634step0 raw22634step0Labels := by
      have hz : ∀ j, raw22634 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22634step0 = (fun i j => raw22634 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22634step0 raw22634; decide +kernel
      have hl : raw22634step0Labels = raw22634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22634 raw22634Labels permutation434 hz
    mixedMoment B raw22634step0 raw22634step0Labels = mixedMoment B raw22634step1 raw22634step1Labels := by
      have ha : raw22634step1 = (fun i j => raw22634step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22634step1 raw22634step0; decide +kernel
      have hl : raw22634step1Labels = raw22634step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22634step0 raw22634step0Labels permutation38 permutation6
    _ = mixedMoment B node1220 node1220Labels := by rfl

def raw22635 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22635step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22635 raw22635Labels = mixedMoment B node1220 node1220Labels := by
  calc
    mixedMoment B raw22635 raw22635Labels = mixedMoment B raw22635step0 raw22635step0Labels := by
      have hz : ∀ j, raw22635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22635step0 = (fun i j => raw22635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22635step0 raw22635; decide +kernel
      have hl : raw22635step0Labels = raw22635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22635 raw22635Labels permutation346 hz
    mixedMoment B raw22635step0 raw22635step0Labels = mixedMoment B raw22635step1 raw22635step1Labels := by
      have ha : raw22635step1 = (fun i j => raw22635step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22635step1 raw22635step0; decide +kernel
      have hl : raw22635step1Labels = raw22635step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22635step0 raw22635step0Labels permutation38 permutation6
    _ = mixedMoment B node1220 node1220Labels := by rfl

def raw22636 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22636step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22636 raw22636Labels = mixedMoment B node1274 node1274Labels := by
  calc
    mixedMoment B raw22636 raw22636Labels = mixedMoment B raw22636step0 raw22636step0Labels := by
      have hz : ∀ j, raw22636 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22636step0 = (fun i j => raw22636 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22636step0 raw22636; decide +kernel
      have hl : raw22636step0Labels = raw22636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22636 raw22636Labels permutation434 hz
    mixedMoment B raw22636step0 raw22636step0Labels = mixedMoment B raw22636step1 raw22636step1Labels := by
      have hz : ∀ j, raw22636step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22636step1 = (fun i j => raw22636step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22636step1 raw22636step0; decide +kernel
      have hl : raw22636step1Labels = raw22636step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22636step0 raw22636step0Labels permutation80 hz
    mixedMoment B raw22636step1 raw22636step1Labels = mixedMoment B raw22636step2 raw22636step2Labels := by
      have ha : raw22636step2 = (fun i j => raw22636step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22636step2 raw22636step1; decide +kernel
      have hl : raw22636step2Labels = raw22636step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22636step1 raw22636step1Labels permutation9 permutation6
    _ = mixedMoment B node1274 node1274Labels := by rfl

def raw22637 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22637step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22637 raw22637Labels = mixedMoment B node1050 node1050Labels := by
  calc
    mixedMoment B raw22637 raw22637Labels = mixedMoment B raw22637step0 raw22637step0Labels := by
      have hz : ∀ j, raw22637 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22637step0 = (fun i j => raw22637 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22637step0 raw22637; decide +kernel
      have hl : raw22637step0Labels = raw22637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22637 raw22637Labels permutation434 hz
    mixedMoment B raw22637step0 raw22637step0Labels = mixedMoment B raw22637step1 raw22637step1Labels := by
      have hz : ∀ j, raw22637step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22637step1 = (fun i j => raw22637step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22637step1 raw22637step0; decide +kernel
      have hl : raw22637step1Labels = raw22637step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22637step0 raw22637step0Labels permutation56 hz
    mixedMoment B raw22637step1 raw22637step1Labels = mixedMoment B raw22637step2 raw22637step2Labels := by
      have ha : raw22637step2 = (fun i j => raw22637step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22637step2 raw22637step1; decide +kernel
      have hl : raw22637step2Labels = raw22637step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22637step1 raw22637step1Labels permutation8 permutation6
    _ = mixedMoment B node1050 node1050Labels := by rfl

def raw22638 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22638 raw22638Labels = mixedMoment B node1220 node1220Labels := by
  calc
    mixedMoment B raw22638 raw22638Labels = mixedMoment B raw22638step0 raw22638step0Labels := by
      have hz : ∀ j, raw22638 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22638step0 = (fun i j => raw22638 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22638step0 raw22638; decide +kernel
      have hl : raw22638step0Labels = raw22638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22638 raw22638Labels permutation434 hz
    mixedMoment B raw22638step0 raw22638step0Labels = mixedMoment B raw22638step1 raw22638step1Labels := by
      have ha : raw22638step1 = (fun i j => raw22638step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22638step1 raw22638step0; decide +kernel
      have hl : raw22638step1Labels = raw22638step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22638step0 raw22638step0Labels permutation32 permutation6
    _ = mixedMoment B node1220 node1220Labels := by rfl

def raw22639 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22639 raw22639Labels = mixedMoment B node1220 node1220Labels := by
  calc
    mixedMoment B raw22639 raw22639Labels = mixedMoment B raw22639step0 raw22639step0Labels := by
      have hz : ∀ j, raw22639 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22639step0 = (fun i j => raw22639 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22639step0 raw22639; decide +kernel
      have hl : raw22639step0Labels = raw22639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22639 raw22639Labels permutation265 hz
    mixedMoment B raw22639step0 raw22639step0Labels = mixedMoment B raw22639step1 raw22639step1Labels := by
      have ha : raw22639step1 = (fun i j => raw22639step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22639step1 raw22639step0; decide +kernel
      have hl : raw22639step1Labels = raw22639step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22639step0 raw22639step0Labels permutation38 permutation6
    _ = mixedMoment B node1220 node1220Labels := by rfl

def raw22640 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22640step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22640 raw22640Labels = mixedMoment B node1274 node1274Labels := by
  calc
    mixedMoment B raw22640 raw22640Labels = mixedMoment B raw22640step0 raw22640step0Labels := by
      have hz : ∀ j, raw22640 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22640step0 = (fun i j => raw22640 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22640step0 raw22640; decide +kernel
      have hl : raw22640step0Labels = raw22640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22640 raw22640Labels permutation434 hz
    mixedMoment B raw22640step0 raw22640step0Labels = mixedMoment B raw22640step1 raw22640step1Labels := by
      have hz : ∀ j, raw22640step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22640step1 = (fun i j => raw22640step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22640step1 raw22640step0; decide +kernel
      have hl : raw22640step1Labels = raw22640step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22640step0 raw22640step0Labels permutation56 hz
    mixedMoment B raw22640step1 raw22640step1Labels = mixedMoment B raw22640step2 raw22640step2Labels := by
      have ha : raw22640step2 = (fun i j => raw22640step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22640step2 raw22640step1; decide +kernel
      have hl : raw22640step2Labels = raw22640step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22640step1 raw22640step1Labels permutation9 permutation6
    _ = mixedMoment B node1274 node1274Labels := by rfl

def raw22641 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22641step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22641step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22641 raw22641Labels = mixedMoment B node1050 node1050Labels := by
  calc
    mixedMoment B raw22641 raw22641Labels = mixedMoment B raw22641step0 raw22641step0Labels := by
      have hz : ∀ j, raw22641 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22641step0 = (fun i j => raw22641 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22641step0 raw22641; decide +kernel
      have hl : raw22641step0Labels = raw22641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22641 raw22641Labels permutation346 hz
    mixedMoment B raw22641step0 raw22641step0Labels = mixedMoment B raw22641step1 raw22641step1Labels := by
      have hz : ∀ j, raw22641step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22641step1 = (fun i j => raw22641step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22641step1 raw22641step0; decide +kernel
      have hl : raw22641step1Labels = raw22641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22641step0 raw22641step0Labels permutation56 hz
    mixedMoment B raw22641step1 raw22641step1Labels = mixedMoment B raw22641step2 raw22641step2Labels := by
      have ha : raw22641step2 = (fun i j => raw22641step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22641step2 raw22641step1; decide +kernel
      have hl : raw22641step2Labels = raw22641step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22641step1 raw22641step1Labels permutation8 permutation6
    _ = mixedMoment B node1050 node1050Labels := by rfl

def raw22642 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22642step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22642 raw22642Labels = mixedMoment B node1220 node1220Labels := by
  calc
    mixedMoment B raw22642 raw22642Labels = mixedMoment B raw22642step0 raw22642step0Labels := by
      have hz : ∀ j, raw22642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22642step0 = (fun i j => raw22642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22642step0 raw22642; decide +kernel
      have hl : raw22642step0Labels = raw22642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22642 raw22642Labels permutation346 hz
    mixedMoment B raw22642step0 raw22642step0Labels = mixedMoment B raw22642step1 raw22642step1Labels := by
      have ha : raw22642step1 = (fun i j => raw22642step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22642step1 raw22642step0; decide +kernel
      have hl : raw22642step1Labels = raw22642step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22642step0 raw22642step0Labels permutation32 permutation6
    _ = mixedMoment B node1220 node1220Labels := by rfl

def raw22643 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22643step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22643 raw22643Labels = mixedMoment B node1220 node1220Labels := by
  calc
    mixedMoment B raw22643 raw22643Labels = mixedMoment B raw22643step0 raw22643step0Labels := by
      have hz : ∀ j, raw22643 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22643step0 = (fun i j => raw22643 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22643step0 raw22643; decide +kernel
      have hl : raw22643step0Labels = raw22643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22643 raw22643Labels permutation265 hz
    mixedMoment B raw22643step0 raw22643step0Labels = mixedMoment B raw22643step1 raw22643step1Labels := by
      have ha : raw22643step1 = (fun i j => raw22643step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22643step1 raw22643step0; decide +kernel
      have hl : raw22643step1Labels = raw22643step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22643step0 raw22643step0Labels permutation32 permutation6
    _ = mixedMoment B node1220 node1220Labels := by rfl

def raw22644 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22644step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22644step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22644step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22644step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22644 raw22644Labels = mixedMoment B node1274 node1274Labels := by
  calc
    mixedMoment B raw22644 raw22644Labels = mixedMoment B raw22644step0 raw22644step0Labels := by
      have hz : ∀ j, raw22644 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22644step0 = (fun i j => raw22644 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22644step0 raw22644; decide +kernel
      have hl : raw22644step0Labels = raw22644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22644 raw22644Labels permutation346 hz
    mixedMoment B raw22644step0 raw22644step0Labels = mixedMoment B raw22644step1 raw22644step1Labels := by
      have hz : ∀ j, raw22644step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22644step1 = (fun i j => raw22644step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22644step1 raw22644step0; decide +kernel
      have hl : raw22644step1Labels = raw22644step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22644step0 raw22644step0Labels permutation56 hz
    mixedMoment B raw22644step1 raw22644step1Labels = mixedMoment B raw22644step2 raw22644step2Labels := by
      have ha : raw22644step2 = (fun i j => raw22644step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22644step2 raw22644step1; decide +kernel
      have hl : raw22644step2Labels = raw22644step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22644step1 raw22644step1Labels permutation9 permutation6
    _ = mixedMoment B node1274 node1274Labels := by rfl

def raw22645 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22645step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22645step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, -2, 2], ![-1, -1, 2]]
def raw22645step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22645step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22645step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22645 raw22645Labels = mixedMoment B node1095 node1095Labels := by
  calc
    mixedMoment B raw22645 raw22645Labels = mixedMoment B raw22645step0 raw22645step0Labels := by
      have hz : ∀ j, raw22645 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22645step0 = (fun i j => raw22645 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22645step0 raw22645; decide +kernel
      have hl : raw22645step0Labels = raw22645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22645 raw22645Labels permutation434 hz
    mixedMoment B raw22645step0 raw22645step0Labels = mixedMoment B raw22645step1 raw22645step1Labels := by
      have hz : ∀ j, raw22645step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22645step1 = (fun i j => raw22645step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22645step1 raw22645step0; decide +kernel
      have hl : raw22645step1Labels = raw22645step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22645step0 raw22645step0Labels permutation80 hz
    mixedMoment B raw22645step1 raw22645step1Labels = mixedMoment B raw22645step2 raw22645step2Labels := by
      have hz : ∀ j, raw22645step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22645step2 = (fun i j => raw22645step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22645step2 raw22645step1; decide +kernel
      have hl : raw22645step2Labels = raw22645step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22645step1 raw22645step1Labels permutation14 hz
    mixedMoment B raw22645step2 raw22645step2Labels = mixedMoment B raw22645step3 raw22645step3Labels := by
      have ha : raw22645step3 = (fun i j => raw22645step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22645step3 raw22645step2; decide +kernel
      have hl : raw22645step3Labels = raw22645step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22645step2 raw22645step2Labels permutation3 permutation6
    _ = mixedMoment B node1095 node1095Labels := by rfl

def raw22646 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22646step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22646 raw22646Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw22646 raw22646Labels = mixedMoment B raw22646step0 raw22646step0Labels := by
      have hz : ∀ j, raw22646 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22646step0 = (fun i j => raw22646 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22646step0 raw22646; decide +kernel
      have hl : raw22646step0Labels = raw22646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22646 raw22646Labels permutation434 hz
    mixedMoment B raw22646step0 raw22646step0Labels = mixedMoment B raw22646step1 raw22646step1Labels := by
      have hz : ∀ j, raw22646step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22646step1 = (fun i j => raw22646step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22646step1 raw22646step0; decide +kernel
      have hl : raw22646step1Labels = raw22646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22646step0 raw22646step0Labels permutation80 hz
    mixedMoment B raw22646step1 raw22646step1Labels = mixedMoment B raw22646step2 raw22646step2Labels := by
      have ha : raw22646step2 = (fun i j => raw22646step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22646step2 raw22646step1; decide +kernel
      have hl : raw22646step2Labels = raw22646step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22646step1 raw22646step1Labels permutation9 permutation6
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw22647 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22647step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22647step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22647 raw22647Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw22647 raw22647Labels = mixedMoment B raw22647step0 raw22647step0Labels := by
      have hz : ∀ j, raw22647 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22647step0 = (fun i j => raw22647 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22647step0 raw22647; decide +kernel
      have hl : raw22647step0Labels = raw22647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22647 raw22647Labels permutation434 hz
    mixedMoment B raw22647step0 raw22647step0Labels = mixedMoment B raw22647step1 raw22647step1Labels := by
      have hz : ∀ j, raw22647step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22647step1 = (fun i j => raw22647step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22647step1 raw22647step0; decide +kernel
      have hl : raw22647step1Labels = raw22647step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22647step0 raw22647step0Labels permutation56 hz
    mixedMoment B raw22647step1 raw22647step1Labels = mixedMoment B raw22647step2 raw22647step2Labels := by
      have ha : raw22647step2 = (fun i j => raw22647step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22647step2 raw22647step1; decide +kernel
      have hl : raw22647step2Labels = raw22647step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22647step1 raw22647step1Labels permutation9 permutation6
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw22648 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22648step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22648 raw22648Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw22648 raw22648Labels = mixedMoment B raw22648step0 raw22648step0Labels := by
      have hz : ∀ j, raw22648 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22648step0 = (fun i j => raw22648 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22648step0 raw22648; decide +kernel
      have hl : raw22648step0Labels = raw22648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22648 raw22648Labels permutation346 hz
    mixedMoment B raw22648step0 raw22648step0Labels = mixedMoment B raw22648step1 raw22648step1Labels := by
      have hz : ∀ j, raw22648step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22648step1 = (fun i j => raw22648step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22648step1 raw22648step0; decide +kernel
      have hl : raw22648step1Labels = raw22648step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22648step0 raw22648step0Labels permutation56 hz
    mixedMoment B raw22648step1 raw22648step1Labels = mixedMoment B raw22648step2 raw22648step2Labels := by
      have ha : raw22648step2 = (fun i j => raw22648step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22648step2 raw22648step1; decide +kernel
      have hl : raw22648step2Labels = raw22648step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22648step1 raw22648step1Labels permutation9 permutation6
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw22649 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22649step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22649step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -2, 2], ![-2, 0, 2]]
def raw22649step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22649step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw22649step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22649 raw22649Labels = mixedMoment B node1311 node1311Labels := by
  calc
    mixedMoment B raw22649 raw22649Labels = mixedMoment B raw22649step0 raw22649step0Labels := by
      have hz : ∀ j, raw22649 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22649step0 = (fun i j => raw22649 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22649step0 raw22649; decide +kernel
      have hl : raw22649step0Labels = raw22649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22649 raw22649Labels permutation434 hz
    mixedMoment B raw22649step0 raw22649step0Labels = mixedMoment B raw22649step1 raw22649step1Labels := by
      have hz : ∀ j, raw22649step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22649step1 = (fun i j => raw22649step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22649step1 raw22649step0; decide +kernel
      have hl : raw22649step1Labels = raw22649step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22649step0 raw22649step0Labels permutation80 hz
    mixedMoment B raw22649step1 raw22649step1Labels = mixedMoment B raw22649step2 raw22649step2Labels := by
      have hz : ∀ j, raw22649step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22649step2 = (fun i j => raw22649step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22649step2 raw22649step1; decide +kernel
      have hl : raw22649step2Labels = raw22649step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22649step1 raw22649step1Labels permutation14 hz
    mixedMoment B raw22649step2 raw22649step2Labels = mixedMoment B raw22649step3 raw22649step3Labels := by
      have ha : raw22649step3 = (fun i j => raw22649step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22649step3 raw22649step2; decide +kernel
      have hl : raw22649step3Labels = raw22649step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22649step2 raw22649step2Labels permutation3 permutation6
    _ = mixedMoment B node1311 node1311Labels := by rfl

def raw22650 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22650step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22650step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 0, 2], ![0, -2, 2]]
def raw22650step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22650step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw22650step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22650 raw22650Labels = mixedMoment B node1311 node1311Labels := by
  calc
    mixedMoment B raw22650 raw22650Labels = mixedMoment B raw22650step0 raw22650step0Labels := by
      have hz : ∀ j, raw22650 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22650step0 = (fun i j => raw22650 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22650step0 raw22650; decide +kernel
      have hl : raw22650step0Labels = raw22650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22650 raw22650Labels permutation434 hz
    mixedMoment B raw22650step0 raw22650step0Labels = mixedMoment B raw22650step1 raw22650step1Labels := by
      have hz : ∀ j, raw22650step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22650step1 = (fun i j => raw22650step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22650step1 raw22650step0; decide +kernel
      have hl : raw22650step1Labels = raw22650step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22650step0 raw22650step0Labels permutation80 hz
    mixedMoment B raw22650step1 raw22650step1Labels = mixedMoment B raw22650step2 raw22650step2Labels := by
      have hz : ∀ j, raw22650step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22650step2 = (fun i j => raw22650step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22650step2 raw22650step1; decide +kernel
      have hl : raw22650step2Labels = raw22650step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22650step1 raw22650step1Labels permutation14 hz
    mixedMoment B raw22650step2 raw22650step2Labels = mixedMoment B raw22650step3 raw22650step3Labels := by
      have ha : raw22650step3 = (fun i j => raw22650step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22650step3 raw22650step2; decide +kernel
      have hl : raw22650step3Labels = raw22650step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22650step2 raw22650step2Labels permutation2 permutation6
    _ = mixedMoment B node1311 node1311Labels := by rfl

def raw22651 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22651step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22651step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22651step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22651 raw22651Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw22651 raw22651Labels = mixedMoment B raw22651step0 raw22651step0Labels := by
      have hz : ∀ j, raw22651 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22651step0 = (fun i j => raw22651 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22651step0 raw22651; decide +kernel
      have hl : raw22651step0Labels = raw22651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22651 raw22651Labels permutation434 hz
    mixedMoment B raw22651step0 raw22651step0Labels = mixedMoment B raw22651step1 raw22651step1Labels := by
      have hz : ∀ j, raw22651step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22651step1 = (fun i j => raw22651step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22651step1 raw22651step0; decide +kernel
      have hl : raw22651step1Labels = raw22651step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22651step0 raw22651step0Labels permutation56 hz
    mixedMoment B raw22651step1 raw22651step1Labels = mixedMoment B raw22651step2 raw22651step2Labels := by
      have ha : raw22651step2 = -raw22651step1 := by apply Matrix.ext; change ∀ i j, raw22651step2 i j = -(raw22651step1 i j); unfold raw22651step2 raw22651step1; decide +kernel
      have hl : raw22651step2Labels = raw22651step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1751 node1751Labels := by rfl

def raw22652 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22652Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22652step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22652step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22652step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22652 raw22652Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw22652 raw22652Labels = mixedMoment B raw22652step0 raw22652step0Labels := by
      have hz : ∀ j, raw22652 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22652step0 = (fun i j => raw22652 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22652step0 raw22652; decide +kernel
      have hl : raw22652step0Labels = raw22652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22652 raw22652Labels permutation346 hz
    mixedMoment B raw22652step0 raw22652step0Labels = mixedMoment B raw22652step1 raw22652step1Labels := by
      have hz : ∀ j, raw22652step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22652step1 = (fun i j => raw22652step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22652step1 raw22652step0; decide +kernel
      have hl : raw22652step1Labels = raw22652step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22652step0 raw22652step0Labels permutation56 hz
    mixedMoment B raw22652step1 raw22652step1Labels = mixedMoment B raw22652step2 raw22652step2Labels := by
      have ha : raw22652step2 = -raw22652step1 := by apply Matrix.ext; change ∀ i j, raw22652step2 i j = -(raw22652step1 i j); unfold raw22652step2 raw22652step1; decide +kernel
      have hl : raw22652step2Labels = raw22652step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1751 node1751Labels := by rfl

def raw22653 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22653Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22653step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22653step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 0, 2], ![-1, -1, 2]]
def raw22653step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22653step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -1, 2], ![-2, 0, 2]]
def raw22653step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22653step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw22653step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22653 raw22653Labels = mixedMoment B node1755 node1755Labels := by
  calc
    mixedMoment B raw22653 raw22653Labels = mixedMoment B raw22653step0 raw22653step0Labels := by
      have hz : ∀ j, raw22653 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22653step0 = (fun i j => raw22653 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22653step0 raw22653; decide +kernel
      have hl : raw22653step0Labels = raw22653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22653 raw22653Labels permutation434 hz
    mixedMoment B raw22653step0 raw22653step0Labels = mixedMoment B raw22653step1 raw22653step1Labels := by
      have hz : ∀ j, raw22653step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22653step1 = (fun i j => raw22653step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22653step1 raw22653step0; decide +kernel
      have hl : raw22653step1Labels = raw22653step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22653step0 raw22653step0Labels permutation80 hz
    mixedMoment B raw22653step1 raw22653step1Labels = mixedMoment B raw22653step2 raw22653step2Labels := by
      have hz : ∀ j, raw22653step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22653step2 = (fun i j => raw22653step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22653step2 raw22653step1; decide +kernel
      have hl : raw22653step2Labels = raw22653step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22653step1 raw22653step1Labels permutation14 hz
    mixedMoment B raw22653step2 raw22653step2Labels = mixedMoment B raw22653step3 raw22653step3Labels := by
      have ha : raw22653step3 = (fun i j => raw22653step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22653step3 raw22653step2; decide +kernel
      have hl : raw22653step3Labels = raw22653step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22653step2 raw22653step2Labels permutation3 permutation2
    mixedMoment B raw22653step3 raw22653step3Labels = mixedMoment B raw22653step4 raw22653step4Labels := by
      have ha : raw22653step4 = -raw22653step3 := by apply Matrix.ext; change ∀ i j, raw22653step4 i j = -(raw22653step3 i j); unfold raw22653step4 raw22653step3; decide +kernel
      have hl : raw22653step4Labels = raw22653step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1755 node1755Labels := by rfl

def raw22654 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22654step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22654step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -1, 2], ![-2, 0, 2]]
def raw22654step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22654step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![2, 0, -2]]
def raw22654step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22654 raw22654Labels = mixedMoment B node1755 node1755Labels := by
  calc
    mixedMoment B raw22654 raw22654Labels = mixedMoment B raw22654step0 raw22654step0Labels := by
      have hz : ∀ j, raw22654 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22654step0 = (fun i j => raw22654 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22654step0 raw22654; decide +kernel
      have hl : raw22654step0Labels = raw22654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22654 raw22654Labels permutation434 hz
    mixedMoment B raw22654step0 raw22654step0Labels = mixedMoment B raw22654step1 raw22654step1Labels := by
      have hz : ∀ j, raw22654step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22654step1 = (fun i j => raw22654step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22654step1 raw22654step0; decide +kernel
      have hl : raw22654step1Labels = raw22654step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22654step0 raw22654step0Labels permutation80 hz
    mixedMoment B raw22654step1 raw22654step1Labels = mixedMoment B raw22654step2 raw22654step2Labels := by
      have hz : ∀ j, raw22654step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22654step2 = (fun i j => raw22654step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22654step2 raw22654step1; decide +kernel
      have hl : raw22654step2Labels = raw22654step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22654step1 raw22654step1Labels permutation14 hz
    mixedMoment B raw22654step2 raw22654step2Labels = mixedMoment B raw22654step3 raw22654step3Labels := by
      have ha : raw22654step3 = -raw22654step2 := by apply Matrix.ext; change ∀ i j, raw22654step3 i j = -(raw22654step2 i j); unfold raw22654step3 raw22654step2; decide +kernel
      have hl : raw22654step3Labels = raw22654step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1755 node1755Labels := by rfl

def raw22655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22655step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22655 raw22655Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw22655 raw22655Labels = mixedMoment B raw22655step0 raw22655step0Labels := by
      have hz : ∀ j, raw22655 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22655step0 = (fun i j => raw22655 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22655step0 raw22655; decide +kernel
      have hl : raw22655step0Labels = raw22655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22655 raw22655Labels permutation346 hz
    mixedMoment B raw22655step0 raw22655step0Labels = mixedMoment B raw22655step1 raw22655step1Labels := by
      have hz : ∀ j, raw22655step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22655step1 = (fun i j => raw22655step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22655step1 raw22655step0; decide +kernel
      have hl : raw22655step1Labels = raw22655step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22655step0 raw22655step0Labels permutation56 hz
    _ = mixedMoment B node5275 node5275Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
