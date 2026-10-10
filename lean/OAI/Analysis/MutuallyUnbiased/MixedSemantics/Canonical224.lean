import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw28672 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw28672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw28672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw28672step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28672step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw28672step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28672 raw28672Labels = mixedMoment B node4809 node4809Labels := by
  calc
    mixedMoment B raw28672 raw28672Labels = mixedMoment B raw28672step0 raw28672step0Labels := by
      have hz : ∀ j, raw28672 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28672step0 = (fun i j => raw28672 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28672step0 raw28672; decide +kernel
      have hl : raw28672step0Labels = raw28672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28672 raw28672Labels permutation434 hz
    mixedMoment B raw28672step0 raw28672step0Labels = mixedMoment B raw28672step1 raw28672step1Labels := by
      have ha : raw28672step1 = (fun i j => raw28672step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28672step1 raw28672step0; decide +kernel
      have hl : raw28672step1Labels = raw28672step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28672step0 raw28672step0Labels permutation143 permutation4
    mixedMoment B raw28672step1 raw28672step1Labels = mixedMoment B raw28672step2 raw28672step2Labels := by
      have ha : raw28672step2 = raw28672step1 := by apply Matrix.ext; unfold raw28672step2 raw28672step1; decide +kernel
      have hl : raw28672step1Labels = labelEmbedding7 ∘ raw28672step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28672step1 raw28672step1Labels raw28672step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4809 node4809Labels := by rfl

def raw28673 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw28673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw28673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw28673step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw28673step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28673 raw28673Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw28673 raw28673Labels = mixedMoment B raw28673step0 raw28673step0Labels := by
      have hz : ∀ j, raw28673 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28673step0 = (fun i j => raw28673 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28673step0 raw28673; decide +kernel
      have hl : raw28673step0Labels = raw28673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28673 raw28673Labels permutation434 hz
    mixedMoment B raw28673step0 raw28673step0Labels = mixedMoment B raw28673step1 raw28673step1Labels := by
      have ha : raw28673step1 = (fun i j => raw28673step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28673step1 raw28673step0; decide +kernel
      have hl : raw28673step1Labels = raw28673step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28673step0 raw28673step0Labels permutation32 permutation6
    mixedMoment B raw28673step1 raw28673step1Labels = mixedMoment B raw28673step2 raw28673step2Labels := by
      have ha : raw28673step2 = raw28673step1 := by apply Matrix.ext; unfold raw28673step2 raw28673step1; decide +kernel
      have hl : raw28673step1Labels = labelEmbedding9 ∘ raw28673step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28673step1 raw28673step1Labels raw28673step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5147 node5147Labels := by rfl

def raw28674 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw28674step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw28674step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28674 raw28674Labels = mixedMoment B node4800 node4800Labels := by
  calc
    mixedMoment B raw28674 raw28674Labels = mixedMoment B raw28674step0 raw28674step0Labels := by
      have hz : ∀ j, raw28674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28674step0 = (fun i j => raw28674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28674step0 raw28674; decide +kernel
      have hl : raw28674step0Labels = raw28674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28674 raw28674Labels permutation346 hz
    mixedMoment B raw28674step0 raw28674step0Labels = mixedMoment B raw28674step1 raw28674step1Labels := by
      have ha : raw28674step1 = (fun i j => raw28674step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28674step1 raw28674step0; decide +kernel
      have hl : raw28674step1Labels = raw28674step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28674step0 raw28674step0Labels permutation143 permutation4
    mixedMoment B raw28674step1 raw28674step1Labels = mixedMoment B raw28674step2 raw28674step2Labels := by
      have ha : raw28674step2 = raw28674step1 := by apply Matrix.ext; unfold raw28674step2 raw28674step1; decide +kernel
      have hl : raw28674step1Labels = labelEmbedding7 ∘ raw28674step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28674step1 raw28674step1Labels raw28674step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4800 node4800Labels := by rfl

def raw28675 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28675step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28675step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28675 raw28675Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw28675 raw28675Labels = mixedMoment B raw28675step0 raw28675step0Labels := by
      have hz : ∀ j, raw28675 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28675step0 = (fun i j => raw28675 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28675step0 raw28675; decide +kernel
      have hl : raw28675step0Labels = raw28675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28675 raw28675Labels permutation346 hz
    mixedMoment B raw28675step0 raw28675step0Labels = mixedMoment B raw28675step1 raw28675step1Labels := by
      have ha : raw28675step1 = (fun i j => raw28675step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28675step1 raw28675step0; decide +kernel
      have hl : raw28675step1Labels = raw28675step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28675step0 raw28675step0Labels permutation145 permutation4
    mixedMoment B raw28675step1 raw28675step1Labels = mixedMoment B raw28675step2 raw28675step2Labels := by
      have ha : raw28675step2 = raw28675step1 := by apply Matrix.ext; unfold raw28675step2 raw28675step1; decide +kernel
      have hl : raw28675step1Labels = labelEmbedding7 ∘ raw28675step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28675step1 raw28675step1Labels raw28675step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4827 node4827Labels := by rfl

def raw28676 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28676step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28676step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28676 raw28676Labels = mixedMoment B node4797 node4797Labels := by
  calc
    mixedMoment B raw28676 raw28676Labels = mixedMoment B raw28676step0 raw28676step0Labels := by
      have ha : raw28676step0 = (fun i j => raw28676 (permutation654 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28676step0 raw28676; decide +kernel
      have hl : raw28676step0Labels = raw28676Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28676 raw28676Labels permutation654 permutation4
    mixedMoment B raw28676step0 raw28676step0Labels = mixedMoment B raw28676step1 raw28676step1Labels := by
      have ha : raw28676step1 = raw28676step0 := by apply Matrix.ext; unfold raw28676step1 raw28676step0; decide +kernel
      have hl : raw28676step0Labels = labelEmbedding7 ∘ raw28676step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28676step0 raw28676step0Labels raw28676step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4797 node4797Labels := by rfl

def raw28677 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw28677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw28677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw28677step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw28677step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28677 raw28677Labels = mixedMoment B node4809 node4809Labels := by
  calc
    mixedMoment B raw28677 raw28677Labels = mixedMoment B raw28677step0 raw28677step0Labels := by
      have hz : ∀ j, raw28677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28677step0 = (fun i j => raw28677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28677step0 raw28677; decide +kernel
      have hl : raw28677step0Labels = raw28677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28677 raw28677Labels permutation346 hz
    mixedMoment B raw28677step0 raw28677step0Labels = mixedMoment B raw28677step1 raw28677step1Labels := by
      have ha : raw28677step1 = (fun i j => raw28677step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28677step1 raw28677step0; decide +kernel
      have hl : raw28677step1Labels = raw28677step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28677step0 raw28677step0Labels permutation143 permutation4
    mixedMoment B raw28677step1 raw28677step1Labels = mixedMoment B raw28677step2 raw28677step2Labels := by
      have ha : raw28677step2 = raw28677step1 := by apply Matrix.ext; unfold raw28677step2 raw28677step1; decide +kernel
      have hl : raw28677step1Labels = labelEmbedding7 ∘ raw28677step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28677step1 raw28677step1Labels raw28677step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4809 node4809Labels := by rfl

def raw28678 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28678step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 0, 1], ![0, -3, 3]]
def raw28678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28678step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28678step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28678step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw28678step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28678 raw28678Labels = mixedMoment B node4837 node4837Labels := by
  calc
    mixedMoment B raw28678 raw28678Labels = mixedMoment B raw28678step0 raw28678step0Labels := by
      have hz : ∀ j, raw28678 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28678step0 = (fun i j => raw28678 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28678step0 raw28678; decide +kernel
      have hl : raw28678step0Labels = raw28678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28678 raw28678Labels permutation434 hz
    mixedMoment B raw28678step0 raw28678step0Labels = mixedMoment B raw28678step1 raw28678step1Labels := by
      have hz : ∀ j, raw28678step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28678step1 = (fun i j => raw28678step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28678step1 raw28678step0; decide +kernel
      have hl : raw28678step1Labels = raw28678step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28678step0 raw28678step0Labels permutation80 hz
    mixedMoment B raw28678step1 raw28678step1Labels = mixedMoment B raw28678step2 raw28678step2Labels := by
      have ha : raw28678step2 = (fun i j => raw28678step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28678step2 raw28678step1; decide +kernel
      have hl : raw28678step2Labels = raw28678step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28678step1 raw28678step1Labels permutation8 permutation6
    mixedMoment B raw28678step2 raw28678step2Labels = mixedMoment B raw28678step3 raw28678step3Labels := by
      have ha : raw28678step3 = raw28678step2 := by apply Matrix.ext; unfold raw28678step3 raw28678step2; decide +kernel
      have hl : raw28678step2Labels = labelEmbedding9 ∘ raw28678step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28678step2 raw28678step2Labels raw28678step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4837 node4837Labels := by rfl

def raw28679 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 0, 1], ![0, -3, 3]]
def raw28679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28679step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28679step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28679step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28679step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28679step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28679 raw28679Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw28679 raw28679Labels = mixedMoment B raw28679step0 raw28679step0Labels := by
      have hz : ∀ j, raw28679 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28679step0 = (fun i j => raw28679 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28679step0 raw28679; decide +kernel
      have hl : raw28679step0Labels = raw28679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28679 raw28679Labels permutation434 hz
    mixedMoment B raw28679step0 raw28679step0Labels = mixedMoment B raw28679step1 raw28679step1Labels := by
      have hz : ∀ j, raw28679step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28679step1 = (fun i j => raw28679step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28679step1 raw28679step0; decide +kernel
      have hl : raw28679step1Labels = raw28679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28679step0 raw28679step0Labels permutation80 hz
    mixedMoment B raw28679step1 raw28679step1Labels = mixedMoment B raw28679step2 raw28679step2Labels := by
      have ha : raw28679step2 = (fun i j => raw28679step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28679step2 raw28679step1; decide +kernel
      have hl : raw28679step2Labels = raw28679step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28679step1 raw28679step1Labels permutation31 permutation6
    mixedMoment B raw28679step2 raw28679step2Labels = mixedMoment B raw28679step3 raw28679step3Labels := by
      have ha : raw28679step3 = -raw28679step2 := by apply Matrix.ext; change ∀ i j, raw28679step3 i j = -(raw28679step2 i j); unfold raw28679step3 raw28679step2; decide +kernel
      have hl : raw28679step3Labels = raw28679step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28679step3 raw28679step3Labels = mixedMoment B raw28679step4 raw28679step4Labels := by
      have ha : raw28679step4 = raw28679step3 := by apply Matrix.ext; unfold raw28679step4 raw28679step3; decide +kernel
      have hl : raw28679step3Labels = labelEmbedding9 ∘ raw28679step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28679step3 raw28679step3Labels raw28679step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4841 node4841Labels := by rfl

def raw28680 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28680step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28680step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28680step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28680step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28680 raw28680Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw28680 raw28680Labels = mixedMoment B raw28680step0 raw28680step0Labels := by
      have hz : ∀ j, raw28680 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28680step0 = (fun i j => raw28680 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28680step0 raw28680; decide +kernel
      have hl : raw28680step0Labels = raw28680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28680 raw28680Labels permutation434 hz
    mixedMoment B raw28680step0 raw28680step0Labels = mixedMoment B raw28680step1 raw28680step1Labels := by
      have ha : raw28680step1 = (fun i j => raw28680step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28680step1 raw28680step0; decide +kernel
      have hl : raw28680step1Labels = raw28680step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28680step0 raw28680step0Labels permutation151 permutation6
    mixedMoment B raw28680step1 raw28680step1Labels = mixedMoment B raw28680step2 raw28680step2Labels := by
      have ha : raw28680step2 = -raw28680step1 := by apply Matrix.ext; change ∀ i j, raw28680step2 i j = -(raw28680step1 i j); unfold raw28680step2 raw28680step1; decide +kernel
      have hl : raw28680step2Labels = raw28680step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28680step2 raw28680step2Labels = mixedMoment B raw28680step3 raw28680step3Labels := by
      have ha : raw28680step3 = raw28680step2 := by apply Matrix.ext; unfold raw28680step3 raw28680step2; decide +kernel
      have hl : raw28680step2Labels = labelEmbedding9 ∘ raw28680step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28680step2 raw28680step2Labels raw28680step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw28681 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28681step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28681step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28681step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28681step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28681 raw28681Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw28681 raw28681Labels = mixedMoment B raw28681step0 raw28681step0Labels := by
      have hz : ∀ j, raw28681 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28681step0 = (fun i j => raw28681 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28681step0 raw28681; decide +kernel
      have hl : raw28681step0Labels = raw28681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28681 raw28681Labels permutation346 hz
    mixedMoment B raw28681step0 raw28681step0Labels = mixedMoment B raw28681step1 raw28681step1Labels := by
      have ha : raw28681step1 = (fun i j => raw28681step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28681step1 raw28681step0; decide +kernel
      have hl : raw28681step1Labels = raw28681step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28681step0 raw28681step0Labels permutation151 permutation6
    mixedMoment B raw28681step1 raw28681step1Labels = mixedMoment B raw28681step2 raw28681step2Labels := by
      have ha : raw28681step2 = -raw28681step1 := by apply Matrix.ext; change ∀ i j, raw28681step2 i j = -(raw28681step1 i j); unfold raw28681step2 raw28681step1; decide +kernel
      have hl : raw28681step2Labels = raw28681step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28681step2 raw28681step2Labels = mixedMoment B raw28681step3 raw28681step3Labels := by
      have ha : raw28681step3 = raw28681step2 := by apply Matrix.ext; unfold raw28681step3 raw28681step2; decide +kernel
      have hl : raw28681step2Labels = labelEmbedding9 ∘ raw28681step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28681step2 raw28681step2Labels raw28681step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw28682 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw28682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw28682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28682step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-2, 1, 1], ![1, -4, 3]]
def raw28682step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28682step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw28682step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28682step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw28682step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28682 raw28682Labels = mixedMoment B node4454 node4454Labels := by
  calc
    mixedMoment B raw28682 raw28682Labels = mixedMoment B raw28682step0 raw28682step0Labels := by
      have hz : ∀ j, raw28682 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28682step0 = (fun i j => raw28682 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28682step0 raw28682; decide +kernel
      have hl : raw28682step0Labels = raw28682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28682 raw28682Labels permutation434 hz
    mixedMoment B raw28682step0 raw28682step0Labels = mixedMoment B raw28682step1 raw28682step1Labels := by
      have hz : ∀ j, raw28682step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28682step1 = (fun i j => raw28682step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28682step1 raw28682step0; decide +kernel
      have hl : raw28682step1Labels = raw28682step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28682step0 raw28682step0Labels permutation80 hz
    mixedMoment B raw28682step1 raw28682step1Labels = mixedMoment B raw28682step2 raw28682step2Labels := by
      have ha : raw28682step2 = (fun i j => raw28682step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28682step2 raw28682step1; decide +kernel
      have hl : raw28682step2Labels = raw28682step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28682step1 raw28682step1Labels permutation29 permutation4
    mixedMoment B raw28682step2 raw28682step2Labels = mixedMoment B raw28682step3 raw28682step3Labels := by
      have ha : raw28682step3 = raw28682step2 := by apply Matrix.ext; unfold raw28682step3 raw28682step2; decide +kernel
      have hl : raw28682step2Labels = labelEmbedding7 ∘ raw28682step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28682step2 raw28682step2Labels raw28682step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4454 node4454Labels := by rfl

def raw28683 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw28683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw28683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-2, 1, 1], ![1, -4, 3]]
def raw28683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28683step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28683step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28683step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28683 raw28683Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw28683 raw28683Labels = mixedMoment B raw28683step0 raw28683step0Labels := by
      have hz : ∀ j, raw28683 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28683step0 = (fun i j => raw28683 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28683step0 raw28683; decide +kernel
      have hl : raw28683step0Labels = raw28683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28683 raw28683Labels permutation434 hz
    mixedMoment B raw28683step0 raw28683step0Labels = mixedMoment B raw28683step1 raw28683step1Labels := by
      have hz : ∀ j, raw28683step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28683step1 = (fun i j => raw28683step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28683step1 raw28683step0; decide +kernel
      have hl : raw28683step1Labels = raw28683step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28683step0 raw28683step0Labels permutation80 hz
    mixedMoment B raw28683step1 raw28683step1Labels = mixedMoment B raw28683step2 raw28683step2Labels := by
      have ha : raw28683step2 = (fun i j => raw28683step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28683step2 raw28683step1; decide +kernel
      have hl : raw28683step2Labels = raw28683step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28683step1 raw28683step1Labels permutation31 permutation4
    mixedMoment B raw28683step2 raw28683step2Labels = mixedMoment B raw28683step3 raw28683step3Labels := by
      have ha : raw28683step3 = raw28683step2 := by apply Matrix.ext; unfold raw28683step3 raw28683step2; decide +kernel
      have hl : raw28683step2Labels = labelEmbedding7 ∘ raw28683step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28683step2 raw28683step2Labels raw28683step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

def raw28684 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw28684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw28684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28684step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28684step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28684 raw28684Labels = mixedMoment B node4450 node4450Labels := by
  calc
    mixedMoment B raw28684 raw28684Labels = mixedMoment B raw28684step0 raw28684step0Labels := by
      have hz : ∀ j, raw28684 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28684step0 = (fun i j => raw28684 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28684step0 raw28684; decide +kernel
      have hl : raw28684step0Labels = raw28684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28684 raw28684Labels permutation434 hz
    mixedMoment B raw28684step0 raw28684step0Labels = mixedMoment B raw28684step1 raw28684step1Labels := by
      have ha : raw28684step1 = (fun i j => raw28684step0 (permutation139 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28684step1 raw28684step0; decide +kernel
      have hl : raw28684step1Labels = raw28684step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28684step0 raw28684step0Labels permutation139 permutation4
    mixedMoment B raw28684step1 raw28684step1Labels = mixedMoment B raw28684step2 raw28684step2Labels := by
      have ha : raw28684step2 = raw28684step1 := by apply Matrix.ext; unfold raw28684step2 raw28684step1; decide +kernel
      have hl : raw28684step1Labels = labelEmbedding7 ∘ raw28684step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28684step1 raw28684step1Labels raw28684step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4450 node4450Labels := by rfl

def raw28685 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw28685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw28685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28685step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw28685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28685 raw28685Labels = mixedMoment B node4450 node4450Labels := by
  calc
    mixedMoment B raw28685 raw28685Labels = mixedMoment B raw28685step0 raw28685step0Labels := by
      have hz : ∀ j, raw28685 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28685step0 = (fun i j => raw28685 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28685step0 raw28685; decide +kernel
      have hl : raw28685step0Labels = raw28685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28685 raw28685Labels permutation346 hz
    mixedMoment B raw28685step0 raw28685step0Labels = mixedMoment B raw28685step1 raw28685step1Labels := by
      have ha : raw28685step1 = (fun i j => raw28685step0 (permutation139 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28685step1 raw28685step0; decide +kernel
      have hl : raw28685step1Labels = raw28685step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28685step0 raw28685step0Labels permutation139 permutation4
    mixedMoment B raw28685step1 raw28685step1Labels = mixedMoment B raw28685step2 raw28685step2Labels := by
      have ha : raw28685step2 = raw28685step1 := by apply Matrix.ext; unfold raw28685step2 raw28685step1; decide +kernel
      have hl : raw28685step1Labels = labelEmbedding7 ∘ raw28685step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28685step1 raw28685step1Labels raw28685step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4450 node4450Labels := by rfl

def raw28686 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw28686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw28686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-3, 2, 1], ![1, -4, 3]]
def raw28686step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw28686step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28686step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw28686step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28686 raw28686Labels = mixedMoment B node4465 node4465Labels := by
  calc
    mixedMoment B raw28686 raw28686Labels = mixedMoment B raw28686step0 raw28686step0Labels := by
      have hz : ∀ j, raw28686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28686step0 = (fun i j => raw28686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28686step0 raw28686; decide +kernel
      have hl : raw28686step0Labels = raw28686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28686 raw28686Labels permutation434 hz
    mixedMoment B raw28686step0 raw28686step0Labels = mixedMoment B raw28686step1 raw28686step1Labels := by
      have hz : ∀ j, raw28686step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28686step1 = (fun i j => raw28686step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28686step1 raw28686step0; decide +kernel
      have hl : raw28686step1Labels = raw28686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28686step0 raw28686step0Labels permutation80 hz
    mixedMoment B raw28686step1 raw28686step1Labels = mixedMoment B raw28686step2 raw28686step2Labels := by
      have ha : raw28686step2 = (fun i j => raw28686step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28686step2 raw28686step1; decide +kernel
      have hl : raw28686step2Labels = raw28686step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28686step1 raw28686step1Labels permutation29 permutation4
    mixedMoment B raw28686step2 raw28686step2Labels = mixedMoment B raw28686step3 raw28686step3Labels := by
      have ha : raw28686step3 = raw28686step2 := by apply Matrix.ext; unfold raw28686step3 raw28686step2; decide +kernel
      have hl : raw28686step2Labels = labelEmbedding7 ∘ raw28686step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28686step2 raw28686step2Labels raw28686step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4465 node4465Labels := by rfl

def raw28687 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28687Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28687step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28687step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-2, 1, 1], ![0, -3, 3]]
def raw28687step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28687step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28687step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28687step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28687step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28687 raw28687Labels = mixedMoment B node2602 node2602Labels := by
  calc
    mixedMoment B raw28687 raw28687Labels = mixedMoment B raw28687step0 raw28687step0Labels := by
      have hz : ∀ j, raw28687 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28687step0 = (fun i j => raw28687 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28687step0 raw28687; decide +kernel
      have hl : raw28687step0Labels = raw28687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28687 raw28687Labels permutation434 hz
    mixedMoment B raw28687step0 raw28687step0Labels = mixedMoment B raw28687step1 raw28687step1Labels := by
      have hz : ∀ j, raw28687step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28687step1 = (fun i j => raw28687step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28687step1 raw28687step0; decide +kernel
      have hl : raw28687step1Labels = raw28687step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28687step0 raw28687step0Labels permutation80 hz
    mixedMoment B raw28687step1 raw28687step1Labels = mixedMoment B raw28687step2 raw28687step2Labels := by
      have ha : raw28687step2 = (fun i j => raw28687step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28687step2 raw28687step1; decide +kernel
      have hl : raw28687step2Labels = raw28687step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28687step1 raw28687step1Labels permutation8 permutation7
    mixedMoment B raw28687step2 raw28687step2Labels = mixedMoment B raw28687step3 raw28687step3Labels := by
      have ha : raw28687step3 = raw28687step2 := by apply Matrix.ext; unfold raw28687step3 raw28687step2; decide +kernel
      have hl : raw28687step2Labels = labelEmbedding1 ∘ raw28687step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28687step2 raw28687step2Labels raw28687step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2602 node2602Labels := by rfl

def raw28688 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28688Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28688step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28688step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28688step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28688 raw28688Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw28688 raw28688Labels = mixedMoment B raw28688step0 raw28688step0Labels := by
      have hz : ∀ j, raw28688 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28688step0 = (fun i j => raw28688 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28688step0 raw28688; decide +kernel
      have hl : raw28688step0Labels = raw28688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28688 raw28688Labels permutation434 hz
    mixedMoment B raw28688step0 raw28688step0Labels = mixedMoment B raw28688step1 raw28688step1Labels := by
      have ha : raw28688step1 = (fun i j => raw28688step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28688step1 raw28688step0; decide +kernel
      have hl : raw28688step1Labels = raw28688step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28688step0 raw28688step0Labels permutation32 permutation7
    mixedMoment B raw28688step1 raw28688step1Labels = mixedMoment B raw28688step2 raw28688step2Labels := by
      have ha : raw28688step2 = raw28688step1 := by apply Matrix.ext; unfold raw28688step2 raw28688step1; decide +kernel
      have hl : raw28688step1Labels = labelEmbedding1 ∘ raw28688step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28688step1 raw28688step1Labels raw28688step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2486 node2486Labels := by rfl

def raw28689 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28689Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28689step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28689step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28689step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28689 raw28689Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw28689 raw28689Labels = mixedMoment B raw28689step0 raw28689step0Labels := by
      have hz : ∀ j, raw28689 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28689step0 = (fun i j => raw28689 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28689step0 raw28689; decide +kernel
      have hl : raw28689step0Labels = raw28689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28689 raw28689Labels permutation346 hz
    mixedMoment B raw28689step0 raw28689step0Labels = mixedMoment B raw28689step1 raw28689step1Labels := by
      have ha : raw28689step1 = (fun i j => raw28689step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28689step1 raw28689step0; decide +kernel
      have hl : raw28689step1Labels = raw28689step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28689step0 raw28689step0Labels permutation32 permutation7
    mixedMoment B raw28689step1 raw28689step1Labels = mixedMoment B raw28689step2 raw28689step2Labels := by
      have ha : raw28689step2 = raw28689step1 := by apply Matrix.ext; unfold raw28689step2 raw28689step1; decide +kernel
      have hl : raw28689step1Labels = labelEmbedding1 ∘ raw28689step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28689step1 raw28689step1Labels raw28689step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2486 node2486Labels := by rfl

def raw28690 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw28690Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw28690step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-3, 2, 1], ![0, -3, 3]]
def raw28690step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw28690step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw28690step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28690 raw28690Labels = mixedMoment B node2520 node2520Labels := by
  calc
    mixedMoment B raw28690 raw28690Labels = mixedMoment B raw28690step0 raw28690step0Labels := by
      have hz : ∀ j, raw28690 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28690step0 = (fun i j => raw28690 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28690step0 raw28690; decide +kernel
      have hl : raw28690step0Labels = raw28690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28690 raw28690Labels permutation434 hz
    mixedMoment B raw28690step0 raw28690step0Labels = mixedMoment B raw28690step1 raw28690step1Labels := by
      have hz : ∀ j, raw28690step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28690step1 = (fun i j => raw28690step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28690step1 raw28690step0; decide +kernel
      have hl : raw28690step1Labels = raw28690step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28690step0 raw28690step0Labels permutation80 hz
    mixedMoment B raw28690step1 raw28690step1Labels = mixedMoment B raw28690step2 raw28690step2Labels := by
      have ha : raw28690step2 = (fun i j => raw28690step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28690step2 raw28690step1; decide +kernel
      have hl : raw28690step2Labels = raw28690step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28690step1 raw28690step1Labels permutation8 permutation7
    mixedMoment B raw28690step2 raw28690step2Labels = mixedMoment B raw28690step3 raw28690step3Labels := by
      have ha : raw28690step3 = raw28690step2 := by apply Matrix.ext; unfold raw28690step3 raw28690step2; decide +kernel
      have hl : raw28690step2Labels = labelEmbedding1 ∘ raw28690step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28690step2 raw28690step2Labels raw28690step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2520 node2520Labels := by rfl

def raw28691 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw28691Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw28691step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28691step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 1, 1], ![-1, -2, 3]]
def raw28691step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28691step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw28691step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28691step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw28691step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28691 raw28691Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw28691 raw28691Labels = mixedMoment B raw28691step0 raw28691step0Labels := by
      have hz : ∀ j, raw28691 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28691step0 = (fun i j => raw28691 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28691step0 raw28691; decide +kernel
      have hl : raw28691step0Labels = raw28691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28691 raw28691Labels permutation434 hz
    mixedMoment B raw28691step0 raw28691step0Labels = mixedMoment B raw28691step1 raw28691step1Labels := by
      have hz : ∀ j, raw28691step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28691step1 = (fun i j => raw28691step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28691step1 raw28691step0; decide +kernel
      have hl : raw28691step1Labels = raw28691step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28691step0 raw28691step0Labels permutation80 hz
    mixedMoment B raw28691step1 raw28691step1Labels = mixedMoment B raw28691step2 raw28691step2Labels := by
      have ha : raw28691step2 = (fun i j => raw28691step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28691step2 raw28691step1; decide +kernel
      have hl : raw28691step2Labels = raw28691step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28691step1 raw28691step1Labels permutation8 permutation7
    mixedMoment B raw28691step2 raw28691step2Labels = mixedMoment B raw28691step3 raw28691step3Labels := by
      have ha : raw28691step3 = raw28691step2 := by apply Matrix.ext; unfold raw28691step3 raw28691step2; decide +kernel
      have hl : raw28691step2Labels = labelEmbedding1 ∘ raw28691step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28691step2 raw28691step2Labels raw28691step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw28692 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28692Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28692step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 1, 1], ![0, -3, 3]]
def raw28692step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28692step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -3, 0]]
def raw28692step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28692step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -3, 0]]
def raw28692step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28692 raw28692Labels = mixedMoment B node3186 node3186Labels := by
  calc
    mixedMoment B raw28692 raw28692Labels = mixedMoment B raw28692step0 raw28692step0Labels := by
      have hz : ∀ j, raw28692 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28692step0 = (fun i j => raw28692 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28692step0 raw28692; decide +kernel
      have hl : raw28692step0Labels = raw28692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28692 raw28692Labels permutation434 hz
    mixedMoment B raw28692step0 raw28692step0Labels = mixedMoment B raw28692step1 raw28692step1Labels := by
      have hz : ∀ j, raw28692step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28692step1 = (fun i j => raw28692step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28692step1 raw28692step0; decide +kernel
      have hl : raw28692step1Labels = raw28692step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28692step0 raw28692step0Labels permutation80 hz
    mixedMoment B raw28692step1 raw28692step1Labels = mixedMoment B raw28692step2 raw28692step2Labels := by
      have ha : raw28692step2 = (fun i j => raw28692step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28692step2 raw28692step1; decide +kernel
      have hl : raw28692step2Labels = raw28692step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28692step1 raw28692step1Labels permutation29 permutation5
    mixedMoment B raw28692step2 raw28692step2Labels = mixedMoment B raw28692step3 raw28692step3Labels := by
      have ha : raw28692step3 = raw28692step2 := by apply Matrix.ext; unfold raw28692step3 raw28692step2; decide +kernel
      have hl : raw28692step2Labels = labelEmbedding1 ∘ raw28692step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28692step2 raw28692step2Labels raw28692step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3186 node3186Labels := by rfl

def raw28693 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28693Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28693step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28693step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28693step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28693step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28693 raw28693Labels = mixedMoment B node2866 node2866Labels := by
  calc
    mixedMoment B raw28693 raw28693Labels = mixedMoment B raw28693step0 raw28693step0Labels := by
      have hz : ∀ j, raw28693 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28693step0 = (fun i j => raw28693 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28693step0 raw28693; decide +kernel
      have hl : raw28693step0Labels = raw28693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28693 raw28693Labels permutation434 hz
    mixedMoment B raw28693step0 raw28693step0Labels = mixedMoment B raw28693step1 raw28693step1Labels := by
      have ha : raw28693step1 = (fun i j => raw28693step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28693step1 raw28693step0; decide +kernel
      have hl : raw28693step1Labels = raw28693step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28693step0 raw28693step0Labels permutation32 permutation7
    mixedMoment B raw28693step1 raw28693step1Labels = mixedMoment B raw28693step2 raw28693step2Labels := by
      have ha : raw28693step2 = raw28693step1 := by apply Matrix.ext; unfold raw28693step2 raw28693step1; decide +kernel
      have hl : raw28693step1Labels = labelEmbedding1 ∘ raw28693step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28693step1 raw28693step1Labels raw28693step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2866 node2866Labels := by rfl

def raw28694 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28694Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28694step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28694step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28694step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28694 raw28694Labels = mixedMoment B node2866 node2866Labels := by
  calc
    mixedMoment B raw28694 raw28694Labels = mixedMoment B raw28694step0 raw28694step0Labels := by
      have hz : ∀ j, raw28694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28694step0 = (fun i j => raw28694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28694step0 raw28694; decide +kernel
      have hl : raw28694step0Labels = raw28694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28694 raw28694Labels permutation346 hz
    mixedMoment B raw28694step0 raw28694step0Labels = mixedMoment B raw28694step1 raw28694step1Labels := by
      have ha : raw28694step1 = (fun i j => raw28694step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28694step1 raw28694step0; decide +kernel
      have hl : raw28694step1Labels = raw28694step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28694step0 raw28694step0Labels permutation32 permutation7
    mixedMoment B raw28694step1 raw28694step1Labels = mixedMoment B raw28694step2 raw28694step2Labels := by
      have ha : raw28694step2 = raw28694step1 := by apply Matrix.ext; unfold raw28694step2 raw28694step1; decide +kernel
      have hl : raw28694step1Labels = labelEmbedding1 ∘ raw28694step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28694step1 raw28694step1Labels raw28694step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2866 node2866Labels := by rfl

def raw28695 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw28695Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw28695step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-3, 2, 1], ![0, -3, 3]]
def raw28695step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 2, -3], ![3, -3, 0]]
def raw28695step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28695step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 2, -3], ![3, -3, 0]]
def raw28695step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28695 raw28695Labels = mixedMoment B node2887 node2887Labels := by
  calc
    mixedMoment B raw28695 raw28695Labels = mixedMoment B raw28695step0 raw28695step0Labels := by
      have hz : ∀ j, raw28695 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28695step0 = (fun i j => raw28695 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28695step0 raw28695; decide +kernel
      have hl : raw28695step0Labels = raw28695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28695 raw28695Labels permutation434 hz
    mixedMoment B raw28695step0 raw28695step0Labels = mixedMoment B raw28695step1 raw28695step1Labels := by
      have hz : ∀ j, raw28695step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28695step1 = (fun i j => raw28695step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28695step1 raw28695step0; decide +kernel
      have hl : raw28695step1Labels = raw28695step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28695step0 raw28695step0Labels permutation80 hz
    mixedMoment B raw28695step1 raw28695step1Labels = mixedMoment B raw28695step2 raw28695step2Labels := by
      have ha : raw28695step2 = (fun i j => raw28695step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28695step2 raw28695step1; decide +kernel
      have hl : raw28695step2Labels = raw28695step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28695step1 raw28695step1Labels permutation8 permutation7
    mixedMoment B raw28695step2 raw28695step2Labels = mixedMoment B raw28695step3 raw28695step3Labels := by
      have ha : raw28695step3 = raw28695step2 := by apply Matrix.ext; unfold raw28695step3 raw28695step2; decide +kernel
      have hl : raw28695step2Labels = labelEmbedding1 ∘ raw28695step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28695step2 raw28695step2Labels raw28695step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2887 node2887Labels := by rfl

def raw28696 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw28696Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw28696step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 1, 1], ![-1, -2, 3]]
def raw28696step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28696step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw28696step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28696step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw28696step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28696 raw28696Labels = mixedMoment B node2886 node2886Labels := by
  calc
    mixedMoment B raw28696 raw28696Labels = mixedMoment B raw28696step0 raw28696step0Labels := by
      have hz : ∀ j, raw28696 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28696step0 = (fun i j => raw28696 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28696step0 raw28696; decide +kernel
      have hl : raw28696step0Labels = raw28696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28696 raw28696Labels permutation434 hz
    mixedMoment B raw28696step0 raw28696step0Labels = mixedMoment B raw28696step1 raw28696step1Labels := by
      have hz : ∀ j, raw28696step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28696step1 = (fun i j => raw28696step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28696step1 raw28696step0; decide +kernel
      have hl : raw28696step1Labels = raw28696step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28696step0 raw28696step0Labels permutation80 hz
    mixedMoment B raw28696step1 raw28696step1Labels = mixedMoment B raw28696step2 raw28696step2Labels := by
      have ha : raw28696step2 = (fun i j => raw28696step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28696step2 raw28696step1; decide +kernel
      have hl : raw28696step2Labels = raw28696step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28696step1 raw28696step1Labels permutation8 permutation7
    mixedMoment B raw28696step2 raw28696step2Labels = mixedMoment B raw28696step3 raw28696step3Labels := by
      have ha : raw28696step3 = raw28696step2 := by apply Matrix.ext; unfold raw28696step3 raw28696step2; decide +kernel
      have hl : raw28696step2Labels = labelEmbedding1 ∘ raw28696step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28696step2 raw28696step2Labels raw28696step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2886 node2886Labels := by rfl

def raw28697 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28697Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28697step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw28697step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28697step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28697step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28697step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28697 raw28697Labels = mixedMoment B node3177 node3177Labels := by
  calc
    mixedMoment B raw28697 raw28697Labels = mixedMoment B raw28697step0 raw28697step0Labels := by
      have hz : ∀ j, raw28697 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28697step0 = (fun i j => raw28697 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28697step0 raw28697; decide +kernel
      have hl : raw28697step0Labels = raw28697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28697 raw28697Labels permutation434 hz
    mixedMoment B raw28697step0 raw28697step0Labels = mixedMoment B raw28697step1 raw28697step1Labels := by
      have ha : raw28697step1 = (fun i j => raw28697step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28697step1 raw28697step0; decide +kernel
      have hl : raw28697step1Labels = raw28697step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28697step0 raw28697step0Labels permutation44 permutation5
    mixedMoment B raw28697step1 raw28697step1Labels = mixedMoment B raw28697step2 raw28697step2Labels := by
      have ha : raw28697step2 = -raw28697step1 := by apply Matrix.ext; change ∀ i j, raw28697step2 i j = -(raw28697step1 i j); unfold raw28697step2 raw28697step1; decide +kernel
      have hl : raw28697step2Labels = raw28697step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28697step2 raw28697step2Labels = mixedMoment B raw28697step3 raw28697step3Labels := by
      have ha : raw28697step3 = raw28697step2 := by apply Matrix.ext; unfold raw28697step3 raw28697step2; decide +kernel
      have hl : raw28697step2Labels = labelEmbedding1 ∘ raw28697step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28697step2 raw28697step2Labels raw28697step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3177 node3177Labels := by rfl

def raw28698 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28698Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28698step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw28698step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28698step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw28698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28698 raw28698Labels = mixedMoment B node2989 node2989Labels := by
  calc
    mixedMoment B raw28698 raw28698Labels = mixedMoment B raw28698step0 raw28698step0Labels := by
      have hz : ∀ j, raw28698 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28698step0 = (fun i j => raw28698 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28698step0 raw28698; decide +kernel
      have hl : raw28698step0Labels = raw28698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28698 raw28698Labels permutation434 hz
    mixedMoment B raw28698step0 raw28698step0Labels = mixedMoment B raw28698step1 raw28698step1Labels := by
      have ha : raw28698step1 = (fun i j => raw28698step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28698step1 raw28698step0; decide +kernel
      have hl : raw28698step1Labels = raw28698step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28698step0 raw28698step0Labels permutation32 permutation7
    mixedMoment B raw28698step1 raw28698step1Labels = mixedMoment B raw28698step2 raw28698step2Labels := by
      have ha : raw28698step2 = raw28698step1 := by apply Matrix.ext; unfold raw28698step2 raw28698step1; decide +kernel
      have hl : raw28698step1Labels = labelEmbedding1 ∘ raw28698step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28698step1 raw28698step1Labels raw28698step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2989 node2989Labels := by rfl

def raw28699 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28699Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28699step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28699step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28699step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28699 raw28699Labels = mixedMoment B node2915 node2915Labels := by
  calc
    mixedMoment B raw28699 raw28699Labels = mixedMoment B raw28699step0 raw28699step0Labels := by
      have ha : raw28699step0 = (fun i j => raw28699 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28699step0 raw28699; decide +kernel
      have hl : raw28699step0Labels = raw28699Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28699 raw28699Labels permutation152 permutation7
    mixedMoment B raw28699step0 raw28699step0Labels = mixedMoment B raw28699step1 raw28699step1Labels := by
      have ha : raw28699step1 = raw28699step0 := by apply Matrix.ext; unfold raw28699step1 raw28699step0; decide +kernel
      have hl : raw28699step0Labels = labelEmbedding1 ∘ raw28699step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28699step0 raw28699step0Labels raw28699step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2915 node2915Labels := by rfl

def raw28700 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw28700Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw28700step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw28700step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw28700step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28700 raw28700Labels = mixedMoment B node2929 node2929Labels := by
  calc
    mixedMoment B raw28700 raw28700Labels = mixedMoment B raw28700step0 raw28700step0Labels := by
      have hz : ∀ j, raw28700 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28700step0 = (fun i j => raw28700 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28700step0 raw28700; decide +kernel
      have hl : raw28700step0Labels = raw28700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28700 raw28700Labels permutation434 hz
    mixedMoment B raw28700step0 raw28700step0Labels = mixedMoment B raw28700step1 raw28700step1Labels := by
      have ha : raw28700step1 = (fun i j => raw28700step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28700step1 raw28700step0; decide +kernel
      have hl : raw28700step1Labels = raw28700step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28700step0 raw28700step0Labels permutation32 permutation7
    mixedMoment B raw28700step1 raw28700step1Labels = mixedMoment B raw28700step2 raw28700step2Labels := by
      have ha : raw28700step2 = raw28700step1 := by apply Matrix.ext; unfold raw28700step2 raw28700step1; decide +kernel
      have hl : raw28700step1Labels = labelEmbedding1 ∘ raw28700step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28700step1 raw28700step1Labels raw28700step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2929 node2929Labels := by rfl

def raw28701 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw28701Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw28701step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28701step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28701step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28701step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28701step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28701 raw28701Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw28701 raw28701Labels = mixedMoment B raw28701step0 raw28701step0Labels := by
      have hz : ∀ j, raw28701 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28701step0 = (fun i j => raw28701 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28701step0 raw28701; decide +kernel
      have hl : raw28701step0Labels = raw28701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28701 raw28701Labels permutation434 hz
    mixedMoment B raw28701step0 raw28701step0Labels = mixedMoment B raw28701step1 raw28701step1Labels := by
      have ha : raw28701step1 = (fun i j => raw28701step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28701step1 raw28701step0; decide +kernel
      have hl : raw28701step1Labels = raw28701step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28701step0 raw28701step0Labels permutation151 permutation7
    mixedMoment B raw28701step1 raw28701step1Labels = mixedMoment B raw28701step2 raw28701step2Labels := by
      have ha : raw28701step2 = -raw28701step1 := by apply Matrix.ext; change ∀ i j, raw28701step2 i j = -(raw28701step1 i j); unfold raw28701step2 raw28701step1; decide +kernel
      have hl : raw28701step2Labels = raw28701step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28701step2 raw28701step2Labels = mixedMoment B raw28701step3 raw28701step3Labels := by
      have ha : raw28701step3 = raw28701step2 := by apply Matrix.ext; unfold raw28701step3 raw28701step2; decide +kernel
      have hl : raw28701step2Labels = labelEmbedding1 ∘ raw28701step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28701step2 raw28701step2Labels raw28701step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2865 node2865Labels := by rfl

def raw28702 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28702step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw28702step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28702step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28702step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28702step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28702 raw28702Labels = mixedMoment B node3177 node3177Labels := by
  calc
    mixedMoment B raw28702 raw28702Labels = mixedMoment B raw28702step0 raw28702step0Labels := by
      have hz : ∀ j, raw28702 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28702step0 = (fun i j => raw28702 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28702step0 raw28702; decide +kernel
      have hl : raw28702step0Labels = raw28702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28702 raw28702Labels permutation346 hz
    mixedMoment B raw28702step0 raw28702step0Labels = mixedMoment B raw28702step1 raw28702step1Labels := by
      have ha : raw28702step1 = (fun i j => raw28702step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28702step1 raw28702step0; decide +kernel
      have hl : raw28702step1Labels = raw28702step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28702step0 raw28702step0Labels permutation44 permutation5
    mixedMoment B raw28702step1 raw28702step1Labels = mixedMoment B raw28702step2 raw28702step2Labels := by
      have ha : raw28702step2 = -raw28702step1 := by apply Matrix.ext; change ∀ i j, raw28702step2 i j = -(raw28702step1 i j); unfold raw28702step2 raw28702step1; decide +kernel
      have hl : raw28702step2Labels = raw28702step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28702step2 raw28702step2Labels = mixedMoment B raw28702step3 raw28702step3Labels := by
      have ha : raw28702step3 = raw28702step2 := by apply Matrix.ext; unfold raw28702step3 raw28702step2; decide +kernel
      have hl : raw28702step2Labels = labelEmbedding1 ∘ raw28702step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28702step2 raw28702step2Labels raw28702step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3177 node3177Labels := by rfl

def raw28703 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28703step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw28703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw28703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28703 raw28703Labels = mixedMoment B node2989 node2989Labels := by
  calc
    mixedMoment B raw28703 raw28703Labels = mixedMoment B raw28703step0 raw28703step0Labels := by
      have hz : ∀ j, raw28703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28703step0 = (fun i j => raw28703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28703step0 raw28703; decide +kernel
      have hl : raw28703step0Labels = raw28703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28703 raw28703Labels permutation346 hz
    mixedMoment B raw28703step0 raw28703step0Labels = mixedMoment B raw28703step1 raw28703step1Labels := by
      have ha : raw28703step1 = (fun i j => raw28703step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28703step1 raw28703step0; decide +kernel
      have hl : raw28703step1Labels = raw28703step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28703step0 raw28703step0Labels permutation32 permutation7
    mixedMoment B raw28703step1 raw28703step1Labels = mixedMoment B raw28703step2 raw28703step2Labels := by
      have ha : raw28703step2 = raw28703step1 := by apply Matrix.ext; unfold raw28703step2 raw28703step1; decide +kernel
      have hl : raw28703step1Labels = labelEmbedding1 ∘ raw28703step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28703step1 raw28703step1Labels raw28703step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2989 node2989Labels := by rfl

def raw28704 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28704step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28704 raw28704Labels = mixedMoment B node2915 node2915Labels := by
  calc
    mixedMoment B raw28704 raw28704Labels = mixedMoment B raw28704step0 raw28704step0Labels := by
      have ha : raw28704step0 = (fun i j => raw28704 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28704step0 raw28704; decide +kernel
      have hl : raw28704step0Labels = raw28704Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28704 raw28704Labels permutation158 permutation7
    mixedMoment B raw28704step0 raw28704step0Labels = mixedMoment B raw28704step1 raw28704step1Labels := by
      have ha : raw28704step1 = raw28704step0 := by apply Matrix.ext; unfold raw28704step1 raw28704step0; decide +kernel
      have hl : raw28704step0Labels = labelEmbedding1 ∘ raw28704step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28704step0 raw28704step0Labels raw28704step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2915 node2915Labels := by rfl

def raw28705 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw28705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw28705step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw28705step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28705step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw28705step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28705 raw28705Labels = mixedMoment B node2929 node2929Labels := by
  calc
    mixedMoment B raw28705 raw28705Labels = mixedMoment B raw28705step0 raw28705step0Labels := by
      have hz : ∀ j, raw28705 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28705step0 = (fun i j => raw28705 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28705step0 raw28705; decide +kernel
      have hl : raw28705step0Labels = raw28705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28705 raw28705Labels permutation346 hz
    mixedMoment B raw28705step0 raw28705step0Labels = mixedMoment B raw28705step1 raw28705step1Labels := by
      have ha : raw28705step1 = (fun i j => raw28705step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28705step1 raw28705step0; decide +kernel
      have hl : raw28705step1Labels = raw28705step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28705step0 raw28705step0Labels permutation32 permutation7
    mixedMoment B raw28705step1 raw28705step1Labels = mixedMoment B raw28705step2 raw28705step2Labels := by
      have ha : raw28705step2 = raw28705step1 := by apply Matrix.ext; unfold raw28705step2 raw28705step1; decide +kernel
      have hl : raw28705step1Labels = labelEmbedding1 ∘ raw28705step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28705step1 raw28705step1Labels raw28705step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2929 node2929Labels := by rfl

def raw28706 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28706step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 0, 1], ![0, -3, 3]]
def raw28706step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28706step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -3, 0]]
def raw28706step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28706step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -3, 0]]
def raw28706step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28706 raw28706Labels = mixedMoment B node3215 node3215Labels := by
  calc
    mixedMoment B raw28706 raw28706Labels = mixedMoment B raw28706step0 raw28706step0Labels := by
      have hz : ∀ j, raw28706 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28706step0 = (fun i j => raw28706 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28706step0 raw28706; decide +kernel
      have hl : raw28706step0Labels = raw28706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28706 raw28706Labels permutation434 hz
    mixedMoment B raw28706step0 raw28706step0Labels = mixedMoment B raw28706step1 raw28706step1Labels := by
      have hz : ∀ j, raw28706step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28706step1 = (fun i j => raw28706step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28706step1 raw28706step0; decide +kernel
      have hl : raw28706step1Labels = raw28706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28706step0 raw28706step0Labels permutation80 hz
    mixedMoment B raw28706step1 raw28706step1Labels = mixedMoment B raw28706step2 raw28706step2Labels := by
      have ha : raw28706step2 = (fun i j => raw28706step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28706step2 raw28706step1; decide +kernel
      have hl : raw28706step2Labels = raw28706step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28706step1 raw28706step1Labels permutation8 permutation7
    mixedMoment B raw28706step2 raw28706step2Labels = mixedMoment B raw28706step3 raw28706step3Labels := by
      have ha : raw28706step3 = raw28706step2 := by apply Matrix.ext; unfold raw28706step3 raw28706step2; decide +kernel
      have hl : raw28706step2Labels = labelEmbedding1 ∘ raw28706step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28706step2 raw28706step2Labels raw28706step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3215 node3215Labels := by rfl

def raw28707 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 0, 1], ![0, -3, 3]]
def raw28707step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28707step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28707step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw28707step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28707 raw28707Labels = mixedMoment B node3004 node3004Labels := by
  calc
    mixedMoment B raw28707 raw28707Labels = mixedMoment B raw28707step0 raw28707step0Labels := by
      have hz : ∀ j, raw28707 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28707step0 = (fun i j => raw28707 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28707step0 raw28707; decide +kernel
      have hl : raw28707step0Labels = raw28707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28707 raw28707Labels permutation434 hz
    mixedMoment B raw28707step0 raw28707step0Labels = mixedMoment B raw28707step1 raw28707step1Labels := by
      have hz : ∀ j, raw28707step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28707step1 = (fun i j => raw28707step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28707step1 raw28707step0; decide +kernel
      have hl : raw28707step1Labels = raw28707step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28707step0 raw28707step0Labels permutation80 hz
    mixedMoment B raw28707step1 raw28707step1Labels = mixedMoment B raw28707step2 raw28707step2Labels := by
      have ha : raw28707step2 = (fun i j => raw28707step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28707step2 raw28707step1; decide +kernel
      have hl : raw28707step2Labels = raw28707step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28707step1 raw28707step1Labels permutation8 permutation7
    mixedMoment B raw28707step2 raw28707step2Labels = mixedMoment B raw28707step3 raw28707step3Labels := by
      have ha : raw28707step3 = raw28707step2 := by apply Matrix.ext; unfold raw28707step3 raw28707step2; decide +kernel
      have hl : raw28707step2Labels = labelEmbedding1 ∘ raw28707step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28707step2 raw28707step2Labels raw28707step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3004 node3004Labels := by rfl

def raw28708 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28708step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28708 raw28708Labels = mixedMoment B node2941 node2941Labels := by
  calc
    mixedMoment B raw28708 raw28708Labels = mixedMoment B raw28708step0 raw28708step0Labels := by
      have hz : ∀ j, raw28708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28708step0 = (fun i j => raw28708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28708step0 raw28708; decide +kernel
      have hl : raw28708step0Labels = raw28708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28708 raw28708Labels permutation434 hz
    mixedMoment B raw28708step0 raw28708step0Labels = mixedMoment B raw28708step1 raw28708step1Labels := by
      have ha : raw28708step1 = (fun i j => raw28708step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28708step1 raw28708step0; decide +kernel
      have hl : raw28708step1Labels = raw28708step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28708step0 raw28708step0Labels permutation32 permutation7
    mixedMoment B raw28708step1 raw28708step1Labels = mixedMoment B raw28708step2 raw28708step2Labels := by
      have ha : raw28708step2 = raw28708step1 := by apply Matrix.ext; unfold raw28708step2 raw28708step1; decide +kernel
      have hl : raw28708step1Labels = labelEmbedding1 ∘ raw28708step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28708step1 raw28708step1Labels raw28708step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2941 node2941Labels := by rfl

def raw28709 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28709step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28709 raw28709Labels = mixedMoment B node2941 node2941Labels := by
  calc
    mixedMoment B raw28709 raw28709Labels = mixedMoment B raw28709step0 raw28709step0Labels := by
      have hz : ∀ j, raw28709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28709step0 = (fun i j => raw28709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28709step0 raw28709; decide +kernel
      have hl : raw28709step0Labels = raw28709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28709 raw28709Labels permutation346 hz
    mixedMoment B raw28709step0 raw28709step0Labels = mixedMoment B raw28709step1 raw28709step1Labels := by
      have ha : raw28709step1 = (fun i j => raw28709step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28709step1 raw28709step0; decide +kernel
      have hl : raw28709step1Labels = raw28709step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28709step0 raw28709step0Labels permutation32 permutation7
    mixedMoment B raw28709step1 raw28709step1Labels = mixedMoment B raw28709step2 raw28709step2Labels := by
      have ha : raw28709step2 = raw28709step1 := by apply Matrix.ext; unfold raw28709step2 raw28709step1; decide +kernel
      have hl : raw28709step1Labels = labelEmbedding1 ∘ raw28709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28709step1 raw28709step1Labels raw28709step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2941 node2941Labels := by rfl

def raw28710 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw28710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw28710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-2, 1, 1], ![1, -4, 3]]
def raw28710step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28710step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw28710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28710step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw28710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28710 raw28710Labels = mixedMoment B node1417 node1417Labels := by
  calc
    mixedMoment B raw28710 raw28710Labels = mixedMoment B raw28710step0 raw28710step0Labels := by
      have hz : ∀ j, raw28710 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28710step0 = (fun i j => raw28710 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28710step0 raw28710; decide +kernel
      have hl : raw28710step0Labels = raw28710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28710 raw28710Labels permutation434 hz
    mixedMoment B raw28710step0 raw28710step0Labels = mixedMoment B raw28710step1 raw28710step1Labels := by
      have hz : ∀ j, raw28710step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28710step1 = (fun i j => raw28710step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28710step1 raw28710step0; decide +kernel
      have hl : raw28710step1Labels = raw28710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28710step0 raw28710step0Labels permutation80 hz
    mixedMoment B raw28710step1 raw28710step1Labels = mixedMoment B raw28710step2 raw28710step2Labels := by
      have ha : raw28710step2 = (fun i j => raw28710step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28710step2 raw28710step1; decide +kernel
      have hl : raw28710step2Labels = raw28710step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28710step1 raw28710step1Labels permutation29 permutation5
    mixedMoment B raw28710step2 raw28710step2Labels = mixedMoment B raw28710step3 raw28710step3Labels := by
      have ha : raw28710step3 = raw28710step2 := by apply Matrix.ext; unfold raw28710step3 raw28710step2; decide +kernel
      have hl : raw28710step2Labels = labelEmbedding1 ∘ raw28710step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28710step2 raw28710step2Labels raw28710step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1417 node1417Labels := by rfl

def raw28711 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw28711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw28711step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-2, 1, 1], ![1, -4, 3]]
def raw28711step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28711step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw28711step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28711step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw28711step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28711 raw28711Labels = mixedMoment B node1449 node1449Labels := by
  calc
    mixedMoment B raw28711 raw28711Labels = mixedMoment B raw28711step0 raw28711step0Labels := by
      have hz : ∀ j, raw28711 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28711step0 = (fun i j => raw28711 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28711step0 raw28711; decide +kernel
      have hl : raw28711step0Labels = raw28711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28711 raw28711Labels permutation434 hz
    mixedMoment B raw28711step0 raw28711step0Labels = mixedMoment B raw28711step1 raw28711step1Labels := by
      have hz : ∀ j, raw28711step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28711step1 = (fun i j => raw28711step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28711step1 raw28711step0; decide +kernel
      have hl : raw28711step1Labels = raw28711step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28711step0 raw28711step0Labels permutation80 hz
    mixedMoment B raw28711step1 raw28711step1Labels = mixedMoment B raw28711step2 raw28711step2Labels := by
      have ha : raw28711step2 = (fun i j => raw28711step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28711step2 raw28711step1; decide +kernel
      have hl : raw28711step2Labels = raw28711step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28711step1 raw28711step1Labels permutation29 permutation5
    mixedMoment B raw28711step2 raw28711step2Labels = mixedMoment B raw28711step3 raw28711step3Labels := by
      have ha : raw28711step3 = raw28711step2 := by apply Matrix.ext; unfold raw28711step3 raw28711step2; decide +kernel
      have hl : raw28711step2Labels = labelEmbedding1 ∘ raw28711step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28711step2 raw28711step2Labels raw28711step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1449 node1449Labels := by rfl

def raw28712 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw28712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw28712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw28712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw28712step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28712 raw28712Labels = mixedMoment B node1415 node1415Labels := by
  calc
    mixedMoment B raw28712 raw28712Labels = mixedMoment B raw28712step0 raw28712step0Labels := by
      have hz : ∀ j, raw28712 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28712step0 = (fun i j => raw28712 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28712step0 raw28712; decide +kernel
      have hl : raw28712step0Labels = raw28712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28712 raw28712Labels permutation434 hz
    mixedMoment B raw28712step0 raw28712step0Labels = mixedMoment B raw28712step1 raw28712step1Labels := by
      have ha : raw28712step1 = (fun i j => raw28712step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28712step1 raw28712step0; decide +kernel
      have hl : raw28712step1Labels = raw28712step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28712step0 raw28712step0Labels permutation137 permutation5
    mixedMoment B raw28712step1 raw28712step1Labels = mixedMoment B raw28712step2 raw28712step2Labels := by
      have ha : raw28712step2 = raw28712step1 := by apply Matrix.ext; unfold raw28712step2 raw28712step1; decide +kernel
      have hl : raw28712step1Labels = labelEmbedding1 ∘ raw28712step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28712step1 raw28712step1Labels raw28712step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1415 node1415Labels := by rfl

def raw28713 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw28713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw28713step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw28713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28713step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw28713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28713 raw28713Labels = mixedMoment B node1415 node1415Labels := by
  calc
    mixedMoment B raw28713 raw28713Labels = mixedMoment B raw28713step0 raw28713step0Labels := by
      have hz : ∀ j, raw28713 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28713step0 = (fun i j => raw28713 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28713step0 raw28713; decide +kernel
      have hl : raw28713step0Labels = raw28713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28713 raw28713Labels permutation346 hz
    mixedMoment B raw28713step0 raw28713step0Labels = mixedMoment B raw28713step1 raw28713step1Labels := by
      have ha : raw28713step1 = (fun i j => raw28713step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28713step1 raw28713step0; decide +kernel
      have hl : raw28713step1Labels = raw28713step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28713step0 raw28713step0Labels permutation137 permutation5
    mixedMoment B raw28713step1 raw28713step1Labels = mixedMoment B raw28713step2 raw28713step2Labels := by
      have ha : raw28713step2 = raw28713step1 := by apply Matrix.ext; unfold raw28713step2 raw28713step1; decide +kernel
      have hl : raw28713step1Labels = labelEmbedding1 ∘ raw28713step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28713step1 raw28713step1Labels raw28713step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1415 node1415Labels := by rfl

def raw28714 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw28714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw28714step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-3, 2, 1], ![1, -4, 3]]
def raw28714step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28714step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw28714step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28714step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw28714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28714 raw28714Labels = mixedMoment B node1418 node1418Labels := by
  calc
    mixedMoment B raw28714 raw28714Labels = mixedMoment B raw28714step0 raw28714step0Labels := by
      have hz : ∀ j, raw28714 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28714step0 = (fun i j => raw28714 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28714step0 raw28714; decide +kernel
      have hl : raw28714step0Labels = raw28714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28714 raw28714Labels permutation434 hz
    mixedMoment B raw28714step0 raw28714step0Labels = mixedMoment B raw28714step1 raw28714step1Labels := by
      have hz : ∀ j, raw28714step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28714step1 = (fun i j => raw28714step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28714step1 raw28714step0; decide +kernel
      have hl : raw28714step1Labels = raw28714step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28714step0 raw28714step0Labels permutation80 hz
    mixedMoment B raw28714step1 raw28714step1Labels = mixedMoment B raw28714step2 raw28714step2Labels := by
      have ha : raw28714step2 = (fun i j => raw28714step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28714step2 raw28714step1; decide +kernel
      have hl : raw28714step2Labels = raw28714step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28714step1 raw28714step1Labels permutation28 permutation5
    mixedMoment B raw28714step2 raw28714step2Labels = mixedMoment B raw28714step3 raw28714step3Labels := by
      have ha : raw28714step3 = raw28714step2 := by apply Matrix.ext; unfold raw28714step3 raw28714step2; decide +kernel
      have hl : raw28714step2Labels = labelEmbedding1 ∘ raw28714step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28714step2 raw28714step2Labels raw28714step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1418 node1418Labels := by rfl

def raw28715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28715 raw28715Labels = mixedMoment B node4954 node4954Labels := by
  calc
    mixedMoment B raw28715 raw28715Labels = mixedMoment B raw28715step0 raw28715step0Labels := by
      have ha : raw28715step0 = (fun i j => raw28715 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28715step0 raw28715; decide +kernel
      have hl : raw28715step0Labels = raw28715Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28715 raw28715Labels permutation158 permutation2
    _ = mixedMoment B node4954 node4954Labels := by rfl

def raw28716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28716step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28716 raw28716Labels = mixedMoment B node5033 node5033Labels := by
  calc
    mixedMoment B raw28716 raw28716Labels = mixedMoment B raw28716step0 raw28716step0Labels := by
      have ha : raw28716step0 = (fun i j => raw28716 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28716step0 raw28716; decide +kernel
      have hl : raw28716step0Labels = raw28716Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28716 raw28716Labels permutation200 permutation2
    _ = mixedMoment B node5033 node5033Labels := by rfl

def raw28717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28717 raw28717Labels = mixedMoment B node5127 node5127Labels := by
  calc
    mixedMoment B raw28717 raw28717Labels = mixedMoment B raw28717step0 raw28717step0Labels := by
      have ha : raw28717step0 = (fun i j => raw28717 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28717step0 raw28717; decide +kernel
      have hl : raw28717step0Labels = raw28717Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28717 raw28717Labels permutation160 permutation2
    _ = mixedMoment B node5127 node5127Labels := by rfl

def raw28718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28718 raw28718Labels = mixedMoment B node4965 node4965Labels := by
  calc
    mixedMoment B raw28718 raw28718Labels = mixedMoment B raw28718step0 raw28718step0Labels := by
      have hz : ∀ j, raw28718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28718step0 = (fun i j => raw28718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28718step0 raw28718; decide +kernel
      have hl : raw28718step0Labels = raw28718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28718 raw28718Labels permutation346 hz
    _ = mixedMoment B node4965 node4965Labels := by rfl

def raw28719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28719step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28719step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28719 raw28719Labels = mixedMoment B node5041 node5041Labels := by
  calc
    mixedMoment B raw28719 raw28719Labels = mixedMoment B raw28719step0 raw28719step0Labels := by
      have ha : raw28719step0 = (fun i j => raw28719 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28719step0 raw28719; decide +kernel
      have hl : raw28719step0Labels = raw28719Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28719 raw28719Labels permutation686 permutation2
    mixedMoment B raw28719step0 raw28719step0Labels = mixedMoment B raw28719step1 raw28719step1Labels := by
      have ha : raw28719step1 = -raw28719step0 := by apply Matrix.ext; change ∀ i j, raw28719step1 i j = -(raw28719step0 i j); unfold raw28719step1 raw28719step0; decide +kernel
      have hl : raw28719step1Labels = raw28719step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5041 node5041Labels := by rfl

def raw28720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw28720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28720 raw28720Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw28720 raw28720Labels = mixedMoment B raw28720step0 raw28720step0Labels := by
      have hz : ∀ j, raw28720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28720step0 = (fun i j => raw28720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28720step0 raw28720; decide +kernel
      have hl : raw28720step0Labels = raw28720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28720 raw28720Labels permutation346 hz
    mixedMoment B raw28720step0 raw28720step0Labels = mixedMoment B raw28720step1 raw28720step1Labels := by
      have ha : raw28720step1 = (fun i j => raw28720step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28720step1 raw28720step0; decide +kernel
      have hl : raw28720step1Labels = raw28720step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28720step0 raw28720step0Labels permutation34 permutation2
    _ = mixedMoment B node5147 node5147Labels := by rfl

def raw28721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28721step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28721step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28721 raw28721Labels = mixedMoment B node4934 node4934Labels := by
  calc
    mixedMoment B raw28721 raw28721Labels = mixedMoment B raw28721step0 raw28721step0Labels := by
      have hz : ∀ j, raw28721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28721step0 = (fun i j => raw28721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28721step0 raw28721; decide +kernel
      have hl : raw28721step0Labels = raw28721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28721 raw28721Labels permutation346 hz
    mixedMoment B raw28721step0 raw28721step0Labels = mixedMoment B raw28721step1 raw28721step1Labels := by
      have ha : raw28721step1 = (fun i j => raw28721step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28721step1 raw28721step0; decide +kernel
      have hl : raw28721step1Labels = raw28721step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28721step0 raw28721step0Labels permutation151 permutation2
    mixedMoment B raw28721step1 raw28721step1Labels = mixedMoment B raw28721step2 raw28721step2Labels := by
      have ha : raw28721step2 = -raw28721step1 := by apply Matrix.ext; change ∀ i j, raw28721step2 i j = -(raw28721step1 i j); unfold raw28721step2 raw28721step1; decide +kernel
      have hl : raw28721step2Labels = raw28721step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4934 node4934Labels := by rfl

def raw28722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28722 raw28722Labels = mixedMoment B node4929 node4929Labels := by
  calc
    mixedMoment B raw28722 raw28722Labels = mixedMoment B raw28722step0 raw28722step0Labels := by
      have ha : raw28722step0 = (fun i j => raw28722 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28722step0 raw28722; decide +kernel
      have hl : raw28722step0Labels = raw28722Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28722 raw28722Labels permutation686 permutation2
    mixedMoment B raw28722step0 raw28722step0Labels = mixedMoment B raw28722step1 raw28722step1Labels := by
      have ha : raw28722step1 = -raw28722step0 := by apply Matrix.ext; change ∀ i j, raw28722step1 i j = -(raw28722step0 i j); unfold raw28722step1 raw28722step0; decide +kernel
      have hl : raw28722step1Labels = raw28722step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4929 node4929Labels := by rfl

def raw28723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28723step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28723step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28723 raw28723Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw28723 raw28723Labels = mixedMoment B raw28723step0 raw28723step0Labels := by
      have hz : ∀ j, raw28723 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28723step0 = (fun i j => raw28723 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28723step0 raw28723; decide +kernel
      have hl : raw28723step0Labels = raw28723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28723 raw28723Labels permutation346 hz
    mixedMoment B raw28723step0 raw28723step0Labels = mixedMoment B raw28723step1 raw28723step1Labels := by
      have ha : raw28723step1 = (fun i j => raw28723step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28723step1 raw28723step0; decide +kernel
      have hl : raw28723step1Labels = raw28723step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28723step0 raw28723step0Labels permutation149 permutation2
    mixedMoment B raw28723step1 raw28723step1Labels = mixedMoment B raw28723step2 raw28723step2Labels := by
      have ha : raw28723step2 = -raw28723step1 := by apply Matrix.ext; change ∀ i j, raw28723step2 i j = -(raw28723step1 i j); unfold raw28723step2 raw28723step1; decide +kernel
      have hl : raw28723step2Labels = raw28723step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4943 node4943Labels := by rfl

def raw28724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28724step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28724step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28724 raw28724Labels = mixedMoment B node4534 node4534Labels := by
  calc
    mixedMoment B raw28724 raw28724Labels = mixedMoment B raw28724step0 raw28724step0Labels := by
      have hz : ∀ j, raw28724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28724step0 = (fun i j => raw28724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28724step0 raw28724; decide +kernel
      have hl : raw28724step0Labels = raw28724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28724 raw28724Labels permutation346 hz
    mixedMoment B raw28724step0 raw28724step0Labels = mixedMoment B raw28724step1 raw28724step1Labels := by
      have ha : raw28724step1 = (fun i j => raw28724step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28724step1 raw28724step0; decide +kernel
      have hl : raw28724step1Labels = raw28724step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28724step0 raw28724step0Labels permutation151 permutation2
    mixedMoment B raw28724step1 raw28724step1Labels = mixedMoment B raw28724step2 raw28724step2Labels := by
      have ha : raw28724step2 = -raw28724step1 := by apply Matrix.ext; change ∀ i j, raw28724step2 i j = -(raw28724step1 i j); unfold raw28724step2 raw28724step1; decide +kernel
      have hl : raw28724step2Labels = raw28724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4534 node4534Labels := by rfl

def raw28725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28725step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28725 raw28725Labels = mixedMoment B node4527 node4527Labels := by
  calc
    mixedMoment B raw28725 raw28725Labels = mixedMoment B raw28725step0 raw28725step0Labels := by
      have ha : raw28725step0 = (fun i j => raw28725 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28725step0 raw28725; decide +kernel
      have hl : raw28725step0Labels = raw28725Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28725 raw28725Labels permutation686 permutation2
    mixedMoment B raw28725step0 raw28725step0Labels = mixedMoment B raw28725step1 raw28725step1Labels := by
      have ha : raw28725step1 = -raw28725step0 := by apply Matrix.ext; change ∀ i j, raw28725step1 i j = -(raw28725step0 i j); unfold raw28725step1 raw28725step0; decide +kernel
      have hl : raw28725step1Labels = raw28725step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4527 node4527Labels := by rfl

def raw28726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28726step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28726 raw28726Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw28726 raw28726Labels = mixedMoment B raw28726step0 raw28726step0Labels := by
      have hz : ∀ j, raw28726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28726step0 = (fun i j => raw28726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28726step0 raw28726; decide +kernel
      have hl : raw28726step0Labels = raw28726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28726 raw28726Labels permutation346 hz
    mixedMoment B raw28726step0 raw28726step0Labels = mixedMoment B raw28726step1 raw28726step1Labels := by
      have ha : raw28726step1 = (fun i j => raw28726step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28726step1 raw28726step0; decide +kernel
      have hl : raw28726step1Labels = raw28726step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28726step0 raw28726step0Labels permutation149 permutation2
    mixedMoment B raw28726step1 raw28726step1Labels = mixedMoment B raw28726step2 raw28726step2Labels := by
      have ha : raw28726step2 = -raw28726step1 := by apply Matrix.ext; change ∀ i j, raw28726step2 i j = -(raw28726step1 i j); unfold raw28726step2 raw28726step1; decide +kernel
      have hl : raw28726step2Labels = raw28726step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4546 node4546Labels := by rfl

def raw28727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw28727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw28727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28727step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28727step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28727 raw28727Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw28727 raw28727Labels = mixedMoment B raw28727step0 raw28727step0Labels := by
      have hz : ∀ j, raw28727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28727step0 = (fun i j => raw28727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28727step0 raw28727; decide +kernel
      have hl : raw28727step0Labels = raw28727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28727 raw28727Labels permutation346 hz
    mixedMoment B raw28727step0 raw28727step0Labels = mixedMoment B raw28727step1 raw28727step1Labels := by
      have ha : raw28727step1 = (fun i j => raw28727step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28727step1 raw28727step0; decide +kernel
      have hl : raw28727step1Labels = raw28727step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28727step0 raw28727step0Labels permutation151 permutation2
    mixedMoment B raw28727step1 raw28727step1Labels = mixedMoment B raw28727step2 raw28727step2Labels := by
      have ha : raw28727step2 = -raw28727step1 := by apply Matrix.ext; change ∀ i j, raw28727step2 i j = -(raw28727step1 i j); unfold raw28727step2 raw28727step1; decide +kernel
      have hl : raw28727step2Labels = raw28727step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw28728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28728 raw28728Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw28728 raw28728Labels = mixedMoment B raw28728step0 raw28728step0Labels := by
      have hz : ∀ j, raw28728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28728step0 = (fun i j => raw28728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28728step0 raw28728; decide +kernel
      have hl : raw28728step0Labels = raw28728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28728 raw28728Labels permutation346 hz
    mixedMoment B raw28728step0 raw28728step0Labels = mixedMoment B raw28728step1 raw28728step1Labels := by
      have ha : raw28728step1 = (fun i j => raw28728step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28728step1 raw28728step0; decide +kernel
      have hl : raw28728step1Labels = raw28728step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28728step0 raw28728step0Labels permutation149 permutation7
    mixedMoment B raw28728step1 raw28728step1Labels = mixedMoment B raw28728step2 raw28728step2Labels := by
      have ha : raw28728step2 = raw28728step1 := by apply Matrix.ext; unfold raw28728step2 raw28728step1; decide +kernel
      have hl : raw28728step1Labels = labelEmbedding1 ∘ raw28728step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28728step1 raw28728step1Labels raw28728step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

def raw28729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28729step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28729step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28729step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28729 raw28729Labels = mixedMoment B node3459 node3459Labels := by
  calc
    mixedMoment B raw28729 raw28729Labels = mixedMoment B raw28729step0 raw28729step0Labels := by
      have ha : raw28729step0 = (fun i j => raw28729 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28729step0 raw28729; decide +kernel
      have hl : raw28729step0Labels = raw28729Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28729 raw28729Labels permutation674 permutation7
    mixedMoment B raw28729step0 raw28729step0Labels = mixedMoment B raw28729step1 raw28729step1Labels := by
      have ha : raw28729step1 = raw28729step0 := by apply Matrix.ext; unfold raw28729step1 raw28729step0; decide +kernel
      have hl : raw28729step0Labels = labelEmbedding1 ∘ raw28729step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28729step0 raw28729step0Labels raw28729step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3459 node3459Labels := by rfl

def raw28730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28730 raw28730Labels = mixedMoment B node3470 node3470Labels := by
  calc
    mixedMoment B raw28730 raw28730Labels = mixedMoment B raw28730step0 raw28730step0Labels := by
      have hz : ∀ j, raw28730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28730step0 = (fun i j => raw28730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28730step0 raw28730; decide +kernel
      have hl : raw28730step0Labels = raw28730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28730 raw28730Labels permutation346 hz
    mixedMoment B raw28730step0 raw28730step0Labels = mixedMoment B raw28730step1 raw28730step1Labels := by
      have ha : raw28730step1 = (fun i j => raw28730step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28730step1 raw28730step0; decide +kernel
      have hl : raw28730step1Labels = raw28730step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28730step0 raw28730step0Labels permutation149 permutation7
    mixedMoment B raw28730step1 raw28730step1Labels = mixedMoment B raw28730step2 raw28730step2Labels := by
      have ha : raw28730step2 = raw28730step1 := by apply Matrix.ext; unfold raw28730step2 raw28730step1; decide +kernel
      have hl : raw28730step1Labels = labelEmbedding1 ∘ raw28730step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28730step1 raw28730step1Labels raw28730step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3470 node3470Labels := by rfl

def raw28731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28731 raw28731Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw28731 raw28731Labels = mixedMoment B raw28731step0 raw28731step0Labels := by
      have hz : ∀ j, raw28731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28731step0 = (fun i j => raw28731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28731step0 raw28731; decide +kernel
      have hl : raw28731step0Labels = raw28731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28731 raw28731Labels permutation346 hz
    mixedMoment B raw28731step0 raw28731step0Labels = mixedMoment B raw28731step1 raw28731step1Labels := by
      have ha : raw28731step1 = (fun i j => raw28731step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28731step1 raw28731step0; decide +kernel
      have hl : raw28731step1Labels = raw28731step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28731step0 raw28731step0Labels permutation149 permutation7
    mixedMoment B raw28731step1 raw28731step1Labels = mixedMoment B raw28731step2 raw28731step2Labels := by
      have ha : raw28731step2 = raw28731step1 := by apply Matrix.ext; unfold raw28731step2 raw28731step1; decide +kernel
      have hl : raw28731step1Labels = labelEmbedding1 ∘ raw28731step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28731step1 raw28731step1Labels raw28731step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw28732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28732step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28732 raw28732Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw28732 raw28732Labels = mixedMoment B raw28732step0 raw28732step0Labels := by
      have hz : ∀ j, raw28732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28732step0 = (fun i j => raw28732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28732step0 raw28732; decide +kernel
      have hl : raw28732step0Labels = raw28732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28732 raw28732Labels permutation346 hz
    mixedMoment B raw28732step0 raw28732step0Labels = mixedMoment B raw28732step1 raw28732step1Labels := by
      have ha : raw28732step1 = (fun i j => raw28732step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28732step1 raw28732step0; decide +kernel
      have hl : raw28732step1Labels = raw28732step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28732step0 raw28732step0Labels permutation149 permutation7
    mixedMoment B raw28732step1 raw28732step1Labels = mixedMoment B raw28732step2 raw28732step2Labels := by
      have ha : raw28732step2 = raw28732step1 := by apply Matrix.ext; unfold raw28732step2 raw28732step1; decide +kernel
      have hl : raw28732step1Labels = labelEmbedding1 ∘ raw28732step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28732step1 raw28732step1Labels raw28732step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw28733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28733step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28733step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw28733step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28733step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw28733step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28733step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw28733step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28733 raw28733Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw28733 raw28733Labels = mixedMoment B raw28733step0 raw28733step0Labels := by
      have hz : ∀ j, raw28733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28733step0 = (fun i j => raw28733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28733step0 raw28733; decide +kernel
      have hl : raw28733step0Labels = raw28733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28733 raw28733Labels permutation346 hz
    mixedMoment B raw28733step0 raw28733step0Labels = mixedMoment B raw28733step1 raw28733step1Labels := by
      have hz : ∀ j, raw28733step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw28733step1 = (fun i j => raw28733step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw28733step1 raw28733step0; decide +kernel
      have hl : raw28733step1Labels = raw28733step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28733step0 raw28733step0Labels permutation56 hz
    mixedMoment B raw28733step1 raw28733step1Labels = mixedMoment B raw28733step2 raw28733step2Labels := by
      have ha : raw28733step2 = (fun i j => raw28733step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28733step2 raw28733step1; decide +kernel
      have hl : raw28733step2Labels = raw28733step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28733step1 raw28733step1Labels permutation8 permutation7
    mixedMoment B raw28733step2 raw28733step2Labels = mixedMoment B raw28733step3 raw28733step3Labels := by
      have ha : raw28733step3 = -raw28733step2 := by apply Matrix.ext; change ∀ i j, raw28733step3 i j = -(raw28733step2 i j); unfold raw28733step3 raw28733step2; decide +kernel
      have hl : raw28733step3Labels = raw28733step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28733step3 raw28733step3Labels = mixedMoment B raw28733step4 raw28733step4Labels := by
      have ha : raw28733step4 = raw28733step3 := by apply Matrix.ext; unfold raw28733step4 raw28733step3; decide +kernel
      have hl : raw28733step3Labels = labelEmbedding1 ∘ raw28733step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28733step3 raw28733step3Labels raw28733step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3300 node3300Labels := by rfl

def raw28734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28734step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28734 raw28734Labels = mixedMoment B node3452 node3452Labels := by
  calc
    mixedMoment B raw28734 raw28734Labels = mixedMoment B raw28734step0 raw28734step0Labels := by
      have ha : raw28734step0 = (fun i j => raw28734 (permutation680 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28734step0 raw28734; decide +kernel
      have hl : raw28734step0Labels = raw28734Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28734 raw28734Labels permutation680 permutation7
    mixedMoment B raw28734step0 raw28734step0Labels = mixedMoment B raw28734step1 raw28734step1Labels := by
      have ha : raw28734step1 = raw28734step0 := by apply Matrix.ext; unfold raw28734step1 raw28734step0; decide +kernel
      have hl : raw28734step0Labels = labelEmbedding1 ∘ raw28734step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28734step0 raw28734step0Labels raw28734step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3452 node3452Labels := by rfl

def raw28735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28735step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28735step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28735step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28735 raw28735Labels = mixedMoment B node3449 node3449Labels := by
  calc
    mixedMoment B raw28735 raw28735Labels = mixedMoment B raw28735step0 raw28735step0Labels := by
      have ha : raw28735step0 = (fun i j => raw28735 (permutation680 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28735step0 raw28735; decide +kernel
      have hl : raw28735step0Labels = raw28735Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28735 raw28735Labels permutation680 permutation7
    mixedMoment B raw28735step0 raw28735step0Labels = mixedMoment B raw28735step1 raw28735step1Labels := by
      have ha : raw28735step1 = raw28735step0 := by apply Matrix.ext; unfold raw28735step1 raw28735step0; decide +kernel
      have hl : raw28735step0Labels = labelEmbedding1 ∘ raw28735step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28735step0 raw28735step0Labels raw28735step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3449 node3449Labels := by rfl

def raw28736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28736 raw28736Labels = mixedMoment B node3513 node3513Labels := by
  calc
    mixedMoment B raw28736 raw28736Labels = mixedMoment B raw28736step0 raw28736step0Labels := by
      have ha : raw28736step0 = (fun i j => raw28736 (permutation680 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28736step0 raw28736; decide +kernel
      have hl : raw28736step0Labels = raw28736Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28736 raw28736Labels permutation680 permutation7
    mixedMoment B raw28736step0 raw28736step0Labels = mixedMoment B raw28736step1 raw28736step1Labels := by
      have ha : raw28736step1 = raw28736step0 := by apply Matrix.ext; unfold raw28736step1 raw28736step0; decide +kernel
      have hl : raw28736step0Labels = labelEmbedding1 ∘ raw28736step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28736step0 raw28736step0Labels raw28736step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3513 node3513Labels := by rfl

def raw28737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw28737step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28737step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28737step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw28737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28737 raw28737Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw28737 raw28737Labels = mixedMoment B raw28737step0 raw28737step0Labels := by
      have ha : raw28737step0 = (fun i j => raw28737 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28737step0 raw28737; decide +kernel
      have hl : raw28737step0Labels = raw28737Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28737 raw28737Labels permutation200 permutation7
    mixedMoment B raw28737step0 raw28737step0Labels = mixedMoment B raw28737step1 raw28737step1Labels := by
      have ha : raw28737step1 = -raw28737step0 := by apply Matrix.ext; change ∀ i j, raw28737step1 i j = -(raw28737step0 i j); unfold raw28737step1 raw28737step0; decide +kernel
      have hl : raw28737step1Labels = raw28737step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28737step1 raw28737step1Labels = mixedMoment B raw28737step2 raw28737step2Labels := by
      have ha : raw28737step2 = raw28737step1 := by apply Matrix.ext; unfold raw28737step2 raw28737step1; decide +kernel
      have hl : raw28737step1Labels = labelEmbedding1 ∘ raw28737step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28737step1 raw28737step1Labels raw28737step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

def raw28738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw28738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28738 raw28738Labels = mixedMoment B node3475 node3475Labels := by
  calc
    mixedMoment B raw28738 raw28738Labels = mixedMoment B raw28738step0 raw28738step0Labels := by
      have hz : ∀ j, raw28738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28738step0 = (fun i j => raw28738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28738step0 raw28738; decide +kernel
      have hl : raw28738step0Labels = raw28738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28738 raw28738Labels permutation346 hz
    mixedMoment B raw28738step0 raw28738step0Labels = mixedMoment B raw28738step1 raw28738step1Labels := by
      have ha : raw28738step1 = (fun i j => raw28738step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28738step1 raw28738step0; decide +kernel
      have hl : raw28738step1Labels = raw28738step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28738step0 raw28738step0Labels permutation149 permutation7
    mixedMoment B raw28738step1 raw28738step1Labels = mixedMoment B raw28738step2 raw28738step2Labels := by
      have ha : raw28738step2 = raw28738step1 := by apply Matrix.ext; unfold raw28738step2 raw28738step1; decide +kernel
      have hl : raw28738step1Labels = labelEmbedding1 ∘ raw28738step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28738step1 raw28738step1Labels raw28738step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3475 node3475Labels := by rfl

def raw28739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28739step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28739step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28739 raw28739Labels = mixedMoment B node3458 node3458Labels := by
  calc
    mixedMoment B raw28739 raw28739Labels = mixedMoment B raw28739step0 raw28739step0Labels := by
      have ha : raw28739step0 = (fun i j => raw28739 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28739step0 raw28739; decide +kernel
      have hl : raw28739step0Labels = raw28739Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28739 raw28739Labels permutation674 permutation7
    mixedMoment B raw28739step0 raw28739step0Labels = mixedMoment B raw28739step1 raw28739step1Labels := by
      have ha : raw28739step1 = raw28739step0 := by apply Matrix.ext; unfold raw28739step1 raw28739step0; decide +kernel
      have hl : raw28739step0Labels = labelEmbedding1 ∘ raw28739step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28739step0 raw28739step0Labels raw28739step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3458 node3458Labels := by rfl

def raw28740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28740 raw28740Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw28740 raw28740Labels = mixedMoment B raw28740step0 raw28740step0Labels := by
      have hz : ∀ j, raw28740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28740step0 = (fun i j => raw28740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28740step0 raw28740; decide +kernel
      have hl : raw28740step0Labels = raw28740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28740 raw28740Labels permutation346 hz
    mixedMoment B raw28740step0 raw28740step0Labels = mixedMoment B raw28740step1 raw28740step1Labels := by
      have ha : raw28740step1 = (fun i j => raw28740step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28740step1 raw28740step0; decide +kernel
      have hl : raw28740step1Labels = raw28740step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28740step0 raw28740step0Labels permutation149 permutation7
    mixedMoment B raw28740step1 raw28740step1Labels = mixedMoment B raw28740step2 raw28740step2Labels := by
      have ha : raw28740step2 = raw28740step1 := by apply Matrix.ext; unfold raw28740step2 raw28740step1; decide +kernel
      have hl : raw28740step1Labels = labelEmbedding1 ∘ raw28740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28740step1 raw28740step1Labels raw28740step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

def raw28741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28741step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw28741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28741step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28741step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28741step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28741 raw28741Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw28741 raw28741Labels = mixedMoment B raw28741step0 raw28741step0Labels := by
      have hz : ∀ j, raw28741 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28741step0 = (fun i j => raw28741 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28741step0 raw28741; decide +kernel
      have hl : raw28741step0Labels = raw28741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28741 raw28741Labels permutation346 hz
    mixedMoment B raw28741step0 raw28741step0Labels = mixedMoment B raw28741step1 raw28741step1Labels := by
      have ha : raw28741step1 = (fun i j => raw28741step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28741step1 raw28741step0; decide +kernel
      have hl : raw28741step1Labels = raw28741step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28741step0 raw28741step0Labels permutation38 permutation7
    mixedMoment B raw28741step1 raw28741step1Labels = mixedMoment B raw28741step2 raw28741step2Labels := by
      have ha : raw28741step2 = -raw28741step1 := by apply Matrix.ext; change ∀ i j, raw28741step2 i j = -(raw28741step1 i j); unfold raw28741step2 raw28741step1; decide +kernel
      have hl : raw28741step2Labels = raw28741step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28741step2 raw28741step2Labels = mixedMoment B raw28741step3 raw28741step3Labels := by
      have ha : raw28741step3 = raw28741step2 := by apply Matrix.ext; unfold raw28741step3 raw28741step2; decide +kernel
      have hl : raw28741step2Labels = labelEmbedding1 ∘ raw28741step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28741step2 raw28741step2Labels raw28741step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

def raw28742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28742 raw28742Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw28742 raw28742Labels = mixedMoment B raw28742step0 raw28742step0Labels := by
      have hz : ∀ j, raw28742 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28742step0 = (fun i j => raw28742 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28742step0 raw28742; decide +kernel
      have hl : raw28742step0Labels = raw28742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28742 raw28742Labels permutation346 hz
    mixedMoment B raw28742step0 raw28742step0Labels = mixedMoment B raw28742step1 raw28742step1Labels := by
      have ha : raw28742step1 = (fun i j => raw28742step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28742step1 raw28742step0; decide +kernel
      have hl : raw28742step1Labels = raw28742step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28742step0 raw28742step0Labels permutation149 permutation7
    mixedMoment B raw28742step1 raw28742step1Labels = mixedMoment B raw28742step2 raw28742step2Labels := by
      have ha : raw28742step2 = raw28742step1 := by apply Matrix.ext; unfold raw28742step2 raw28742step1; decide +kernel
      have hl : raw28742step1Labels = labelEmbedding1 ∘ raw28742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28742step1 raw28742step1Labels raw28742step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3415 node3415Labels := by rfl

def raw28743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28743step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28743 raw28743Labels = mixedMoment B node3403 node3403Labels := by
  calc
    mixedMoment B raw28743 raw28743Labels = mixedMoment B raw28743step0 raw28743step0Labels := by
      have ha : raw28743step0 = (fun i j => raw28743 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28743step0 raw28743; decide +kernel
      have hl : raw28743step0Labels = raw28743Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28743 raw28743Labels permutation674 permutation7
    mixedMoment B raw28743step0 raw28743step0Labels = mixedMoment B raw28743step1 raw28743step1Labels := by
      have ha : raw28743step1 = raw28743step0 := by apply Matrix.ext; unfold raw28743step1 raw28743step0; decide +kernel
      have hl : raw28743step0Labels = labelEmbedding1 ∘ raw28743step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28743step0 raw28743step0Labels raw28743step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3403 node3403Labels := by rfl

def raw28744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28744step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28744step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28744 raw28744Labels = mixedMoment B node3411 node3411Labels := by
  calc
    mixedMoment B raw28744 raw28744Labels = mixedMoment B raw28744step0 raw28744step0Labels := by
      have hz : ∀ j, raw28744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28744step0 = (fun i j => raw28744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28744step0 raw28744; decide +kernel
      have hl : raw28744step0Labels = raw28744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28744 raw28744Labels permutation346 hz
    mixedMoment B raw28744step0 raw28744step0Labels = mixedMoment B raw28744step1 raw28744step1Labels := by
      have ha : raw28744step1 = (fun i j => raw28744step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28744step1 raw28744step0; decide +kernel
      have hl : raw28744step1Labels = raw28744step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28744step0 raw28744step0Labels permutation149 permutation7
    mixedMoment B raw28744step1 raw28744step1Labels = mixedMoment B raw28744step2 raw28744step2Labels := by
      have ha : raw28744step2 = raw28744step1 := by apply Matrix.ext; unfold raw28744step2 raw28744step1; decide +kernel
      have hl : raw28744step1Labels = labelEmbedding1 ∘ raw28744step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28744step1 raw28744step1Labels raw28744step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3411 node3411Labels := by rfl

def raw28745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw28745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw28745step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw28745step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28745step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28745step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28745step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28745 raw28745Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw28745 raw28745Labels = mixedMoment B raw28745step0 raw28745step0Labels := by
      have hz : ∀ j, raw28745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28745step0 = (fun i j => raw28745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28745step0 raw28745; decide +kernel
      have hl : raw28745step0Labels = raw28745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28745 raw28745Labels permutation346 hz
    mixedMoment B raw28745step0 raw28745step0Labels = mixedMoment B raw28745step1 raw28745step1Labels := by
      have ha : raw28745step1 = (fun i j => raw28745step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28745step1 raw28745step0; decide +kernel
      have hl : raw28745step1Labels = raw28745step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28745step0 raw28745step0Labels permutation38 permutation7
    mixedMoment B raw28745step1 raw28745step1Labels = mixedMoment B raw28745step2 raw28745step2Labels := by
      have ha : raw28745step2 = -raw28745step1 := by apply Matrix.ext; change ∀ i j, raw28745step2 i j = -(raw28745step1 i j); unfold raw28745step2 raw28745step1; decide +kernel
      have hl : raw28745step2Labels = raw28745step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28745step2 raw28745step2Labels = mixedMoment B raw28745step3 raw28745step3Labels := by
      have ha : raw28745step3 = raw28745step2 := by apply Matrix.ext; unfold raw28745step3 raw28745step2; decide +kernel
      have hl : raw28745step2Labels = labelEmbedding1 ∘ raw28745step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28745step2 raw28745step2Labels raw28745step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

def raw28746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28746step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw28746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28746 raw28746Labels = mixedMoment B node3268 node3268Labels := by
  calc
    mixedMoment B raw28746 raw28746Labels = mixedMoment B raw28746step0 raw28746step0Labels := by
      have hz : ∀ j, raw28746 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28746step0 = (fun i j => raw28746 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28746step0 raw28746; decide +kernel
      have hl : raw28746step0Labels = raw28746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28746 raw28746Labels permutation346 hz
    mixedMoment B raw28746step0 raw28746step0Labels = mixedMoment B raw28746step1 raw28746step1Labels := by
      have ha : raw28746step1 = (fun i j => raw28746step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28746step1 raw28746step0; decide +kernel
      have hl : raw28746step1Labels = raw28746step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28746step0 raw28746step0Labels permutation149 permutation7
    mixedMoment B raw28746step1 raw28746step1Labels = mixedMoment B raw28746step2 raw28746step2Labels := by
      have ha : raw28746step2 = raw28746step1 := by apply Matrix.ext; unfold raw28746step2 raw28746step1; decide +kernel
      have hl : raw28746step1Labels = labelEmbedding1 ∘ raw28746step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28746step1 raw28746step1Labels raw28746step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3268 node3268Labels := by rfl

def raw28747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28747step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28747step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28747step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28747 raw28747Labels = mixedMoment B node3255 node3255Labels := by
  calc
    mixedMoment B raw28747 raw28747Labels = mixedMoment B raw28747step0 raw28747step0Labels := by
      have ha : raw28747step0 = (fun i j => raw28747 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28747step0 raw28747; decide +kernel
      have hl : raw28747step0Labels = raw28747Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28747 raw28747Labels permutation674 permutation7
    mixedMoment B raw28747step0 raw28747step0Labels = mixedMoment B raw28747step1 raw28747step1Labels := by
      have ha : raw28747step1 = raw28747step0 := by apply Matrix.ext; unfold raw28747step1 raw28747step0; decide +kernel
      have hl : raw28747step0Labels = labelEmbedding1 ∘ raw28747step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28747step0 raw28747step0Labels raw28747step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3255 node3255Labels := by rfl

def raw28748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28748step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28748step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw28748step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28748 raw28748Labels = mixedMoment B node3264 node3264Labels := by
  calc
    mixedMoment B raw28748 raw28748Labels = mixedMoment B raw28748step0 raw28748step0Labels := by
      have hz : ∀ j, raw28748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28748step0 = (fun i j => raw28748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28748step0 raw28748; decide +kernel
      have hl : raw28748step0Labels = raw28748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28748 raw28748Labels permutation346 hz
    mixedMoment B raw28748step0 raw28748step0Labels = mixedMoment B raw28748step1 raw28748step1Labels := by
      have ha : raw28748step1 = (fun i j => raw28748step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28748step1 raw28748step0; decide +kernel
      have hl : raw28748step1Labels = raw28748step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28748step0 raw28748step0Labels permutation149 permutation7
    mixedMoment B raw28748step1 raw28748step1Labels = mixedMoment B raw28748step2 raw28748step2Labels := by
      have ha : raw28748step2 = raw28748step1 := by apply Matrix.ext; unfold raw28748step2 raw28748step1; decide +kernel
      have hl : raw28748step1Labels = labelEmbedding1 ∘ raw28748step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28748step1 raw28748step1Labels raw28748step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3264 node3264Labels := by rfl

def raw28749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw28749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw28749step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28749step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28749step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw28749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28749 raw28749Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw28749 raw28749Labels = mixedMoment B raw28749step0 raw28749step0Labels := by
      have hz : ∀ j, raw28749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28749step0 = (fun i j => raw28749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28749step0 raw28749; decide +kernel
      have hl : raw28749step0Labels = raw28749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28749 raw28749Labels permutation346 hz
    mixedMoment B raw28749step0 raw28749step0Labels = mixedMoment B raw28749step1 raw28749step1Labels := by
      have ha : raw28749step1 = (fun i j => raw28749step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28749step1 raw28749step0; decide +kernel
      have hl : raw28749step1Labels = raw28749step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28749step0 raw28749step0Labels permutation149 permutation7
    mixedMoment B raw28749step1 raw28749step1Labels = mixedMoment B raw28749step2 raw28749step2Labels := by
      have ha : raw28749step2 = raw28749step1 := by apply Matrix.ext; unfold raw28749step2 raw28749step1; decide +kernel
      have hl : raw28749step1Labels = labelEmbedding1 ∘ raw28749step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28749step1 raw28749step1Labels raw28749step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw28750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw28750step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28750 raw28750Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw28750 raw28750Labels = mixedMoment B raw28750step0 raw28750step0Labels := by
      have hz : ∀ j, raw28750 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28750step0 = (fun i j => raw28750 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28750step0 raw28750; decide +kernel
      have hl : raw28750step0Labels = raw28750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28750 raw28750Labels permutation346 hz
    mixedMoment B raw28750step0 raw28750step0Labels = mixedMoment B raw28750step1 raw28750step1Labels := by
      have ha : raw28750step1 = (fun i j => raw28750step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28750step1 raw28750step0; decide +kernel
      have hl : raw28750step1Labels = raw28750step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28750step0 raw28750step0Labels permutation151 permutation2
    mixedMoment B raw28750step1 raw28750step1Labels = mixedMoment B raw28750step2 raw28750step2Labels := by
      have ha : raw28750step2 = -raw28750step1 := by apply Matrix.ext; change ∀ i j, raw28750step2 i j = -(raw28750step1 i j); unfold raw28750step2 raw28750step1; decide +kernel
      have hl : raw28750step2Labels = raw28750step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw28751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28751 raw28751Labels = mixedMoment B node2347 node2347Labels := by
  calc
    mixedMoment B raw28751 raw28751Labels = mixedMoment B raw28751step0 raw28751step0Labels := by
      have ha : raw28751step0 = (fun i j => raw28751 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28751step0 raw28751; decide +kernel
      have hl : raw28751step0Labels = raw28751Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28751 raw28751Labels permutation158 permutation2
    _ = mixedMoment B node2347 node2347Labels := by rfl

def raw28752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28752 raw28752Labels = mixedMoment B node2355 node2355Labels := by
  calc
    mixedMoment B raw28752 raw28752Labels = mixedMoment B raw28752step0 raw28752step0Labels := by
      have hz : ∀ j, raw28752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28752step0 = (fun i j => raw28752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28752step0 raw28752; decide +kernel
      have hl : raw28752step0Labels = raw28752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28752 raw28752Labels permutation346 hz
    _ = mixedMoment B node2355 node2355Labels := by rfl

def raw28753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28753step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28753step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28753 raw28753Labels = mixedMoment B node2325 node2325Labels := by
  calc
    mixedMoment B raw28753 raw28753Labels = mixedMoment B raw28753step0 raw28753step0Labels := by
      have hz : ∀ j, raw28753 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28753step0 = (fun i j => raw28753 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28753step0 raw28753; decide +kernel
      have hl : raw28753step0Labels = raw28753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28753 raw28753Labels permutation346 hz
    mixedMoment B raw28753step0 raw28753step0Labels = mixedMoment B raw28753step1 raw28753step1Labels := by
      have ha : raw28753step1 = (fun i j => raw28753step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28753step1 raw28753step0; decide +kernel
      have hl : raw28753step1Labels = raw28753step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28753step0 raw28753step0Labels permutation151 permutation2
    mixedMoment B raw28753step1 raw28753step1Labels = mixedMoment B raw28753step2 raw28753step2Labels := by
      have ha : raw28753step2 = -raw28753step1 := by apply Matrix.ext; change ∀ i j, raw28753step2 i j = -(raw28753step1 i j); unfold raw28753step2 raw28753step1; decide +kernel
      have hl : raw28753step2Labels = raw28753step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2325 node2325Labels := by rfl

def raw28754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28754step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw28754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw28754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28754 raw28754Labels = mixedMoment B node1119 node1119Labels := by
  calc
    mixedMoment B raw28754 raw28754Labels = mixedMoment B raw28754step0 raw28754step0Labels := by
      have hz : ∀ j, raw28754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28754step0 = (fun i j => raw28754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28754step0 raw28754; decide +kernel
      have hl : raw28754step0Labels = raw28754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28754 raw28754Labels permutation346 hz
    mixedMoment B raw28754step0 raw28754step0Labels = mixedMoment B raw28754step1 raw28754step1Labels := by
      have ha : raw28754step1 = (fun i j => raw28754step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28754step1 raw28754step0; decide +kernel
      have hl : raw28754step1Labels = raw28754step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28754step0 raw28754step0Labels permutation151 permutation2
    mixedMoment B raw28754step1 raw28754step1Labels = mixedMoment B raw28754step2 raw28754step2Labels := by
      have ha : raw28754step2 = -raw28754step1 := by apply Matrix.ext; change ∀ i j, raw28754step2 i j = -(raw28754step1 i j); unfold raw28754step2 raw28754step1; decide +kernel
      have hl : raw28754step2Labels = raw28754step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1119 node1119Labels := by rfl

def raw28755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28755 raw28755Labels = mixedMoment B node2479 node2479Labels := by
  calc
    mixedMoment B raw28755 raw28755Labels = mixedMoment B raw28755step0 raw28755step0Labels := by
      have ha : raw28755step0 = (fun i j => raw28755 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28755step0 raw28755; decide +kernel
      have hl : raw28755step0Labels = raw28755Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28755 raw28755Labels permutation686 permutation2
    mixedMoment B raw28755step0 raw28755step0Labels = mixedMoment B raw28755step1 raw28755step1Labels := by
      have ha : raw28755step1 = -raw28755step0 := by apply Matrix.ext; change ∀ i j, raw28755step1 i j = -(raw28755step0 i j); unfold raw28755step1 raw28755step0; decide +kernel
      have hl : raw28755step1Labels = raw28755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2479 node2479Labels := by rfl

def raw28756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28756step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28756 raw28756Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw28756 raw28756Labels = mixedMoment B raw28756step0 raw28756step0Labels := by
      have hz : ∀ j, raw28756 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw28756step0 = (fun i j => raw28756 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw28756step0 raw28756; decide +kernel
      have hl : raw28756step0Labels = raw28756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28756 raw28756Labels permutation265 hz
    mixedMoment B raw28756step0 raw28756step0Labels = mixedMoment B raw28756step1 raw28756step1Labels := by
      have ha : raw28756step1 = (fun i j => raw28756step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28756step1 raw28756step0; decide +kernel
      have hl : raw28756step1Labels = raw28756step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28756step0 raw28756step0Labels permutation151 permutation2
    mixedMoment B raw28756step1 raw28756step1Labels = mixedMoment B raw28756step2 raw28756step2Labels := by
      have ha : raw28756step2 = -raw28756step1 := by apply Matrix.ext; change ∀ i j, raw28756step2 i j = -(raw28756step1 i j); unfold raw28756step2 raw28756step1; decide +kernel
      have hl : raw28756step2Labels = raw28756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw28757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28757step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28757 raw28757Labels = mixedMoment B node2436 node2436Labels := by
  calc
    mixedMoment B raw28757 raw28757Labels = mixedMoment B raw28757step0 raw28757step0Labels := by
      have ha : raw28757step0 = (fun i j => raw28757 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28757step0 raw28757; decide +kernel
      have hl : raw28757step0Labels = raw28757Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28757 raw28757Labels permutation686 permutation2
    mixedMoment B raw28757step0 raw28757step0Labels = mixedMoment B raw28757step1 raw28757step1Labels := by
      have ha : raw28757step1 = -raw28757step0 := by apply Matrix.ext; change ∀ i j, raw28757step1 i j = -(raw28757step0 i j); unfold raw28757step1 raw28757step0; decide +kernel
      have hl : raw28757step1Labels = raw28757step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2436 node2436Labels := by rfl

def raw28758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28758 raw28758Labels = mixedMoment B node2319 node2319Labels := by
  calc
    mixedMoment B raw28758 raw28758Labels = mixedMoment B raw28758step0 raw28758step0Labels := by
      have ha : raw28758step0 = (fun i j => raw28758 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28758step0 raw28758; decide +kernel
      have hl : raw28758step0Labels = raw28758Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28758 raw28758Labels permutation686 permutation2
    mixedMoment B raw28758step0 raw28758step0Labels = mixedMoment B raw28758step1 raw28758step1Labels := by
      have ha : raw28758step1 = -raw28758step0 := by apply Matrix.ext; change ∀ i j, raw28758step1 i j = -(raw28758step0 i j); unfold raw28758step1 raw28758step0; decide +kernel
      have hl : raw28758step1Labels = raw28758step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2319 node2319Labels := by rfl

def raw28759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw28759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28759 raw28759Labels = mixedMoment B node1111 node1111Labels := by
  calc
    mixedMoment B raw28759 raw28759Labels = mixedMoment B raw28759step0 raw28759step0Labels := by
      have ha : raw28759step0 = (fun i j => raw28759 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28759step0 raw28759; decide +kernel
      have hl : raw28759step0Labels = raw28759Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28759 raw28759Labels permutation686 permutation2
    mixedMoment B raw28759step0 raw28759step0Labels = mixedMoment B raw28759step1 raw28759step1Labels := by
      have ha : raw28759step1 = -raw28759step0 := by apply Matrix.ext; change ∀ i j, raw28759step1 i j = -(raw28759step0 i j); unfold raw28759step1 raw28759step0; decide +kernel
      have hl : raw28759step1Labels = raw28759step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1111 node1111Labels := by rfl

def raw28760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw28760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28760step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28760 raw28760Labels = mixedMoment B node2511 node2511Labels := by
  calc
    mixedMoment B raw28760 raw28760Labels = mixedMoment B raw28760step0 raw28760step0Labels := by
      have hz : ∀ j, raw28760 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28760step0 = (fun i j => raw28760 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28760step0 raw28760; decide +kernel
      have hl : raw28760step0Labels = raw28760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28760 raw28760Labels permutation346 hz
    mixedMoment B raw28760step0 raw28760step0Labels = mixedMoment B raw28760step1 raw28760step1Labels := by
      have ha : raw28760step1 = (fun i j => raw28760step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28760step1 raw28760step0; decide +kernel
      have hl : raw28760step1Labels = raw28760step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28760step0 raw28760step0Labels permutation149 permutation2
    mixedMoment B raw28760step1 raw28760step1Labels = mixedMoment B raw28760step2 raw28760step2Labels := by
      have ha : raw28760step2 = -raw28760step1 := by apply Matrix.ext; change ∀ i j, raw28760step2 i j = -(raw28760step1 i j); unfold raw28760step2 raw28760step1; decide +kernel
      have hl : raw28760step2Labels = raw28760step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2511 node2511Labels := by rfl

def raw28761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28761 raw28761Labels = mixedMoment B node2425 node2425Labels := by
  calc
    mixedMoment B raw28761 raw28761Labels = mixedMoment B raw28761step0 raw28761step0Labels := by
      have ha : raw28761step0 = (fun i j => raw28761 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28761step0 raw28761; decide +kernel
      have hl : raw28761step0Labels = raw28761Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28761 raw28761Labels permutation200 permutation2
    _ = mixedMoment B node2425 node2425Labels := by rfl

def raw28762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw28762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28762 raw28762Labels = mixedMoment B node2334 node2334Labels := by
  calc
    mixedMoment B raw28762 raw28762Labels = mixedMoment B raw28762step0 raw28762step0Labels := by
      have hz : ∀ j, raw28762 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28762step0 = (fun i j => raw28762 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28762step0 raw28762; decide +kernel
      have hl : raw28762step0Labels = raw28762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28762 raw28762Labels permutation346 hz
    mixedMoment B raw28762step0 raw28762step0Labels = mixedMoment B raw28762step1 raw28762step1Labels := by
      have ha : raw28762step1 = (fun i j => raw28762step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28762step1 raw28762step0; decide +kernel
      have hl : raw28762step1Labels = raw28762step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28762step0 raw28762step0Labels permutation149 permutation2
    mixedMoment B raw28762step1 raw28762step1Labels = mixedMoment B raw28762step2 raw28762step2Labels := by
      have ha : raw28762step2 = -raw28762step1 := by apply Matrix.ext; change ∀ i j, raw28762step2 i j = -(raw28762step1 i j); unfold raw28762step2 raw28762step1; decide +kernel
      have hl : raw28762step2Labels = raw28762step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2334 node2334Labels := by rfl

def raw28763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw28763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28763step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28763 raw28763Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw28763 raw28763Labels = mixedMoment B raw28763step0 raw28763step0Labels := by
      have hz : ∀ j, raw28763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28763step0 = (fun i j => raw28763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28763step0 raw28763; decide +kernel
      have hl : raw28763step0Labels = raw28763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28763 raw28763Labels permutation346 hz
    mixedMoment B raw28763step0 raw28763step0Labels = mixedMoment B raw28763step1 raw28763step1Labels := by
      have ha : raw28763step1 = (fun i j => raw28763step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28763step1 raw28763step0; decide +kernel
      have hl : raw28763step1Labels = raw28763step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28763step0 raw28763step0Labels permutation149 permutation2
    mixedMoment B raw28763step1 raw28763step1Labels = mixedMoment B raw28763step2 raw28763step2Labels := by
      have ha : raw28763step2 = -raw28763step1 := by apply Matrix.ext; change ∀ i j, raw28763step2 i j = -(raw28763step1 i j); unfold raw28763step2 raw28763step1; decide +kernel
      have hl : raw28763step2Labels = raw28763step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1131 node1131Labels := by rfl

def raw28764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28764step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28764step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28764step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28764 raw28764Labels = mixedMoment B node4322 node4322Labels := by
  calc
    mixedMoment B raw28764 raw28764Labels = mixedMoment B raw28764step0 raw28764step0Labels := by
      have ha : raw28764step0 = (fun i j => raw28764 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28764step0 raw28764; decide +kernel
      have hl : raw28764step0Labels = raw28764Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28764 raw28764Labels permutation158 permutation3
    mixedMoment B raw28764step0 raw28764step0Labels = mixedMoment B raw28764step1 raw28764step1Labels := by
      have ha : raw28764step1 = raw28764step0 := by apply Matrix.ext; unfold raw28764step1 raw28764step0; decide +kernel
      have hl : raw28764step0Labels = labelEmbedding6 ∘ raw28764step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28764step0 raw28764step0Labels raw28764step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4322 node4322Labels := by rfl

def raw28765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28765step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28765step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28765 raw28765Labels = mixedMoment B node4927 node4927Labels := by
  calc
    mixedMoment B raw28765 raw28765Labels = mixedMoment B raw28765step0 raw28765step0Labels := by
      have ha : raw28765step0 = (fun i j => raw28765 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28765step0 raw28765; decide +kernel
      have hl : raw28765step0Labels = raw28765Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28765 raw28765Labels permutation158 permutation3
    mixedMoment B raw28765step0 raw28765step0Labels = mixedMoment B raw28765step1 raw28765step1Labels := by
      have ha : raw28765step1 = raw28765step0 := by apply Matrix.ext; unfold raw28765step1 raw28765step0; decide +kernel
      have hl : raw28765step0Labels = labelEmbedding6 ∘ raw28765step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28765step0 raw28765step0Labels raw28765step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4927 node4927Labels := by rfl

def raw28766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28766step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28766step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28766 raw28766Labels = mixedMoment B node4986 node4986Labels := by
  calc
    mixedMoment B raw28766 raw28766Labels = mixedMoment B raw28766step0 raw28766step0Labels := by
      have ha : raw28766step0 = (fun i j => raw28766 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28766step0 raw28766; decide +kernel
      have hl : raw28766step0Labels = raw28766Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28766 raw28766Labels permutation200 permutation3
    mixedMoment B raw28766step0 raw28766step0Labels = mixedMoment B raw28766step1 raw28766step1Labels := by
      have ha : raw28766step1 = raw28766step0 := by apply Matrix.ext; unfold raw28766step1 raw28766step0; decide +kernel
      have hl : raw28766step0Labels = labelEmbedding6 ∘ raw28766step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28766step0 raw28766step0Labels raw28766step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4986 node4986Labels := by rfl

def raw28767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw28767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw28767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28767step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28767step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28767step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28767step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28767 raw28767Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw28767 raw28767Labels = mixedMoment B raw28767step0 raw28767step0Labels := by
      have hz : ∀ j, raw28767 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28767step0 = (fun i j => raw28767 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28767step0 raw28767; decide +kernel
      have hl : raw28767step0Labels = raw28767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28767 raw28767Labels permutation520 hz
    mixedMoment B raw28767step0 raw28767step0Labels = mixedMoment B raw28767step1 raw28767step1Labels := by
      have ha : raw28767step1 = (fun i j => raw28767step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28767step1 raw28767step0; decide +kernel
      have hl : raw28767step1Labels = raw28767step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28767step0 raw28767step0Labels permutation145 permutation3
    mixedMoment B raw28767step1 raw28767step1Labels = mixedMoment B raw28767step2 raw28767step2Labels := by
      have ha : raw28767step2 = -raw28767step1 := by apply Matrix.ext; change ∀ i j, raw28767step2 i j = -(raw28767step1 i j); unfold raw28767step2 raw28767step1; decide +kernel
      have hl : raw28767step2Labels = raw28767step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28767step2 raw28767step2Labels = mixedMoment B raw28767step3 raw28767step3Labels := by
      have ha : raw28767step3 = raw28767step2 := by apply Matrix.ext; unfold raw28767step3 raw28767step2; decide +kernel
      have hl : raw28767step2Labels = labelEmbedding6 ∘ raw28767step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28767step2 raw28767step2Labels raw28767step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw28768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28768step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28768step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28768 raw28768Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw28768 raw28768Labels = mixedMoment B raw28768step0 raw28768step0Labels := by
      have hz : ∀ j, raw28768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28768step0 = (fun i j => raw28768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28768step0 raw28768; decide +kernel
      have hl : raw28768step0Labels = raw28768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28768 raw28768Labels permutation346 hz
    mixedMoment B raw28768step0 raw28768step0Labels = mixedMoment B raw28768step1 raw28768step1Labels := by
      have ha : raw28768step1 = (fun i j => raw28768step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28768step1 raw28768step0; decide +kernel
      have hl : raw28768step1Labels = raw28768step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28768step0 raw28768step0Labels permutation32 permutation3
    mixedMoment B raw28768step1 raw28768step1Labels = mixedMoment B raw28768step2 raw28768step2Labels := by
      have ha : raw28768step2 = raw28768step1 := by apply Matrix.ext; unfold raw28768step2 raw28768step1; decide +kernel
      have hl : raw28768step1Labels = labelEmbedding6 ∘ raw28768step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28768step1 raw28768step1Labels raw28768step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4346 node4346Labels := by rfl

def raw28769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28769step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28769step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28769 raw28769Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw28769 raw28769Labels = mixedMoment B raw28769step0 raw28769step0Labels := by
      have hz : ∀ j, raw28769 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28769step0 = (fun i j => raw28769 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28769step0 raw28769; decide +kernel
      have hl : raw28769step0Labels = raw28769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28769 raw28769Labels permutation346 hz
    mixedMoment B raw28769step0 raw28769step0Labels = mixedMoment B raw28769step1 raw28769step1Labels := by
      have ha : raw28769step1 = (fun i j => raw28769step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28769step1 raw28769step0; decide +kernel
      have hl : raw28769step1Labels = raw28769step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28769step0 raw28769step0Labels permutation32 permutation3
    mixedMoment B raw28769step1 raw28769step1Labels = mixedMoment B raw28769step2 raw28769step2Labels := by
      have ha : raw28769step2 = raw28769step1 := by apply Matrix.ext; unfold raw28769step2 raw28769step1; decide +kernel
      have hl : raw28769step1Labels = labelEmbedding6 ∘ raw28769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28769step1 raw28769step1Labels raw28769step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4943 node4943Labels := by rfl

def raw28770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28770step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28770 raw28770Labels = mixedMoment B node5033 node5033Labels := by
  calc
    mixedMoment B raw28770 raw28770Labels = mixedMoment B raw28770step0 raw28770step0Labels := by
      have ha : raw28770step0 = (fun i j => raw28770 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28770step0 raw28770; decide +kernel
      have hl : raw28770step0Labels = raw28770Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28770 raw28770Labels permutation176 permutation3
    mixedMoment B raw28770step0 raw28770step0Labels = mixedMoment B raw28770step1 raw28770step1Labels := by
      have ha : raw28770step1 = raw28770step0 := by apply Matrix.ext; unfold raw28770step1 raw28770step0; decide +kernel
      have hl : raw28770step0Labels = labelEmbedding6 ∘ raw28770step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28770step0 raw28770step0Labels raw28770step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5033 node5033Labels := by rfl

def raw28771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw28771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw28771step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28771step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28771step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28771step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28771step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28771 raw28771Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw28771 raw28771Labels = mixedMoment B raw28771step0 raw28771step0Labels := by
      have hz : ∀ j, raw28771 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28771step0 = (fun i j => raw28771 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28771step0 raw28771; decide +kernel
      have hl : raw28771step0Labels = raw28771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28771 raw28771Labels permutation520 hz
    mixedMoment B raw28771step0 raw28771step0Labels = mixedMoment B raw28771step1 raw28771step1Labels := by
      have hz : ∀ j, raw28771step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28771step1 = (fun i j => raw28771step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28771step1 raw28771step0; decide +kernel
      have hl : raw28771step1Labels = raw28771step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28771step0 raw28771step0Labels permutation80 hz
    mixedMoment B raw28771step1 raw28771step1Labels = mixedMoment B raw28771step2 raw28771step2Labels := by
      have ha : raw28771step2 = (fun i j => raw28771step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28771step2 raw28771step1; decide +kernel
      have hl : raw28771step2Labels = raw28771step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28771step1 raw28771step1Labels permutation8 permutation3
    mixedMoment B raw28771step2 raw28771step2Labels = mixedMoment B raw28771step3 raw28771step3Labels := by
      have ha : raw28771step3 = raw28771step2 := by apply Matrix.ext; unfold raw28771step3 raw28771step2; decide +kernel
      have hl : raw28771step2Labels = labelEmbedding6 ∘ raw28771step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28771step2 raw28771step2Labels raw28771step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5171 node5171Labels := by rfl

def raw28772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw28772step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw28772step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28772 raw28772Labels = mixedMoment B node4325 node4325Labels := by
  calc
    mixedMoment B raw28772 raw28772Labels = mixedMoment B raw28772step0 raw28772step0Labels := by
      have hz : ∀ j, raw28772 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28772step0 = (fun i j => raw28772 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28772step0 raw28772; decide +kernel
      have hl : raw28772step0Labels = raw28772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28772 raw28772Labels permutation346 hz
    mixedMoment B raw28772step0 raw28772step0Labels = mixedMoment B raw28772step1 raw28772step1Labels := by
      have ha : raw28772step1 = (fun i j => raw28772step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28772step1 raw28772step0; decide +kernel
      have hl : raw28772step1Labels = raw28772step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28772step0 raw28772step0Labels permutation32 permutation3
    mixedMoment B raw28772step1 raw28772step1Labels = mixedMoment B raw28772step2 raw28772step2Labels := by
      have ha : raw28772step2 = raw28772step1 := by apply Matrix.ext; unfold raw28772step2 raw28772step1; decide +kernel
      have hl : raw28772step1Labels = labelEmbedding6 ∘ raw28772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28772step1 raw28772step1Labels raw28772step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4325 node4325Labels := by rfl

def raw28773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28773step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28773step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28773step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28773step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28773 raw28773Labels = mixedMoment B node4907 node4907Labels := by
  calc
    mixedMoment B raw28773 raw28773Labels = mixedMoment B raw28773step0 raw28773step0Labels := by
      have hz : ∀ j, raw28773 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28773step0 = (fun i j => raw28773 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28773step0 raw28773; decide +kernel
      have hl : raw28773step0Labels = raw28773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28773 raw28773Labels permutation346 hz
    mixedMoment B raw28773step0 raw28773step0Labels = mixedMoment B raw28773step1 raw28773step1Labels := by
      have ha : raw28773step1 = (fun i j => raw28773step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28773step1 raw28773step0; decide +kernel
      have hl : raw28773step1Labels = raw28773step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28773step0 raw28773step0Labels permutation151 permutation3
    mixedMoment B raw28773step1 raw28773step1Labels = mixedMoment B raw28773step2 raw28773step2Labels := by
      have ha : raw28773step2 = -raw28773step1 := by apply Matrix.ext; change ∀ i j, raw28773step2 i j = -(raw28773step1 i j); unfold raw28773step2 raw28773step1; decide +kernel
      have hl : raw28773step2Labels = raw28773step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28773step2 raw28773step2Labels = mixedMoment B raw28773step3 raw28773step3Labels := by
      have ha : raw28773step3 = raw28773step2 := by apply Matrix.ext; unfold raw28773step3 raw28773step2; decide +kernel
      have hl : raw28773step2Labels = labelEmbedding6 ∘ raw28773step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28773step2 raw28773step2Labels raw28773step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4907 node4907Labels := by rfl

def raw28774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28774step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28774step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28774step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28774step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28774 raw28774Labels = mixedMoment B node4902 node4902Labels := by
  calc
    mixedMoment B raw28774 raw28774Labels = mixedMoment B raw28774step0 raw28774step0Labels := by
      have ha : raw28774step0 = (fun i j => raw28774 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28774step0 raw28774; decide +kernel
      have hl : raw28774step0Labels = raw28774Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28774 raw28774Labels permutation686 permutation3
    mixedMoment B raw28774step0 raw28774step0Labels = mixedMoment B raw28774step1 raw28774step1Labels := by
      have ha : raw28774step1 = -raw28774step0 := by apply Matrix.ext; change ∀ i j, raw28774step1 i j = -(raw28774step0 i j); unfold raw28774step1 raw28774step0; decide +kernel
      have hl : raw28774step1Labels = raw28774step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28774step1 raw28774step1Labels = mixedMoment B raw28774step2 raw28774step2Labels := by
      have ha : raw28774step2 = raw28774step1 := by apply Matrix.ext; unfold raw28774step2 raw28774step1; decide +kernel
      have hl : raw28774step1Labels = labelEmbedding6 ∘ raw28774step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28774step1 raw28774step1Labels raw28774step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4902 node4902Labels := by rfl

def raw28775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28775step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28775step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28775step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28775step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28775 raw28775Labels = mixedMoment B node4913 node4913Labels := by
  calc
    mixedMoment B raw28775 raw28775Labels = mixedMoment B raw28775step0 raw28775step0Labels := by
      have hz : ∀ j, raw28775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28775step0 = (fun i j => raw28775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28775step0 raw28775; decide +kernel
      have hl : raw28775step0Labels = raw28775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28775 raw28775Labels permutation346 hz
    mixedMoment B raw28775step0 raw28775step0Labels = mixedMoment B raw28775step1 raw28775step1Labels := by
      have ha : raw28775step1 = (fun i j => raw28775step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28775step1 raw28775step0; decide +kernel
      have hl : raw28775step1Labels = raw28775step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28775step0 raw28775step0Labels permutation149 permutation3
    mixedMoment B raw28775step1 raw28775step1Labels = mixedMoment B raw28775step2 raw28775step2Labels := by
      have ha : raw28775step2 = -raw28775step1 := by apply Matrix.ext; change ∀ i j, raw28775step2 i j = -(raw28775step1 i j); unfold raw28775step2 raw28775step1; decide +kernel
      have hl : raw28775step2Labels = raw28775step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28775step2 raw28775step2Labels = mixedMoment B raw28775step3 raw28775step3Labels := by
      have ha : raw28775step3 = raw28775step2 := by apply Matrix.ext; unfold raw28775step3 raw28775step2; decide +kernel
      have hl : raw28775step2Labels = labelEmbedding6 ∘ raw28775step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28775step2 raw28775step2Labels raw28775step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4913 node4913Labels := by rfl

def raw28776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw28776step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28776step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28776step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28776step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28776step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28776 raw28776Labels = mixedMoment B node4289 node4289Labels := by
  calc
    mixedMoment B raw28776 raw28776Labels = mixedMoment B raw28776step0 raw28776step0Labels := by
      have hz : ∀ j, raw28776 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28776step0 = (fun i j => raw28776 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28776step0 raw28776; decide +kernel
      have hl : raw28776step0Labels = raw28776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28776 raw28776Labels permutation346 hz
    mixedMoment B raw28776step0 raw28776step0Labels = mixedMoment B raw28776step1 raw28776step1Labels := by
      have ha : raw28776step1 = (fun i j => raw28776step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28776step1 raw28776step0; decide +kernel
      have hl : raw28776step1Labels = raw28776step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28776step0 raw28776step0Labels permutation151 permutation3
    mixedMoment B raw28776step1 raw28776step1Labels = mixedMoment B raw28776step2 raw28776step2Labels := by
      have ha : raw28776step2 = -raw28776step1 := by apply Matrix.ext; change ∀ i j, raw28776step2 i j = -(raw28776step1 i j); unfold raw28776step2 raw28776step1; decide +kernel
      have hl : raw28776step2Labels = raw28776step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28776step2 raw28776step2Labels = mixedMoment B raw28776step3 raw28776step3Labels := by
      have ha : raw28776step3 = raw28776step2 := by apply Matrix.ext; unfold raw28776step3 raw28776step2; decide +kernel
      have hl : raw28776step2Labels = labelEmbedding6 ∘ raw28776step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28776step2 raw28776step2Labels raw28776step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4289 node4289Labels := by rfl

def raw28777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28777step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28777step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28777step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28777step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28777 raw28777Labels = mixedMoment B node4295 node4295Labels := by
  calc
    mixedMoment B raw28777 raw28777Labels = mixedMoment B raw28777step0 raw28777step0Labels := by
      have hz : ∀ j, raw28777 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28777step0 = (fun i j => raw28777 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28777step0 raw28777; decide +kernel
      have hl : raw28777step0Labels = raw28777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28777 raw28777Labels permutation346 hz
    mixedMoment B raw28777step0 raw28777step0Labels = mixedMoment B raw28777step1 raw28777step1Labels := by
      have ha : raw28777step1 = (fun i j => raw28777step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28777step1 raw28777step0; decide +kernel
      have hl : raw28777step1Labels = raw28777step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28777step0 raw28777step0Labels permutation151 permutation3
    mixedMoment B raw28777step1 raw28777step1Labels = mixedMoment B raw28777step2 raw28777step2Labels := by
      have ha : raw28777step2 = -raw28777step1 := by apply Matrix.ext; change ∀ i j, raw28777step2 i j = -(raw28777step1 i j); unfold raw28777step2 raw28777step1; decide +kernel
      have hl : raw28777step2Labels = raw28777step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28777step2 raw28777step2Labels = mixedMoment B raw28777step3 raw28777step3Labels := by
      have ha : raw28777step3 = raw28777step2 := by apply Matrix.ext; unfold raw28777step3 raw28777step2; decide +kernel
      have hl : raw28777step2Labels = labelEmbedding6 ∘ raw28777step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28777step2 raw28777step2Labels raw28777step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4295 node4295Labels := by rfl

def raw28778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28778step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28778step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28778step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28778step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28778 raw28778Labels = mixedMoment B node4287 node4287Labels := by
  calc
    mixedMoment B raw28778 raw28778Labels = mixedMoment B raw28778step0 raw28778step0Labels := by
      have ha : raw28778step0 = (fun i j => raw28778 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28778step0 raw28778; decide +kernel
      have hl : raw28778step0Labels = raw28778Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28778 raw28778Labels permutation686 permutation3
    mixedMoment B raw28778step0 raw28778step0Labels = mixedMoment B raw28778step1 raw28778step1Labels := by
      have ha : raw28778step1 = -raw28778step0 := by apply Matrix.ext; change ∀ i j, raw28778step1 i j = -(raw28778step0 i j); unfold raw28778step1 raw28778step0; decide +kernel
      have hl : raw28778step1Labels = raw28778step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28778step1 raw28778step1Labels = mixedMoment B raw28778step2 raw28778step2Labels := by
      have ha : raw28778step2 = raw28778step1 := by apply Matrix.ext; unfold raw28778step2 raw28778step1; decide +kernel
      have hl : raw28778step1Labels = labelEmbedding6 ∘ raw28778step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28778step1 raw28778step1Labels raw28778step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4287 node4287Labels := by rfl

def raw28779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28779step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28779step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28779step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28779step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28779 raw28779Labels = mixedMoment B node4303 node4303Labels := by
  calc
    mixedMoment B raw28779 raw28779Labels = mixedMoment B raw28779step0 raw28779step0Labels := by
      have hz : ∀ j, raw28779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28779step0 = (fun i j => raw28779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28779step0 raw28779; decide +kernel
      have hl : raw28779step0Labels = raw28779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28779 raw28779Labels permutation346 hz
    mixedMoment B raw28779step0 raw28779step0Labels = mixedMoment B raw28779step1 raw28779step1Labels := by
      have ha : raw28779step1 = (fun i j => raw28779step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28779step1 raw28779step0; decide +kernel
      have hl : raw28779step1Labels = raw28779step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28779step0 raw28779step0Labels permutation149 permutation3
    mixedMoment B raw28779step1 raw28779step1Labels = mixedMoment B raw28779step2 raw28779step2Labels := by
      have ha : raw28779step2 = -raw28779step1 := by apply Matrix.ext; change ∀ i j, raw28779step2 i j = -(raw28779step1 i j); unfold raw28779step2 raw28779step1; decide +kernel
      have hl : raw28779step2Labels = raw28779step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28779step2 raw28779step2Labels = mixedMoment B raw28779step3 raw28779step3Labels := by
      have ha : raw28779step3 = raw28779step2 := by apply Matrix.ext; unfold raw28779step3 raw28779step2; decide +kernel
      have hl : raw28779step2Labels = labelEmbedding6 ∘ raw28779step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28779step2 raw28779step2Labels raw28779step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4303 node4303Labels := by rfl

def raw28780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![4, -3, -1]]
def raw28780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw28780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![4, -3, -1]]
def raw28780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28780step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28780step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28780step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28780step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28780step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28780step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28780 raw28780Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw28780 raw28780Labels = mixedMoment B raw28780step0 raw28780step0Labels := by
      have hz : ∀ j, raw28780 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28780step0 = (fun i j => raw28780 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28780step0 raw28780; decide +kernel
      have hl : raw28780step0Labels = raw28780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28780 raw28780Labels permutation520 hz
    mixedMoment B raw28780step0 raw28780step0Labels = mixedMoment B raw28780step1 raw28780step1Labels := by
      have hz : ∀ j, raw28780step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28780step1 = (fun i j => raw28780step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28780step1 raw28780step0; decide +kernel
      have hl : raw28780step1Labels = raw28780step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28780step0 raw28780step0Labels permutation80 hz
    mixedMoment B raw28780step1 raw28780step1Labels = mixedMoment B raw28780step2 raw28780step2Labels := by
      have ha : raw28780step2 = (fun i j => raw28780step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28780step2 raw28780step1; decide +kernel
      have hl : raw28780step2Labels = raw28780step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28780step1 raw28780step1Labels permutation31 permutation3
    mixedMoment B raw28780step2 raw28780step2Labels = mixedMoment B raw28780step3 raw28780step3Labels := by
      have ha : raw28780step3 = -raw28780step2 := by apply Matrix.ext; change ∀ i j, raw28780step3 i j = -(raw28780step2 i j); unfold raw28780step3 raw28780step2; decide +kernel
      have hl : raw28780step3Labels = raw28780step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28780step3 raw28780step3Labels = mixedMoment B raw28780step4 raw28780step4Labels := by
      have ha : raw28780step4 = raw28780step3 := by apply Matrix.ext; unfold raw28780step4 raw28780step3; decide +kernel
      have hl : raw28780step3Labels = labelEmbedding6 ∘ raw28780step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28780step3 raw28780step3Labels raw28780step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw28781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28781step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28781 raw28781Labels = mixedMoment B node900 node900Labels := by
  calc
    mixedMoment B raw28781 raw28781Labels = mixedMoment B raw28781step0 raw28781step0Labels := by
      have ha : raw28781step0 = (fun i j => raw28781 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28781step0 raw28781; decide +kernel
      have hl : raw28781step0Labels = raw28781Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28781 raw28781Labels permutation158 permutation3
    _ = mixedMoment B node900 node900Labels := by rfl

def raw28782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28782step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28782 raw28782Labels = mixedMoment B node2317 node2317Labels := by
  calc
    mixedMoment B raw28782 raw28782Labels = mixedMoment B raw28782step0 raw28782step0Labels := by
      have ha : raw28782step0 = (fun i j => raw28782 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28782step0 raw28782; decide +kernel
      have hl : raw28782step0Labels = raw28782Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28782 raw28782Labels permutation158 permutation3
    _ = mixedMoment B node2317 node2317Labels := by rfl

def raw28783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28783step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28783 raw28783Labels = mixedMoment B node2371 node2371Labels := by
  calc
    mixedMoment B raw28783 raw28783Labels = mixedMoment B raw28783step0 raw28783step0Labels := by
      have ha : raw28783step0 = (fun i j => raw28783 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28783step0 raw28783; decide +kernel
      have hl : raw28783step0Labels = raw28783Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28783 raw28783Labels permutation200 permutation3
    _ = mixedMoment B node2371 node2371Labels := by rfl

def raw28784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw28784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw28784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28784step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28784 raw28784Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw28784 raw28784Labels = mixedMoment B raw28784step0 raw28784step0Labels := by
      have hz : ∀ j, raw28784 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28784step0 = (fun i j => raw28784 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28784step0 raw28784; decide +kernel
      have hl : raw28784step0Labels = raw28784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28784 raw28784Labels permutation520 hz
    mixedMoment B raw28784step0 raw28784step0Labels = mixedMoment B raw28784step1 raw28784step1Labels := by
      have ha : raw28784step1 = (fun i j => raw28784step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28784step1 raw28784step0; decide +kernel
      have hl : raw28784step1Labels = raw28784step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28784step0 raw28784step0Labels permutation145 permutation3
    mixedMoment B raw28784step1 raw28784step1Labels = mixedMoment B raw28784step2 raw28784step2Labels := by
      have ha : raw28784step2 = -raw28784step1 := by apply Matrix.ext; change ∀ i j, raw28784step2 i j = -(raw28784step1 i j); unfold raw28784step2 raw28784step1; decide +kernel
      have hl : raw28784step2Labels = raw28784step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw28785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28785 raw28785Labels = mixedMoment B node924 node924Labels := by
  calc
    mixedMoment B raw28785 raw28785Labels = mixedMoment B raw28785step0 raw28785step0Labels := by
      have hz : ∀ j, raw28785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28785step0 = (fun i j => raw28785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28785step0 raw28785; decide +kernel
      have hl : raw28785step0Labels = raw28785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28785 raw28785Labels permutation346 hz
    mixedMoment B raw28785step0 raw28785step0Labels = mixedMoment B raw28785step1 raw28785step1Labels := by
      have ha : raw28785step1 = (fun i j => raw28785step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28785step1 raw28785step0; decide +kernel
      have hl : raw28785step1Labels = raw28785step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28785step0 raw28785step0Labels permutation32 permutation3
    _ = mixedMoment B node924 node924Labels := by rfl

def raw28786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28786 raw28786Labels = mixedMoment B node2334 node2334Labels := by
  calc
    mixedMoment B raw28786 raw28786Labels = mixedMoment B raw28786step0 raw28786step0Labels := by
      have hz : ∀ j, raw28786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28786step0 = (fun i j => raw28786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28786step0 raw28786; decide +kernel
      have hl : raw28786step0Labels = raw28786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28786 raw28786Labels permutation346 hz
    mixedMoment B raw28786step0 raw28786step0Labels = mixedMoment B raw28786step1 raw28786step1Labels := by
      have ha : raw28786step1 = (fun i j => raw28786step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28786step1 raw28786step0; decide +kernel
      have hl : raw28786step1Labels = raw28786step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28786step0 raw28786step0Labels permutation32 permutation3
    _ = mixedMoment B node2334 node2334Labels := by rfl

def raw28787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28787 raw28787Labels = mixedMoment B node2425 node2425Labels := by
  calc
    mixedMoment B raw28787 raw28787Labels = mixedMoment B raw28787step0 raw28787step0Labels := by
      have ha : raw28787step0 = (fun i j => raw28787 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28787step0 raw28787; decide +kernel
      have hl : raw28787step0Labels = raw28787Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28787 raw28787Labels permutation176 permutation3
    _ = mixedMoment B node2425 node2425Labels := by rfl

def raw28788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw28788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw28788step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28788step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw28788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28788 raw28788Labels = mixedMoment B node2598 node2598Labels := by
  calc
    mixedMoment B raw28788 raw28788Labels = mixedMoment B raw28788step0 raw28788step0Labels := by
      have hz : ∀ j, raw28788 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28788step0 = (fun i j => raw28788 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28788step0 raw28788; decide +kernel
      have hl : raw28788step0Labels = raw28788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28788 raw28788Labels permutation520 hz
    mixedMoment B raw28788step0 raw28788step0Labels = mixedMoment B raw28788step1 raw28788step1Labels := by
      have hz : ∀ j, raw28788step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28788step1 = (fun i j => raw28788step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28788step1 raw28788step0; decide +kernel
      have hl : raw28788step1Labels = raw28788step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28788step0 raw28788step0Labels permutation80 hz
    mixedMoment B raw28788step1 raw28788step1Labels = mixedMoment B raw28788step2 raw28788step2Labels := by
      have ha : raw28788step2 = (fun i j => raw28788step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28788step2 raw28788step1; decide +kernel
      have hl : raw28788step2Labels = raw28788step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28788step1 raw28788step1Labels permutation8 permutation3
    _ = mixedMoment B node2598 node2598Labels := by rfl

def raw28789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw28789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28789 raw28789Labels = mixedMoment B node903 node903Labels := by
  calc
    mixedMoment B raw28789 raw28789Labels = mixedMoment B raw28789step0 raw28789step0Labels := by
      have hz : ∀ j, raw28789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28789step0 = (fun i j => raw28789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28789step0 raw28789; decide +kernel
      have hl : raw28789step0Labels = raw28789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28789 raw28789Labels permutation346 hz
    mixedMoment B raw28789step0 raw28789step0Labels = mixedMoment B raw28789step1 raw28789step1Labels := by
      have ha : raw28789step1 = (fun i j => raw28789step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28789step1 raw28789step0; decide +kernel
      have hl : raw28789step1Labels = raw28789step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28789step0 raw28789step0Labels permutation32 permutation3
    _ = mixedMoment B node903 node903Labels := by rfl

def raw28790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28790step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28790step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28790step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28790step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28790 raw28790Labels = mixedMoment B node2300 node2300Labels := by
  calc
    mixedMoment B raw28790 raw28790Labels = mixedMoment B raw28790step0 raw28790step0Labels := by
      have hz : ∀ j, raw28790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28790step0 = (fun i j => raw28790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28790step0 raw28790; decide +kernel
      have hl : raw28790step0Labels = raw28790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28790 raw28790Labels permutation346 hz
    mixedMoment B raw28790step0 raw28790step0Labels = mixedMoment B raw28790step1 raw28790step1Labels := by
      have ha : raw28790step1 = (fun i j => raw28790step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28790step1 raw28790step0; decide +kernel
      have hl : raw28790step1Labels = raw28790step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28790step0 raw28790step0Labels permutation151 permutation3
    mixedMoment B raw28790step1 raw28790step1Labels = mixedMoment B raw28790step2 raw28790step2Labels := by
      have ha : raw28790step2 = -raw28790step1 := by apply Matrix.ext; change ∀ i j, raw28790step2 i j = -(raw28790step1 i j); unfold raw28790step2 raw28790step1; decide +kernel
      have hl : raw28790step2Labels = raw28790step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2300 node2300Labels := by rfl

def raw28791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28791step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28791step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28791 raw28791Labels = mixedMoment B node2295 node2295Labels := by
  calc
    mixedMoment B raw28791 raw28791Labels = mixedMoment B raw28791step0 raw28791step0Labels := by
      have ha : raw28791step0 = (fun i j => raw28791 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28791step0 raw28791; decide +kernel
      have hl : raw28791step0Labels = raw28791Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28791 raw28791Labels permutation686 permutation3
    mixedMoment B raw28791step0 raw28791step0Labels = mixedMoment B raw28791step1 raw28791step1Labels := by
      have ha : raw28791step1 = -raw28791step0 := by apply Matrix.ext; change ∀ i j, raw28791step1 i j = -(raw28791step0 i j); unfold raw28791step1 raw28791step0; decide +kernel
      have hl : raw28791step1Labels = raw28791step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2295 node2295Labels := by rfl

def raw28792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28792Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28792step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28792step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28792 raw28792Labels = mixedMoment B node2306 node2306Labels := by
  calc
    mixedMoment B raw28792 raw28792Labels = mixedMoment B raw28792step0 raw28792step0Labels := by
      have hz : ∀ j, raw28792 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28792step0 = (fun i j => raw28792 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28792step0 raw28792; decide +kernel
      have hl : raw28792step0Labels = raw28792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28792 raw28792Labels permutation346 hz
    mixedMoment B raw28792step0 raw28792step0Labels = mixedMoment B raw28792step1 raw28792step1Labels := by
      have ha : raw28792step1 = (fun i j => raw28792step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28792step1 raw28792step0; decide +kernel
      have hl : raw28792step1Labels = raw28792step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28792step0 raw28792step0Labels permutation149 permutation3
    mixedMoment B raw28792step1 raw28792step1Labels = mixedMoment B raw28792step2 raw28792step2Labels := by
      have ha : raw28792step2 = -raw28792step1 := by apply Matrix.ext; change ∀ i j, raw28792step2 i j = -(raw28792step1 i j); unfold raw28792step2 raw28792step1; decide +kernel
      have hl : raw28792step2Labels = raw28792step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2306 node2306Labels := by rfl

def raw28793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28793Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28793step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw28793step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw28793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28793 raw28793Labels = mixedMoment B node867 node867Labels := by
  calc
    mixedMoment B raw28793 raw28793Labels = mixedMoment B raw28793step0 raw28793step0Labels := by
      have hz : ∀ j, raw28793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28793step0 = (fun i j => raw28793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28793step0 raw28793; decide +kernel
      have hl : raw28793step0Labels = raw28793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28793 raw28793Labels permutation346 hz
    mixedMoment B raw28793step0 raw28793step0Labels = mixedMoment B raw28793step1 raw28793step1Labels := by
      have ha : raw28793step1 = (fun i j => raw28793step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28793step1 raw28793step0; decide +kernel
      have hl : raw28793step1Labels = raw28793step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28793step0 raw28793step0Labels permutation151 permutation3
    mixedMoment B raw28793step1 raw28793step1Labels = mixedMoment B raw28793step2 raw28793step2Labels := by
      have ha : raw28793step2 = -raw28793step1 := by apply Matrix.ext; change ∀ i j, raw28793step2 i j = -(raw28793step1 i j); unfold raw28793step2 raw28793step1; decide +kernel
      have hl : raw28793step2Labels = raw28793step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node867 node867Labels := by rfl

def raw28794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28794Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28794step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw28794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28794step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw28794step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28794 raw28794Labels = mixedMoment B node873 node873Labels := by
  calc
    mixedMoment B raw28794 raw28794Labels = mixedMoment B raw28794step0 raw28794step0Labels := by
      have hz : ∀ j, raw28794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28794step0 = (fun i j => raw28794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28794step0 raw28794; decide +kernel
      have hl : raw28794step0Labels = raw28794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28794 raw28794Labels permutation346 hz
    mixedMoment B raw28794step0 raw28794step0Labels = mixedMoment B raw28794step1 raw28794step1Labels := by
      have ha : raw28794step1 = (fun i j => raw28794step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28794step1 raw28794step0; decide +kernel
      have hl : raw28794step1Labels = raw28794step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28794step0 raw28794step0Labels permutation151 permutation3
    mixedMoment B raw28794step1 raw28794step1Labels = mixedMoment B raw28794step2 raw28794step2Labels := by
      have ha : raw28794step2 = -raw28794step1 := by apply Matrix.ext; change ∀ i j, raw28794step2 i j = -(raw28794step1 i j); unfold raw28794step2 raw28794step1; decide +kernel
      have hl : raw28794step2Labels = raw28794step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node873 node873Labels := by rfl

def raw28795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28795Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28795step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28795 raw28795Labels = mixedMoment B node865 node865Labels := by
  calc
    mixedMoment B raw28795 raw28795Labels = mixedMoment B raw28795step0 raw28795step0Labels := by
      have ha : raw28795step0 = (fun i j => raw28795 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28795step0 raw28795; decide +kernel
      have hl : raw28795step0Labels = raw28795Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28795 raw28795Labels permutation686 permutation3
    mixedMoment B raw28795step0 raw28795step0Labels = mixedMoment B raw28795step1 raw28795step1Labels := by
      have ha : raw28795step1 = -raw28795step0 := by apply Matrix.ext; change ∀ i j, raw28795step1 i j = -(raw28795step0 i j); unfold raw28795step1 raw28795step0; decide +kernel
      have hl : raw28795step1Labels = raw28795step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node865 node865Labels := by rfl

def raw28796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28796Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28796step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28796step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28796 raw28796Labels = mixedMoment B node881 node881Labels := by
  calc
    mixedMoment B raw28796 raw28796Labels = mixedMoment B raw28796step0 raw28796step0Labels := by
      have hz : ∀ j, raw28796 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28796step0 = (fun i j => raw28796 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28796step0 raw28796; decide +kernel
      have hl : raw28796step0Labels = raw28796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28796 raw28796Labels permutation346 hz
    mixedMoment B raw28796step0 raw28796step0Labels = mixedMoment B raw28796step1 raw28796step1Labels := by
      have ha : raw28796step1 = (fun i j => raw28796step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28796step1 raw28796step0; decide +kernel
      have hl : raw28796step1Labels = raw28796step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28796step0 raw28796step0Labels permutation149 permutation3
    mixedMoment B raw28796step1 raw28796step1Labels = mixedMoment B raw28796step2 raw28796step2Labels := by
      have ha : raw28796step2 = -raw28796step1 := by apply Matrix.ext; change ∀ i j, raw28796step2 i j = -(raw28796step1 i j); unfold raw28796step2 raw28796step1; decide +kernel
      have hl : raw28796step2Labels = raw28796step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node881 node881Labels := by rfl

def raw28797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![4, -3, -1]]
def raw28797Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw28797step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![4, -3, -1]]
def raw28797step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28797step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28797step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28797step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28797 raw28797Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw28797 raw28797Labels = mixedMoment B raw28797step0 raw28797step0Labels := by
      have hz : ∀ j, raw28797 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28797step0 = (fun i j => raw28797 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28797step0 raw28797; decide +kernel
      have hl : raw28797step0Labels = raw28797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28797 raw28797Labels permutation520 hz
    mixedMoment B raw28797step0 raw28797step0Labels = mixedMoment B raw28797step1 raw28797step1Labels := by
      have hz : ∀ j, raw28797step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28797step1 = (fun i j => raw28797step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28797step1 raw28797step0; decide +kernel
      have hl : raw28797step1Labels = raw28797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28797step0 raw28797step0Labels permutation80 hz
    mixedMoment B raw28797step1 raw28797step1Labels = mixedMoment B raw28797step2 raw28797step2Labels := by
      have ha : raw28797step2 = (fun i j => raw28797step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28797step2 raw28797step1; decide +kernel
      have hl : raw28797step2Labels = raw28797step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28797step1 raw28797step1Labels permutation31 permutation3
    mixedMoment B raw28797step2 raw28797step2Labels = mixedMoment B raw28797step3 raw28797step3Labels := by
      have ha : raw28797step3 = -raw28797step2 := by apply Matrix.ext; change ∀ i j, raw28797step3 i j = -(raw28797step2 i j); unfold raw28797step3 raw28797step2; decide +kernel
      have hl : raw28797step3Labels = raw28797step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1043 node1043Labels := by rfl

def raw28798 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw28798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw28798step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28798step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28798step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28798step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28798step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28798 raw28798Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw28798 raw28798Labels = mixedMoment B raw28798step0 raw28798step0Labels := by
      have hz : ∀ j, raw28798 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28798step0 = (fun i j => raw28798 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28798step0 raw28798; decide +kernel
      have hl : raw28798step0Labels = raw28798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28798 raw28798Labels permutation346 hz
    mixedMoment B raw28798step0 raw28798step0Labels = mixedMoment B raw28798step1 raw28798step1Labels := by
      have ha : raw28798step1 = (fun i j => raw28798step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28798step1 raw28798step0; decide +kernel
      have hl : raw28798step1Labels = raw28798step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28798step0 raw28798step0Labels permutation151 permutation6
    mixedMoment B raw28798step1 raw28798step1Labels = mixedMoment B raw28798step2 raw28798step2Labels := by
      have ha : raw28798step2 = -raw28798step1 := by apply Matrix.ext; change ∀ i j, raw28798step2 i j = -(raw28798step1 i j); unfold raw28798step2 raw28798step1; decide +kernel
      have hl : raw28798step2Labels = raw28798step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28798step2 raw28798step2Labels = mixedMoment B raw28798step3 raw28798step3Labels := by
      have ha : raw28798step3 = raw28798step2 := by apply Matrix.ext; unfold raw28798step3 raw28798step2; decide +kernel
      have hl : raw28798step2Labels = labelEmbedding9 ∘ raw28798step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28798step2 raw28798step2Labels raw28798step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw28799 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw28799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw28799step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28799step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28799step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28799step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28799step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28799 raw28799Labels = mixedMoment B node5065 node5065Labels := by
  calc
    mixedMoment B raw28799 raw28799Labels = mixedMoment B raw28799step0 raw28799step0Labels := by
      have ha : raw28799step0 = (fun i j => raw28799 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28799step0 raw28799; decide +kernel
      have hl : raw28799step0Labels = raw28799Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28799 raw28799Labels permutation682 permutation6
    mixedMoment B raw28799step0 raw28799step0Labels = mixedMoment B raw28799step1 raw28799step1Labels := by
      have ha : raw28799step1 = -raw28799step0 := by apply Matrix.ext; change ∀ i j, raw28799step1 i j = -(raw28799step0 i j); unfold raw28799step1 raw28799step0; decide +kernel
      have hl : raw28799step1Labels = raw28799step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28799step1 raw28799step1Labels = mixedMoment B raw28799step2 raw28799step2Labels := by
      have ha : raw28799step2 = raw28799step1 := by apply Matrix.ext; unfold raw28799step2 raw28799step1; decide +kernel
      have hl : raw28799step1Labels = labelEmbedding9 ∘ raw28799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28799step1 raw28799step1Labels raw28799step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5065 node5065Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
