import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw31360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw31360Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -1, -2], ![1, -1, 0]]
def raw31360step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw31360step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31360step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw31360step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31360step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw31360step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31360 raw31360Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw31360 raw31360Labels = mixedMoment B raw31360step0 raw31360step0Labels := by
      have hz : ∀ j, raw31360 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31360step0 = (fun i j => raw31360 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31360step0 raw31360; decide +kernel
      have hl : raw31360step0Labels = raw31360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31360 raw31360Labels permutation434 hz
    mixedMoment B raw31360step0 raw31360step0Labels = mixedMoment B raw31360step1 raw31360step1Labels := by
      have ha : raw31360step1 = (fun i j => raw31360step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31360step1 raw31360step0; decide +kernel
      have hl : raw31360step1Labels = raw31360step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31360step0 raw31360step0Labels permutation36 permutation7
    mixedMoment B raw31360step1 raw31360step1Labels = mixedMoment B raw31360step2 raw31360step2Labels := by
      have ha : raw31360step2 = -raw31360step1 := by apply Matrix.ext; change ∀ i j, raw31360step2 i j = -(raw31360step1 i j); unfold raw31360step2 raw31360step1; decide +kernel
      have hl : raw31360step2Labels = raw31360step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31360step2 raw31360step2Labels = mixedMoment B raw31360step3 raw31360step3Labels := by
      have ha : raw31360step3 = raw31360step2 := by apply Matrix.ext; unfold raw31360step3 raw31360step2; decide +kernel
      have hl : raw31360step2Labels = labelEmbedding1 ∘ raw31360step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31360step2 raw31360step2Labels raw31360step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw31361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31361Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31361step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw31361step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31361step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw31361step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31361step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw31361step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31361 raw31361Labels = mixedMoment B node1685 node1685Labels := by
  calc
    mixedMoment B raw31361 raw31361Labels = mixedMoment B raw31361step0 raw31361step0Labels := by
      have hz : ∀ j, raw31361 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31361step0 = (fun i j => raw31361 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31361step0 raw31361; decide +kernel
      have hl : raw31361step0Labels = raw31361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31361 raw31361Labels permutation434 hz
    mixedMoment B raw31361step0 raw31361step0Labels = mixedMoment B raw31361step1 raw31361step1Labels := by
      have ha : raw31361step1 = (fun i j => raw31361step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31361step1 raw31361step0; decide +kernel
      have hl : raw31361step1Labels = raw31361step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31361step0 raw31361step0Labels permutation36 permutation7
    mixedMoment B raw31361step1 raw31361step1Labels = mixedMoment B raw31361step2 raw31361step2Labels := by
      have ha : raw31361step2 = -raw31361step1 := by apply Matrix.ext; change ∀ i j, raw31361step2 i j = -(raw31361step1 i j); unfold raw31361step2 raw31361step1; decide +kernel
      have hl : raw31361step2Labels = raw31361step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31361step2 raw31361step2Labels = mixedMoment B raw31361step3 raw31361step3Labels := by
      have ha : raw31361step3 = raw31361step2 := by apply Matrix.ext; unfold raw31361step3 raw31361step2; decide +kernel
      have hl : raw31361step2Labels = labelEmbedding1 ∘ raw31361step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31361step2 raw31361step2Labels raw31361step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1685 node1685Labels := by rfl

def raw31362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31362Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31362step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw31362step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw31362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31362 raw31362Labels = mixedMoment B node2161 node2161Labels := by
  calc
    mixedMoment B raw31362 raw31362Labels = mixedMoment B raw31362step0 raw31362step0Labels := by
      have hz : ∀ j, raw31362 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31362step0 = (fun i j => raw31362 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31362step0 raw31362; decide +kernel
      have hl : raw31362step0Labels = raw31362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31362 raw31362Labels permutation434 hz
    mixedMoment B raw31362step0 raw31362step0Labels = mixedMoment B raw31362step1 raw31362step1Labels := by
      have ha : raw31362step1 = (fun i j => raw31362step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31362step1 raw31362step0; decide +kernel
      have hl : raw31362step1Labels = raw31362step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31362step0 raw31362step0Labels permutation147 permutation5
    mixedMoment B raw31362step1 raw31362step1Labels = mixedMoment B raw31362step2 raw31362step2Labels := by
      have ha : raw31362step2 = raw31362step1 := by apply Matrix.ext; unfold raw31362step2 raw31362step1; decide +kernel
      have hl : raw31362step1Labels = labelEmbedding1 ∘ raw31362step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31362step1 raw31362step1Labels raw31362step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2161 node2161Labels := by rfl

def raw31363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31363Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31363step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw31363step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw31363step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31363 raw31363Labels = mixedMoment B node2162 node2162Labels := by
  calc
    mixedMoment B raw31363 raw31363Labels = mixedMoment B raw31363step0 raw31363step0Labels := by
      have hz : ∀ j, raw31363 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31363step0 = (fun i j => raw31363 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31363step0 raw31363; decide +kernel
      have hl : raw31363step0Labels = raw31363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31363 raw31363Labels permutation434 hz
    mixedMoment B raw31363step0 raw31363step0Labels = mixedMoment B raw31363step1 raw31363step1Labels := by
      have ha : raw31363step1 = (fun i j => raw31363step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31363step1 raw31363step0; decide +kernel
      have hl : raw31363step1Labels = raw31363step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31363step0 raw31363step0Labels permutation146 permutation5
    mixedMoment B raw31363step1 raw31363step1Labels = mixedMoment B raw31363step2 raw31363step2Labels := by
      have ha : raw31363step2 = raw31363step1 := by apply Matrix.ext; unfold raw31363step2 raw31363step1; decide +kernel
      have hl : raw31363step1Labels = labelEmbedding1 ∘ raw31363step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31363step1 raw31363step1Labels raw31363step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2162 node2162Labels := by rfl

def raw31364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31364Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw31364step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31364step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw31364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31364 raw31364Labels = mixedMoment B node2160 node2160Labels := by
  calc
    mixedMoment B raw31364 raw31364Labels = mixedMoment B raw31364step0 raw31364step0Labels := by
      have ha : raw31364step0 = (fun i j => raw31364 (permutation667 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31364step0 raw31364; decide +kernel
      have hl : raw31364step0Labels = raw31364Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31364 raw31364Labels permutation667 permutation5
    mixedMoment B raw31364step0 raw31364step0Labels = mixedMoment B raw31364step1 raw31364step1Labels := by
      have ha : raw31364step1 = raw31364step0 := by apply Matrix.ext; unfold raw31364step1 raw31364step0; decide +kernel
      have hl : raw31364step0Labels = labelEmbedding1 ∘ raw31364step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31364step0 raw31364step0Labels raw31364step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2160 node2160Labels := by rfl

def raw31365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw31365Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31365step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw31365step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw31365step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31365step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw31365step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31365 raw31365Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw31365 raw31365Labels = mixedMoment B raw31365step0 raw31365step0Labels := by
      have hz : ∀ j, raw31365 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31365step0 = (fun i j => raw31365 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31365step0 raw31365; decide +kernel
      have hl : raw31365step0Labels = raw31365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31365 raw31365Labels permutation434 hz
    mixedMoment B raw31365step0 raw31365step0Labels = mixedMoment B raw31365step1 raw31365step1Labels := by
      have ha : raw31365step1 = (fun i j => raw31365step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31365step1 raw31365step0; decide +kernel
      have hl : raw31365step1Labels = raw31365step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31365step0 raw31365step0Labels permutation36 permutation7
    mixedMoment B raw31365step1 raw31365step1Labels = mixedMoment B raw31365step2 raw31365step2Labels := by
      have ha : raw31365step2 = -raw31365step1 := by apply Matrix.ext; change ∀ i j, raw31365step2 i j = -(raw31365step1 i j); unfold raw31365step2 raw31365step1; decide +kernel
      have hl : raw31365step2Labels = raw31365step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31365step2 raw31365step2Labels = mixedMoment B raw31365step3 raw31365step3Labels := by
      have ha : raw31365step3 = raw31365step2 := by apply Matrix.ext; unfold raw31365step3 raw31365step2; decide +kernel
      have hl : raw31365step2Labels = labelEmbedding1 ∘ raw31365step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31365step2 raw31365step2Labels raw31365step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw31366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31366 raw31366Labels = mixedMoment B node3379 node3379Labels := by
  calc
    mixedMoment B raw31366 raw31366Labels = mixedMoment B raw31366step0 raw31366step0Labels := by
      have hz : ∀ j, raw31366 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31366step0 = (fun i j => raw31366 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31366step0 raw31366; decide +kernel
      have hl : raw31366step0Labels = raw31366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31366 raw31366Labels permutation434 hz
    mixedMoment B raw31366step0 raw31366step0Labels = mixedMoment B raw31366step1 raw31366step1Labels := by
      have ha : raw31366step1 = (fun i j => raw31366step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31366step1 raw31366step0; decide +kernel
      have hl : raw31366step1Labels = raw31366step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31366step0 raw31366step0Labels permutation33 permutation2
    _ = mixedMoment B node3379 node3379Labels := by rfl

def raw31367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31367 raw31367Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw31367 raw31367Labels = mixedMoment B raw31367step0 raw31367step0Labels := by
      have hz : ∀ j, raw31367 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31367step0 = (fun i j => raw31367 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31367step0 raw31367; decide +kernel
      have hl : raw31367step0Labels = raw31367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31367 raw31367Labels permutation434 hz
    mixedMoment B raw31367step0 raw31367step0Labels = mixedMoment B raw31367step1 raw31367step1Labels := by
      have ha : raw31367step1 = (fun i j => raw31367step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31367step1 raw31367step0; decide +kernel
      have hl : raw31367step1Labels = raw31367step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31367step0 raw31367step0Labels permutation33 permutation2
    _ = mixedMoment B node2028 node2028Labels := by rfl

def raw31368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31368 raw31368Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw31368 raw31368Labels = mixedMoment B raw31368step0 raw31368step0Labels := by
      have hz : ∀ j, raw31368 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31368step0 = (fun i j => raw31368 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31368step0 raw31368; decide +kernel
      have hl : raw31368step0Labels = raw31368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31368 raw31368Labels permutation434 hz
    mixedMoment B raw31368step0 raw31368step0Labels = mixedMoment B raw31368step1 raw31368step1Labels := by
      have ha : raw31368step1 = (fun i j => raw31368step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31368step1 raw31368step0; decide +kernel
      have hl : raw31368step1Labels = raw31368step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31368step0 raw31368step0Labels permutation33 permutation2
    _ = mixedMoment B node1814 node1814Labels := by rfl

def raw31369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31369 raw31369Labels = mixedMoment B node1791 node1791Labels := by
  calc
    mixedMoment B raw31369 raw31369Labels = mixedMoment B raw31369step0 raw31369step0Labels := by
      have ha : raw31369step0 = (fun i j => raw31369 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31369step0 raw31369; decide +kernel
      have hl : raw31369step0Labels = raw31369Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31369 raw31369Labels permutation153 permutation2
    _ = mixedMoment B node1791 node1791Labels := by rfl

def raw31370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw31370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31370 raw31370Labels = mixedMoment B node1795 node1795Labels := by
  calc
    mixedMoment B raw31370 raw31370Labels = mixedMoment B raw31370step0 raw31370step0Labels := by
      have hz : ∀ j, raw31370 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31370step0 = (fun i j => raw31370 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31370step0 raw31370; decide +kernel
      have hl : raw31370step0Labels = raw31370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31370 raw31370Labels permutation434 hz
    mixedMoment B raw31370step0 raw31370step0Labels = mixedMoment B raw31370step1 raw31370step1Labels := by
      have ha : raw31370step1 = (fun i j => raw31370step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31370step1 raw31370step0; decide +kernel
      have hl : raw31370step1Labels = raw31370step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31370step0 raw31370step0Labels permutation33 permutation2
    _ = mixedMoment B node1795 node1795Labels := by rfl

def raw31371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31371 raw31371Labels = mixedMoment B node1797 node1797Labels := by
  calc
    mixedMoment B raw31371 raw31371Labels = mixedMoment B raw31371step0 raw31371step0Labels := by
      have hz : ∀ j, raw31371 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31371step0 = (fun i j => raw31371 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31371step0 raw31371; decide +kernel
      have hl : raw31371step0Labels = raw31371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31371 raw31371Labels permutation434 hz
    _ = mixedMoment B node1797 node1797Labels := by rfl

def raw31372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31372 raw31372Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw31372 raw31372Labels = mixedMoment B raw31372step0 raw31372step0Labels := by
      have hz : ∀ j, raw31372 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31372step0 = (fun i j => raw31372 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31372step0 raw31372; decide +kernel
      have hl : raw31372step0Labels = raw31372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31372 raw31372Labels permutation434 hz
    mixedMoment B raw31372step0 raw31372step0Labels = mixedMoment B raw31372step1 raw31372step1Labels := by
      have ha : raw31372step1 = (fun i j => raw31372step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31372step1 raw31372step0; decide +kernel
      have hl : raw31372step1Labels = raw31372step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31372step0 raw31372step0Labels permutation33 permutation2
    _ = mixedMoment B node932 node932Labels := by rfl

def raw31373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31373 raw31373Labels = mixedMoment B node1966 node1966Labels := by
  calc
    mixedMoment B raw31373 raw31373Labels = mixedMoment B raw31373step0 raw31373step0Labels := by
      have ha : raw31373step0 = (fun i j => raw31373 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31373step0 raw31373; decide +kernel
      have hl : raw31373step0Labels = raw31373Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31373 raw31373Labels permutation159 permutation2
    _ = mixedMoment B node1966 node1966Labels := by rfl

def raw31374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31374 raw31374Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw31374 raw31374Labels = mixedMoment B raw31374step0 raw31374step0Labels := by
      have hz : ∀ j, raw31374 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31374step0 = (fun i j => raw31374 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31374step0 raw31374; decide +kernel
      have hl : raw31374step0Labels = raw31374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31374 raw31374Labels permutation434 hz
    _ = mixedMoment B node2058 node2058Labels := by rfl

def raw31375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31375step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31375 raw31375Labels = mixedMoment B node2053 node2053Labels := by
  calc
    mixedMoment B raw31375 raw31375Labels = mixedMoment B raw31375step0 raw31375step0Labels := by
      have hz : ∀ j, raw31375 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31375step0 = (fun i j => raw31375 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31375step0 raw31375; decide +kernel
      have hl : raw31375step0Labels = raw31375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31375 raw31375Labels permutation434 hz
    mixedMoment B raw31375step0 raw31375step0Labels = mixedMoment B raw31375step1 raw31375step1Labels := by
      have ha : raw31375step1 = (fun i j => raw31375step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31375step1 raw31375step0; decide +kernel
      have hl : raw31375step1Labels = raw31375step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31375step0 raw31375step0Labels permutation36 permutation2
    _ = mixedMoment B node2053 node2053Labels := by rfl

def raw31376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31376Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31376step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31376 raw31376Labels = mixedMoment B node906 node906Labels := by
  calc
    mixedMoment B raw31376 raw31376Labels = mixedMoment B raw31376step0 raw31376step0Labels := by
      have ha : raw31376step0 = (fun i j => raw31376 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31376step0 raw31376; decide +kernel
      have hl : raw31376step0Labels = raw31376Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31376 raw31376Labels permutation153 permutation2
    _ = mixedMoment B node906 node906Labels := by rfl

def raw31377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31377 raw31377Labels = mixedMoment B node1974 node1974Labels := by
  calc
    mixedMoment B raw31377 raw31377Labels = mixedMoment B raw31377step0 raw31377step0Labels := by
      have ha : raw31377step0 = (fun i j => raw31377 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31377step0 raw31377; decide +kernel
      have hl : raw31377step0Labels = raw31377Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31377 raw31377Labels permutation153 permutation2
    _ = mixedMoment B node1974 node1974Labels := by rfl

def raw31378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31378 raw31378Labels = mixedMoment B node2021 node2021Labels := by
  calc
    _ = mixedMoment B node2021 node2021Labels := by rfl

def raw31379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31379Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31379step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31379 raw31379Labels = mixedMoment B node2019 node2019Labels := by
  calc
    mixedMoment B raw31379 raw31379Labels = mixedMoment B raw31379step0 raw31379step0Labels := by
      have ha : raw31379step0 = (fun i j => raw31379 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31379step0 raw31379; decide +kernel
      have hl : raw31379step0Labels = raw31379Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31379 raw31379Labels permutation153 permutation2
    _ = mixedMoment B node2019 node2019Labels := by rfl

def raw31380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31380step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31380step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31380step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31380 raw31380Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw31380 raw31380Labels = mixedMoment B raw31380step0 raw31380step0Labels := by
      have hz : ∀ j, raw31380 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31380step0 = (fun i j => raw31380 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31380step0 raw31380; decide +kernel
      have hl : raw31380step0Labels = raw31380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31380 raw31380Labels permutation434 hz
    mixedMoment B raw31380step0 raw31380step0Labels = mixedMoment B raw31380step1 raw31380step1Labels := by
      have ha : raw31380step1 = (fun i j => raw31380step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31380step1 raw31380step0; decide +kernel
      have hl : raw31380step1Labels = raw31380step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31380step0 raw31380step0Labels permutation33 permutation3
    mixedMoment B raw31380step1 raw31380step1Labels = mixedMoment B raw31380step2 raw31380step2Labels := by
      have ha : raw31380step2 = raw31380step1 := by apply Matrix.ext; unfold raw31380step2 raw31380step1; decide +kernel
      have hl : raw31380step1Labels = labelEmbedding6 ∘ raw31380step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31380step1 raw31380step1Labels raw31380step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw31381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw31381step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31381step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31381step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31381step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31381step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31381 raw31381Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw31381 raw31381Labels = mixedMoment B raw31381step0 raw31381step0Labels := by
      have hz : ∀ j, raw31381 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31381step0 = (fun i j => raw31381 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31381step0 raw31381; decide +kernel
      have hl : raw31381step0Labels = raw31381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31381 raw31381Labels permutation434 hz
    mixedMoment B raw31381step0 raw31381step0Labels = mixedMoment B raw31381step1 raw31381step1Labels := by
      have ha : raw31381step1 = (fun i j => raw31381step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31381step1 raw31381step0; decide +kernel
      have hl : raw31381step1Labels = raw31381step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31381step0 raw31381step0Labels permutation125 permutation3
    mixedMoment B raw31381step1 raw31381step1Labels = mixedMoment B raw31381step2 raw31381step2Labels := by
      have ha : raw31381step2 = -raw31381step1 := by apply Matrix.ext; change ∀ i j, raw31381step2 i j = -(raw31381step1 i j); unfold raw31381step2 raw31381step1; decide +kernel
      have hl : raw31381step2Labels = raw31381step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31381step2 raw31381step2Labels = mixedMoment B raw31381step3 raw31381step3Labels := by
      have ha : raw31381step3 = raw31381step2 := by apply Matrix.ext; unfold raw31381step3 raw31381step2; decide +kernel
      have hl : raw31381step2Labels = labelEmbedding6 ∘ raw31381step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31381step2 raw31381step2Labels raw31381step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw31382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw31382step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31382step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31382step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31382step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31382 raw31382Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw31382 raw31382Labels = mixedMoment B raw31382step0 raw31382step0Labels := by
      have ha : raw31382step0 = (fun i j => raw31382 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31382step0 raw31382; decide +kernel
      have hl : raw31382step0Labels = raw31382Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31382 raw31382Labels permutation582 permutation3
    mixedMoment B raw31382step0 raw31382step0Labels = mixedMoment B raw31382step1 raw31382step1Labels := by
      have ha : raw31382step1 = -raw31382step0 := by apply Matrix.ext; change ∀ i j, raw31382step1 i j = -(raw31382step0 i j); unfold raw31382step1 raw31382step0; decide +kernel
      have hl : raw31382step1Labels = raw31382step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31382step1 raw31382step1Labels = mixedMoment B raw31382step2 raw31382step2Labels := by
      have ha : raw31382step2 = raw31382step1 := by apply Matrix.ext; unfold raw31382step2 raw31382step1; decide +kernel
      have hl : raw31382step1Labels = labelEmbedding6 ∘ raw31382step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31382step1 raw31382step1Labels raw31382step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw31383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw31383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31383step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31383step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31383step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31383 raw31383Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw31383 raw31383Labels = mixedMoment B raw31383step0 raw31383step0Labels := by
      have hz : ∀ j, raw31383 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31383step0 = (fun i j => raw31383 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31383step0 raw31383; decide +kernel
      have hl : raw31383step0Labels = raw31383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31383 raw31383Labels permutation434 hz
    mixedMoment B raw31383step0 raw31383step0Labels = mixedMoment B raw31383step1 raw31383step1Labels := by
      have ha : raw31383step1 = (fun i j => raw31383step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31383step1 raw31383step0; decide +kernel
      have hl : raw31383step1Labels = raw31383step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31383step0 raw31383step0Labels permutation33 permutation3
    mixedMoment B raw31383step1 raw31383step1Labels = mixedMoment B raw31383step2 raw31383step2Labels := by
      have ha : raw31383step2 = raw31383step1 := by apply Matrix.ext; unfold raw31383step2 raw31383step1; decide +kernel
      have hl : raw31383step1Labels = labelEmbedding6 ∘ raw31383step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31383step1 raw31383step1Labels raw31383step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw31384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw31384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31384step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31384step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31384step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31384 raw31384Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw31384 raw31384Labels = mixedMoment B raw31384step0 raw31384step0Labels := by
      have hz : ∀ j, raw31384 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31384step0 = (fun i j => raw31384 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31384step0 raw31384; decide +kernel
      have hl : raw31384step0Labels = raw31384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31384 raw31384Labels permutation434 hz
    mixedMoment B raw31384step0 raw31384step0Labels = mixedMoment B raw31384step1 raw31384step1Labels := by
      have ha : raw31384step1 = (fun i j => raw31384step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31384step1 raw31384step0; decide +kernel
      have hl : raw31384step1Labels = raw31384step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31384step0 raw31384step0Labels permutation32 permutation3
    mixedMoment B raw31384step1 raw31384step1Labels = mixedMoment B raw31384step2 raw31384step2Labels := by
      have ha : raw31384step2 = raw31384step1 := by apply Matrix.ext; unfold raw31384step2 raw31384step1; decide +kernel
      have hl : raw31384step1Labels = labelEmbedding6 ∘ raw31384step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31384step1 raw31384step1Labels raw31384step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw31385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31385step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31385step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31385 raw31385Labels = mixedMoment B node4223 node4223Labels := by
  calc
    mixedMoment B raw31385 raw31385Labels = mixedMoment B raw31385step0 raw31385step0Labels := by
      have hz : ∀ j, raw31385 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31385step0 = (fun i j => raw31385 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31385step0 raw31385; decide +kernel
      have hl : raw31385step0Labels = raw31385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31385 raw31385Labels permutation434 hz
    mixedMoment B raw31385step0 raw31385step0Labels = mixedMoment B raw31385step1 raw31385step1Labels := by
      have ha : raw31385step1 = (fun i j => raw31385step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31385step1 raw31385step0; decide +kernel
      have hl : raw31385step1Labels = raw31385step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31385step0 raw31385step0Labels permutation33 permutation3
    mixedMoment B raw31385step1 raw31385step1Labels = mixedMoment B raw31385step2 raw31385step2Labels := by
      have ha : raw31385step2 = raw31385step1 := by apply Matrix.ext; unfold raw31385step2 raw31385step1; decide +kernel
      have hl : raw31385step1Labels = labelEmbedding6 ∘ raw31385step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31385step1 raw31385step1Labels raw31385step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4223 node4223Labels := by rfl

def raw31386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31386step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31386step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31386 raw31386Labels = mixedMoment B node4653 node4653Labels := by
  calc
    mixedMoment B raw31386 raw31386Labels = mixedMoment B raw31386step0 raw31386step0Labels := by
      have hz : ∀ j, raw31386 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31386step0 = (fun i j => raw31386 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31386step0 raw31386; decide +kernel
      have hl : raw31386step0Labels = raw31386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31386 raw31386Labels permutation434 hz
    mixedMoment B raw31386step0 raw31386step0Labels = mixedMoment B raw31386step1 raw31386step1Labels := by
      have ha : raw31386step1 = (fun i j => raw31386step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31386step1 raw31386step0; decide +kernel
      have hl : raw31386step1Labels = raw31386step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31386step0 raw31386step0Labels permutation33 permutation3
    mixedMoment B raw31386step1 raw31386step1Labels = mixedMoment B raw31386step2 raw31386step2Labels := by
      have ha : raw31386step2 = raw31386step1 := by apply Matrix.ext; unfold raw31386step2 raw31386step1; decide +kernel
      have hl : raw31386step1Labels = labelEmbedding6 ∘ raw31386step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31386step1 raw31386step1Labels raw31386step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4653 node4653Labels := by rfl

def raw31387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31387step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31387 raw31387Labels = mixedMoment B node4716 node4716Labels := by
  calc
    mixedMoment B raw31387 raw31387Labels = mixedMoment B raw31387step0 raw31387step0Labels := by
      have ha : raw31387step0 = (fun i j => raw31387 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31387step0 raw31387; decide +kernel
      have hl : raw31387step0Labels = raw31387Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31387 raw31387Labels permutation201 permutation3
    mixedMoment B raw31387step0 raw31387step0Labels = mixedMoment B raw31387step1 raw31387step1Labels := by
      have ha : raw31387step1 = raw31387step0 := by apply Matrix.ext; unfold raw31387step1 raw31387step0; decide +kernel
      have hl : raw31387step0Labels = labelEmbedding6 ∘ raw31387step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31387step0 raw31387step0Labels raw31387step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4716 node4716Labels := by rfl

def raw31388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw31388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31388step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31388step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31388 raw31388Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw31388 raw31388Labels = mixedMoment B raw31388step0 raw31388step0Labels := by
      have hz : ∀ j, raw31388 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31388step0 = (fun i j => raw31388 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31388step0 raw31388; decide +kernel
      have hl : raw31388step0Labels = raw31388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31388 raw31388Labels permutation434 hz
    mixedMoment B raw31388step0 raw31388step0Labels = mixedMoment B raw31388step1 raw31388step1Labels := by
      have ha : raw31388step1 = (fun i j => raw31388step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31388step1 raw31388step0; decide +kernel
      have hl : raw31388step1Labels = raw31388step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31388step0 raw31388step0Labels permutation36 permutation3
    mixedMoment B raw31388step1 raw31388step1Labels = mixedMoment B raw31388step2 raw31388step2Labels := by
      have ha : raw31388step2 = raw31388step1 := by apply Matrix.ext; unfold raw31388step2 raw31388step1; decide +kernel
      have hl : raw31388step1Labels = labelEmbedding6 ∘ raw31388step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31388step1 raw31388step1Labels raw31388step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

def raw31389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31389step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31389 raw31389Labels = mixedMoment B node4200 node4200Labels := by
  calc
    mixedMoment B raw31389 raw31389Labels = mixedMoment B raw31389step0 raw31389step0Labels := by
      have ha : raw31389step0 = (fun i j => raw31389 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31389step0 raw31389; decide +kernel
      have hl : raw31389step0Labels = raw31389Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31389 raw31389Labels permutation153 permutation3
    mixedMoment B raw31389step0 raw31389step0Labels = mixedMoment B raw31389step1 raw31389step1Labels := by
      have ha : raw31389step1 = raw31389step0 := by apply Matrix.ext; unfold raw31389step1 raw31389step0; decide +kernel
      have hl : raw31389step0Labels = labelEmbedding6 ∘ raw31389step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31389step0 raw31389step0Labels raw31389step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4200 node4200Labels := by rfl

def raw31390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31390step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31390step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31390 raw31390Labels = mixedMoment B node4634 node4634Labels := by
  calc
    mixedMoment B raw31390 raw31390Labels = mixedMoment B raw31390step0 raw31390step0Labels := by
      have ha : raw31390step0 = (fun i j => raw31390 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31390step0 raw31390; decide +kernel
      have hl : raw31390step0Labels = raw31390Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31390 raw31390Labels permutation153 permutation3
    mixedMoment B raw31390step0 raw31390step0Labels = mixedMoment B raw31390step1 raw31390step1Labels := by
      have ha : raw31390step1 = raw31390step0 := by apply Matrix.ext; unfold raw31390step1 raw31390step0; decide +kernel
      have hl : raw31390step0Labels = labelEmbedding6 ∘ raw31390step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31390step0 raw31390step0Labels raw31390step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4634 node4634Labels := by rfl

def raw31391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31391step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31391step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31391step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31391 raw31391Labels = mixedMoment B node4766 node4766Labels := by
  calc
    mixedMoment B raw31391 raw31391Labels = mixedMoment B raw31391step0 raw31391step0Labels := by
      have ha : raw31391step0 = (fun i j => raw31391 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31391step0 raw31391; decide +kernel
      have hl : raw31391step0Labels = raw31391Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31391 raw31391Labels permutation153 permutation3
    mixedMoment B raw31391step0 raw31391step0Labels = mixedMoment B raw31391step1 raw31391step1Labels := by
      have ha : raw31391step1 = raw31391step0 := by apply Matrix.ext; unfold raw31391step1 raw31391step0; decide +kernel
      have hl : raw31391step0Labels = labelEmbedding6 ∘ raw31391step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31391step0 raw31391step0Labels raw31391step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4766 node4766Labels := by rfl

def raw31392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31392step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31392step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31392step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31392 raw31392Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw31392 raw31392Labels = mixedMoment B raw31392step0 raw31392step0Labels := by
      have ha : raw31392step0 = (fun i j => raw31392 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31392step0 raw31392; decide +kernel
      have hl : raw31392step0Labels = raw31392Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31392 raw31392Labels permutation156 permutation3
    mixedMoment B raw31392step0 raw31392step0Labels = mixedMoment B raw31392step1 raw31392step1Labels := by
      have ha : raw31392step1 = raw31392step0 := by apply Matrix.ext; unfold raw31392step1 raw31392step0; decide +kernel
      have hl : raw31392step0Labels = labelEmbedding6 ∘ raw31392step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31392step0 raw31392step0Labels raw31392step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

def raw31393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -3, 0], ![2, 0, -2]]
def raw31393step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw31393step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31393step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw31393step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31393 raw31393Labels = mixedMoment B node4203 node4203Labels := by
  calc
    mixedMoment B raw31393 raw31393Labels = mixedMoment B raw31393step0 raw31393step0Labels := by
      have hz : ∀ j, raw31393 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31393step0 = (fun i j => raw31393 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31393step0 raw31393; decide +kernel
      have hl : raw31393step0Labels = raw31393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31393 raw31393Labels permutation434 hz
    mixedMoment B raw31393step0 raw31393step0Labels = mixedMoment B raw31393step1 raw31393step1Labels := by
      have ha : raw31393step1 = (fun i j => raw31393step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31393step1 raw31393step0; decide +kernel
      have hl : raw31393step1Labels = raw31393step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31393step0 raw31393step0Labels permutation33 permutation3
    mixedMoment B raw31393step1 raw31393step1Labels = mixedMoment B raw31393step2 raw31393step2Labels := by
      have ha : raw31393step2 = raw31393step1 := by apply Matrix.ext; unfold raw31393step2 raw31393step1; decide +kernel
      have hl : raw31393step1Labels = labelEmbedding6 ∘ raw31393step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31393step1 raw31393step1Labels raw31393step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4203 node4203Labels := by rfl

def raw31394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![3, -3, 0], ![2, 0, -2]]
def raw31394step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw31394step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31394step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw31394step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31394 raw31394Labels = mixedMoment B node4636 node4636Labels := by
  calc
    mixedMoment B raw31394 raw31394Labels = mixedMoment B raw31394step0 raw31394step0Labels := by
      have hz : ∀ j, raw31394 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31394step0 = (fun i j => raw31394 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31394step0 raw31394; decide +kernel
      have hl : raw31394step0Labels = raw31394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31394 raw31394Labels permutation434 hz
    mixedMoment B raw31394step0 raw31394step0Labels = mixedMoment B raw31394step1 raw31394step1Labels := by
      have ha : raw31394step1 = (fun i j => raw31394step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31394step1 raw31394step0; decide +kernel
      have hl : raw31394step1Labels = raw31394step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31394step0 raw31394step0Labels permutation33 permutation3
    mixedMoment B raw31394step1 raw31394step1Labels = mixedMoment B raw31394step2 raw31394step2Labels := by
      have ha : raw31394step2 = raw31394step1 := by apply Matrix.ext; unfold raw31394step2 raw31394step1; decide +kernel
      have hl : raw31394step1Labels = labelEmbedding6 ∘ raw31394step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31394step1 raw31394step1Labels raw31394step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4636 node4636Labels := by rfl

def raw31395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![3, -3, 0], ![2, 0, -2]]
def raw31395step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw31395step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw31395step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31395step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw31395step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31395 raw31395Labels = mixedMoment B node4678 node4678Labels := by
  calc
    mixedMoment B raw31395 raw31395Labels = mixedMoment B raw31395step0 raw31395step0Labels := by
      have hz : ∀ j, raw31395 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31395step0 = (fun i j => raw31395 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31395step0 raw31395; decide +kernel
      have hl : raw31395step0Labels = raw31395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31395 raw31395Labels permutation434 hz
    mixedMoment B raw31395step0 raw31395step0Labels = mixedMoment B raw31395step1 raw31395step1Labels := by
      have ha : raw31395step1 = (fun i j => raw31395step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31395step1 raw31395step0; decide +kernel
      have hl : raw31395step1Labels = raw31395step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31395step0 raw31395step0Labels permutation125 permutation3
    mixedMoment B raw31395step1 raw31395step1Labels = mixedMoment B raw31395step2 raw31395step2Labels := by
      have ha : raw31395step2 = -raw31395step1 := by apply Matrix.ext; change ∀ i j, raw31395step2 i j = -(raw31395step1 i j); unfold raw31395step2 raw31395step1; decide +kernel
      have hl : raw31395step2Labels = raw31395step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31395step2 raw31395step2Labels = mixedMoment B raw31395step3 raw31395step3Labels := by
      have ha : raw31395step3 = raw31395step2 := by apply Matrix.ext; unfold raw31395step3 raw31395step2; decide +kernel
      have hl : raw31395step2Labels = labelEmbedding6 ∘ raw31395step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31395step2 raw31395step2Labels raw31395step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4678 node4678Labels := by rfl

def raw31396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw31396step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw31396step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31396step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw31396step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31396 raw31396Labels = mixedMoment B node4658 node4658Labels := by
  calc
    mixedMoment B raw31396 raw31396Labels = mixedMoment B raw31396step0 raw31396step0Labels := by
      have ha : raw31396step0 = (fun i j => raw31396 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31396step0 raw31396; decide +kernel
      have hl : raw31396step0Labels = raw31396Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31396 raw31396Labels permutation582 permutation3
    mixedMoment B raw31396step0 raw31396step0Labels = mixedMoment B raw31396step1 raw31396step1Labels := by
      have ha : raw31396step1 = -raw31396step0 := by apply Matrix.ext; change ∀ i j, raw31396step1 i j = -(raw31396step0 i j); unfold raw31396step1 raw31396step0; decide +kernel
      have hl : raw31396step1Labels = raw31396step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31396step1 raw31396step1Labels = mixedMoment B raw31396step2 raw31396step2Labels := by
      have ha : raw31396step2 = raw31396step1 := by apply Matrix.ext; unfold raw31396step2 raw31396step1; decide +kernel
      have hl : raw31396step1Labels = labelEmbedding6 ∘ raw31396step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31396step1 raw31396step1Labels raw31396step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4658 node4658Labels := by rfl

def raw31397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw31397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -3, 0], ![1, 1, -2]]
def raw31397step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw31397step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31397step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw31397step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31397 raw31397Labels = mixedMoment B node4800 node4800Labels := by
  calc
    mixedMoment B raw31397 raw31397Labels = mixedMoment B raw31397step0 raw31397step0Labels := by
      have hz : ∀ j, raw31397 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31397step0 = (fun i j => raw31397 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31397step0 raw31397; decide +kernel
      have hl : raw31397step0Labels = raw31397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31397 raw31397Labels permutation434 hz
    mixedMoment B raw31397step0 raw31397step0Labels = mixedMoment B raw31397step1 raw31397step1Labels := by
      have ha : raw31397step1 = (fun i j => raw31397step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31397step1 raw31397step0; decide +kernel
      have hl : raw31397step1Labels = raw31397step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31397step0 raw31397step0Labels permutation33 permutation3
    mixedMoment B raw31397step1 raw31397step1Labels = mixedMoment B raw31397step2 raw31397step2Labels := by
      have ha : raw31397step2 = raw31397step1 := by apply Matrix.ext; unfold raw31397step2 raw31397step1; decide +kernel
      have hl : raw31397step1Labels = labelEmbedding6 ∘ raw31397step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31397step1 raw31397step1Labels raw31397step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4800 node4800Labels := by rfl

def raw31398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, -1, -2]]
def raw31398step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31398step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31398step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31398step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31398 raw31398Labels = mixedMoment B node4205 node4205Labels := by
  calc
    mixedMoment B raw31398 raw31398Labels = mixedMoment B raw31398step0 raw31398step0Labels := by
      have hz : ∀ j, raw31398 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31398step0 = (fun i j => raw31398 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31398step0 raw31398; decide +kernel
      have hl : raw31398step0Labels = raw31398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31398 raw31398Labels permutation434 hz
    mixedMoment B raw31398step0 raw31398step0Labels = mixedMoment B raw31398step1 raw31398step1Labels := by
      have ha : raw31398step1 = (fun i j => raw31398step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31398step1 raw31398step0; decide +kernel
      have hl : raw31398step1Labels = raw31398step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31398step0 raw31398step0Labels permutation32 permutation3
    mixedMoment B raw31398step1 raw31398step1Labels = mixedMoment B raw31398step2 raw31398step2Labels := by
      have ha : raw31398step2 = raw31398step1 := by apply Matrix.ext; unfold raw31398step2 raw31398step1; decide +kernel
      have hl : raw31398step1Labels = labelEmbedding6 ∘ raw31398step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31398step1 raw31398step1Labels raw31398step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4205 node4205Labels := by rfl

def raw31399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![3, -1, -2]]
def raw31399step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31399step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31399step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31399step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31399 raw31399Labels = mixedMoment B node4638 node4638Labels := by
  calc
    mixedMoment B raw31399 raw31399Labels = mixedMoment B raw31399step0 raw31399step0Labels := by
      have hz : ∀ j, raw31399 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31399step0 = (fun i j => raw31399 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31399step0 raw31399; decide +kernel
      have hl : raw31399step0Labels = raw31399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31399 raw31399Labels permutation434 hz
    mixedMoment B raw31399step0 raw31399step0Labels = mixedMoment B raw31399step1 raw31399step1Labels := by
      have ha : raw31399step1 = (fun i j => raw31399step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31399step1 raw31399step0; decide +kernel
      have hl : raw31399step1Labels = raw31399step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31399step0 raw31399step0Labels permutation32 permutation3
    mixedMoment B raw31399step1 raw31399step1Labels = mixedMoment B raw31399step2 raw31399step2Labels := by
      have ha : raw31399step2 = raw31399step1 := by apply Matrix.ext; unfold raw31399step2 raw31399step1; decide +kernel
      have hl : raw31399step1Labels = labelEmbedding6 ∘ raw31399step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31399step1 raw31399step1Labels raw31399step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4638 node4638Labels := by rfl

def raw31400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![3, -1, -2]]
def raw31400step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31400step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31400step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31400 raw31400Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw31400 raw31400Labels = mixedMoment B raw31400step0 raw31400step0Labels := by
      have hz : ∀ j, raw31400 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31400step0 = (fun i j => raw31400 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31400step0 raw31400; decide +kernel
      have hl : raw31400step0Labels = raw31400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31400 raw31400Labels permutation434 hz
    mixedMoment B raw31400step0 raw31400step0Labels = mixedMoment B raw31400step1 raw31400step1Labels := by
      have ha : raw31400step1 = (fun i j => raw31400step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31400step1 raw31400step0; decide +kernel
      have hl : raw31400step1Labels = raw31400step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31400step0 raw31400step0Labels permutation32 permutation3
    mixedMoment B raw31400step1 raw31400step1Labels = mixedMoment B raw31400step2 raw31400step2Labels := by
      have ha : raw31400step2 = raw31400step1 := by apply Matrix.ext; unfold raw31400step2 raw31400step1; decide +kernel
      have hl : raw31400step1Labels = labelEmbedding6 ∘ raw31400step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31400step1 raw31400step1Labels raw31400step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4770 node4770Labels := by rfl

def raw31401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31401step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31401step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31401step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31401 raw31401Labels = mixedMoment B node4707 node4707Labels := by
  calc
    mixedMoment B raw31401 raw31401Labels = mixedMoment B raw31401step0 raw31401step0Labels := by
      have ha : raw31401step0 = (fun i j => raw31401 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31401step0 raw31401; decide +kernel
      have hl : raw31401step0Labels = raw31401Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31401 raw31401Labels permutation200 permutation3
    mixedMoment B raw31401step0 raw31401step0Labels = mixedMoment B raw31401step1 raw31401step1Labels := by
      have ha : raw31401step1 = raw31401step0 := by apply Matrix.ext; unfold raw31401step1 raw31401step0; decide +kernel
      have hl : raw31401step0Labels = labelEmbedding6 ∘ raw31401step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31401step0 raw31401step0Labels raw31401step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4707 node4707Labels := by rfl

def raw31402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31402step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31402 raw31402Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw31402 raw31402Labels = mixedMoment B raw31402step0 raw31402step0Labels := by
      have hz : ∀ j, raw31402 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31402step0 = (fun i j => raw31402 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31402step0 raw31402; decide +kernel
      have hl : raw31402step0Labels = raw31402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31402 raw31402Labels permutation434 hz
    mixedMoment B raw31402step0 raw31402step0Labels = mixedMoment B raw31402step1 raw31402step1Labels := by
      have ha : raw31402step1 = (fun i j => raw31402step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31402step1 raw31402step0; decide +kernel
      have hl : raw31402step1Labels = raw31402step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31402step0 raw31402step0Labels permutation33 permutation3
    _ = mixedMoment B node3693 node3693Labels := by rfl

def raw31403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31403Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31403step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw31403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31403step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31403step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31403 raw31403Labels = mixedMoment B node3736 node3736Labels := by
  calc
    mixedMoment B raw31403 raw31403Labels = mixedMoment B raw31403step0 raw31403step0Labels := by
      have hz : ∀ j, raw31403 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31403step0 = (fun i j => raw31403 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31403step0 raw31403; decide +kernel
      have hl : raw31403step0Labels = raw31403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31403 raw31403Labels permutation434 hz
    mixedMoment B raw31403step0 raw31403step0Labels = mixedMoment B raw31403step1 raw31403step1Labels := by
      have ha : raw31403step1 = (fun i j => raw31403step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31403step1 raw31403step0; decide +kernel
      have hl : raw31403step1Labels = raw31403step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31403step0 raw31403step0Labels permutation125 permutation3
    mixedMoment B raw31403step1 raw31403step1Labels = mixedMoment B raw31403step2 raw31403step2Labels := by
      have ha : raw31403step2 = -raw31403step1 := by apply Matrix.ext; change ∀ i j, raw31403step2 i j = -(raw31403step1 i j); unfold raw31403step2 raw31403step1; decide +kernel
      have hl : raw31403step2Labels = raw31403step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3736 node3736Labels := by rfl

def raw31404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31404Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw31404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31404step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31404step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31404 raw31404Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw31404 raw31404Labels = mixedMoment B raw31404step0 raw31404step0Labels := by
      have ha : raw31404step0 = (fun i j => raw31404 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31404step0 raw31404; decide +kernel
      have hl : raw31404step0Labels = raw31404Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31404 raw31404Labels permutation582 permutation3
    mixedMoment B raw31404step0 raw31404step0Labels = mixedMoment B raw31404step1 raw31404step1Labels := by
      have ha : raw31404step1 = -raw31404step0 := by apply Matrix.ext; change ∀ i j, raw31404step1 i j = -(raw31404step0 i j); unfold raw31404step1 raw31404step0; decide +kernel
      have hl : raw31404step1Labels = raw31404step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3719 node3719Labels := by rfl

def raw31405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw31405step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31405step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31405 raw31405Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw31405 raw31405Labels = mixedMoment B raw31405step0 raw31405step0Labels := by
      have hz : ∀ j, raw31405 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31405step0 = (fun i j => raw31405 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31405step0 raw31405; decide +kernel
      have hl : raw31405step0Labels = raw31405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31405 raw31405Labels permutation434 hz
    mixedMoment B raw31405step0 raw31405step0Labels = mixedMoment B raw31405step1 raw31405step1Labels := by
      have ha : raw31405step1 = (fun i j => raw31405step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31405step1 raw31405step0; decide +kernel
      have hl : raw31405step1Labels = raw31405step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31405step0 raw31405step0Labels permutation33 permutation3
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw31406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw31406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31406 raw31406Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw31406 raw31406Labels = mixedMoment B raw31406step0 raw31406step0Labels := by
      have hz : ∀ j, raw31406 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31406step0 = (fun i j => raw31406 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31406step0 raw31406; decide +kernel
      have hl : raw31406step0Labels = raw31406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31406 raw31406Labels permutation434 hz
    mixedMoment B raw31406step0 raw31406step0Labels = mixedMoment B raw31406step1 raw31406step1Labels := by
      have ha : raw31406step1 = (fun i j => raw31406step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31406step1 raw31406step0; decide +kernel
      have hl : raw31406step1Labels = raw31406step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31406step0 raw31406step0Labels permutation32 permutation3
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw31407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31407step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31407 raw31407Labels = mixedMoment B node724 node724Labels := by
  calc
    mixedMoment B raw31407 raw31407Labels = mixedMoment B raw31407step0 raw31407step0Labels := by
      have hz : ∀ j, raw31407 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31407step0 = (fun i j => raw31407 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31407step0 raw31407; decide +kernel
      have hl : raw31407step0Labels = raw31407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31407 raw31407Labels permutation434 hz
    mixedMoment B raw31407step0 raw31407step0Labels = mixedMoment B raw31407step1 raw31407step1Labels := by
      have ha : raw31407step1 = (fun i j => raw31407step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31407step1 raw31407step0; decide +kernel
      have hl : raw31407step1Labels = raw31407step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31407step0 raw31407step0Labels permutation33 permutation3
    _ = mixedMoment B node724 node724Labels := by rfl

def raw31408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31408step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31408 raw31408Labels = mixedMoment B node1781 node1781Labels := by
  calc
    mixedMoment B raw31408 raw31408Labels = mixedMoment B raw31408step0 raw31408step0Labels := by
      have hz : ∀ j, raw31408 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31408step0 = (fun i j => raw31408 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31408step0 raw31408; decide +kernel
      have hl : raw31408step0Labels = raw31408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31408 raw31408Labels permutation434 hz
    mixedMoment B raw31408step0 raw31408step0Labels = mixedMoment B raw31408step1 raw31408step1Labels := by
      have ha : raw31408step1 = (fun i j => raw31408step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31408step1 raw31408step0; decide +kernel
      have hl : raw31408step1Labels = raw31408step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31408step0 raw31408step0Labels permutation33 permutation3
    _ = mixedMoment B node1781 node1781Labels := by rfl

def raw31409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31409 raw31409Labels = mixedMoment B node1870 node1870Labels := by
  calc
    mixedMoment B raw31409 raw31409Labels = mixedMoment B raw31409step0 raw31409step0Labels := by
      have ha : raw31409step0 = (fun i j => raw31409 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31409step0 raw31409; decide +kernel
      have hl : raw31409step0Labels = raw31409Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31409 raw31409Labels permutation201 permutation3
    _ = mixedMoment B node1870 node1870Labels := by rfl

def raw31410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw31410step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31410 raw31410Labels = mixedMoment B node2048 node2048Labels := by
  calc
    mixedMoment B raw31410 raw31410Labels = mixedMoment B raw31410step0 raw31410step0Labels := by
      have hz : ∀ j, raw31410 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31410step0 = (fun i j => raw31410 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31410step0 raw31410; decide +kernel
      have hl : raw31410step0Labels = raw31410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31410 raw31410Labels permutation434 hz
    mixedMoment B raw31410step0 raw31410step0Labels = mixedMoment B raw31410step1 raw31410step1Labels := by
      have ha : raw31410step1 = (fun i j => raw31410step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31410step1 raw31410step0; decide +kernel
      have hl : raw31410step1Labels = raw31410step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31410step0 raw31410step0Labels permutation36 permutation3
    _ = mixedMoment B node2048 node2048Labels := by rfl

def raw31411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31411 raw31411Labels = mixedMoment B node703 node703Labels := by
  calc
    mixedMoment B raw31411 raw31411Labels = mixedMoment B raw31411step0 raw31411step0Labels := by
      have ha : raw31411step0 = (fun i j => raw31411 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31411step0 raw31411; decide +kernel
      have hl : raw31411step0Labels = raw31411Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31411 raw31411Labels permutation153 permutation3
    _ = mixedMoment B node703 node703Labels := by rfl

def raw31412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31412 raw31412Labels = mixedMoment B node1763 node1763Labels := by
  calc
    mixedMoment B raw31412 raw31412Labels = mixedMoment B raw31412step0 raw31412step0Labels := by
      have ha : raw31412step0 = (fun i j => raw31412 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31412step0 raw31412; decide +kernel
      have hl : raw31412step0Labels = raw31412Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31412 raw31412Labels permutation153 permutation3
    _ = mixedMoment B node1763 node1763Labels := by rfl

def raw31413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31413 raw31413Labels = mixedMoment B node1966 node1966Labels := by
  calc
    mixedMoment B raw31413 raw31413Labels = mixedMoment B raw31413step0 raw31413step0Labels := by
      have ha : raw31413step0 = (fun i j => raw31413 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31413step0 raw31413; decide +kernel
      have hl : raw31413step0Labels = raw31413Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31413 raw31413Labels permutation153 permutation3
    _ = mixedMoment B node1966 node1966Labels := by rfl

def raw31414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31414Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31414 raw31414Labels = mixedMoment B node2016 node2016Labels := by
  calc
    mixedMoment B raw31414 raw31414Labels = mixedMoment B raw31414step0 raw31414step0Labels := by
      have ha : raw31414step0 = (fun i j => raw31414 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31414step0 raw31414; decide +kernel
      have hl : raw31414step0Labels = raw31414Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31414 raw31414Labels permutation156 permutation3
    _ = mixedMoment B node2016 node2016Labels := by rfl

def raw31415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31415Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -3, 0], ![2, 0, -2]]
def raw31415step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw31415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31415 raw31415Labels = mixedMoment B node706 node706Labels := by
  calc
    mixedMoment B raw31415 raw31415Labels = mixedMoment B raw31415step0 raw31415step0Labels := by
      have hz : ∀ j, raw31415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31415step0 = (fun i j => raw31415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31415step0 raw31415; decide +kernel
      have hl : raw31415step0Labels = raw31415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31415 raw31415Labels permutation434 hz
    mixedMoment B raw31415step0 raw31415step0Labels = mixedMoment B raw31415step1 raw31415step1Labels := by
      have ha : raw31415step1 = (fun i j => raw31415step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31415step1 raw31415step0; decide +kernel
      have hl : raw31415step1Labels = raw31415step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31415step0 raw31415step0Labels permutation33 permutation3
    _ = mixedMoment B node706 node706Labels := by rfl

def raw31416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31416Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![3, -3, 0], ![2, 0, -2]]
def raw31416step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw31416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31416 raw31416Labels = mixedMoment B node1765 node1765Labels := by
  calc
    mixedMoment B raw31416 raw31416Labels = mixedMoment B raw31416step0 raw31416step0Labels := by
      have hz : ∀ j, raw31416 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31416step0 = (fun i j => raw31416 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31416step0 raw31416; decide +kernel
      have hl : raw31416step0Labels = raw31416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31416 raw31416Labels permutation434 hz
    mixedMoment B raw31416step0 raw31416step0Labels = mixedMoment B raw31416step1 raw31416step1Labels := by
      have ha : raw31416step1 = (fun i j => raw31416step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31416step1 raw31416step0; decide +kernel
      have hl : raw31416step1Labels = raw31416step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31416step0 raw31416step0Labels permutation33 permutation3
    _ = mixedMoment B node1765 node1765Labels := by rfl

def raw31417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31417Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![3, -3, 0], ![2, 0, -2]]
def raw31417step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw31417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31417step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw31417step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31417 raw31417Labels = mixedMoment B node1804 node1804Labels := by
  calc
    mixedMoment B raw31417 raw31417Labels = mixedMoment B raw31417step0 raw31417step0Labels := by
      have hz : ∀ j, raw31417 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31417step0 = (fun i j => raw31417 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31417step0 raw31417; decide +kernel
      have hl : raw31417step0Labels = raw31417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31417 raw31417Labels permutation434 hz
    mixedMoment B raw31417step0 raw31417step0Labels = mixedMoment B raw31417step1 raw31417step1Labels := by
      have ha : raw31417step1 = (fun i j => raw31417step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31417step1 raw31417step0; decide +kernel
      have hl : raw31417step1Labels = raw31417step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31417step0 raw31417step0Labels permutation125 permutation3
    mixedMoment B raw31417step1 raw31417step1Labels = mixedMoment B raw31417step2 raw31417step2Labels := by
      have ha : raw31417step2 = -raw31417step1 := by apply Matrix.ext; change ∀ i j, raw31417step2 i j = -(raw31417step1 i j); unfold raw31417step2 raw31417step1; decide +kernel
      have hl : raw31417step2Labels = raw31417step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1804 node1804Labels := by rfl

def raw31418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31418Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw31418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw31418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31418 raw31418Labels = mixedMoment B node1784 node1784Labels := by
  calc
    mixedMoment B raw31418 raw31418Labels = mixedMoment B raw31418step0 raw31418step0Labels := by
      have ha : raw31418step0 = (fun i j => raw31418 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31418step0 raw31418; decide +kernel
      have hl : raw31418step0Labels = raw31418Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31418 raw31418Labels permutation582 permutation3
    mixedMoment B raw31418step0 raw31418step0Labels = mixedMoment B raw31418step1 raw31418step1Labels := by
      have ha : raw31418step1 = -raw31418step0 := by apply Matrix.ext; change ∀ i j, raw31418step1 i j = -(raw31418step0 i j); unfold raw31418step1 raw31418step0; decide +kernel
      have hl : raw31418step1Labels = raw31418step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1784 node1784Labels := by rfl

def raw31419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw31419Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -3, 0], ![1, 1, -2]]
def raw31419step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw31419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31419 raw31419Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw31419 raw31419Labels = mixedMoment B raw31419step0 raw31419step0Labels := by
      have hz : ∀ j, raw31419 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31419step0 = (fun i j => raw31419 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31419step0 raw31419; decide +kernel
      have hl : raw31419step0Labels = raw31419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31419 raw31419Labels permutation434 hz
    mixedMoment B raw31419step0 raw31419step0Labels = mixedMoment B raw31419step1 raw31419step1Labels := by
      have ha : raw31419step1 = (fun i j => raw31419step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31419step1 raw31419step0; decide +kernel
      have hl : raw31419step1Labels = raw31419step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31419step0 raw31419step0Labels permutation33 permutation3
    _ = mixedMoment B node2018 node2018Labels := by rfl

def raw31420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31420Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, -1, -2]]
def raw31420step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31420 raw31420Labels = mixedMoment B node708 node708Labels := by
  calc
    mixedMoment B raw31420 raw31420Labels = mixedMoment B raw31420step0 raw31420step0Labels := by
      have hz : ∀ j, raw31420 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31420step0 = (fun i j => raw31420 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31420step0 raw31420; decide +kernel
      have hl : raw31420step0Labels = raw31420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31420 raw31420Labels permutation434 hz
    mixedMoment B raw31420step0 raw31420step0Labels = mixedMoment B raw31420step1 raw31420step1Labels := by
      have ha : raw31420step1 = (fun i j => raw31420step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31420step1 raw31420step0; decide +kernel
      have hl : raw31420step1Labels = raw31420step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31420step0 raw31420step0Labels permutation32 permutation3
    _ = mixedMoment B node708 node708Labels := by rfl

def raw31421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31421Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -2, 0], ![3, -1, -2]]
def raw31421step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31421 raw31421Labels = mixedMoment B node1767 node1767Labels := by
  calc
    mixedMoment B raw31421 raw31421Labels = mixedMoment B raw31421step0 raw31421step0Labels := by
      have hz : ∀ j, raw31421 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31421step0 = (fun i j => raw31421 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31421step0 raw31421; decide +kernel
      have hl : raw31421step0Labels = raw31421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31421 raw31421Labels permutation434 hz
    mixedMoment B raw31421step0 raw31421step0Labels = mixedMoment B raw31421step1 raw31421step1Labels := by
      have ha : raw31421step1 = (fun i j => raw31421step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31421step1 raw31421step0; decide +kernel
      have hl : raw31421step1Labels = raw31421step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31421step0 raw31421step0Labels permutation32 permutation3
    _ = mixedMoment B node1767 node1767Labels := by rfl

def raw31422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31422Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -2, 0], ![3, -1, -2]]
def raw31422step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31422 raw31422Labels = mixedMoment B node1970 node1970Labels := by
  calc
    mixedMoment B raw31422 raw31422Labels = mixedMoment B raw31422step0 raw31422step0Labels := by
      have hz : ∀ j, raw31422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31422step0 = (fun i j => raw31422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31422step0 raw31422; decide +kernel
      have hl : raw31422step0Labels = raw31422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31422 raw31422Labels permutation434 hz
    mixedMoment B raw31422step0 raw31422step0Labels = mixedMoment B raw31422step1 raw31422step1Labels := by
      have ha : raw31422step1 = (fun i j => raw31422step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31422step1 raw31422step0; decide +kernel
      have hl : raw31422step1Labels = raw31422step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31422step0 raw31422step0Labels permutation32 permutation3
    _ = mixedMoment B node1970 node1970Labels := by rfl

def raw31423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31423Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31423 raw31423Labels = mixedMoment B node1861 node1861Labels := by
  calc
    mixedMoment B raw31423 raw31423Labels = mixedMoment B raw31423step0 raw31423step0Labels := by
      have ha : raw31423step0 = (fun i j => raw31423 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31423step0 raw31423; decide +kernel
      have hl : raw31423step0Labels = raw31423Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31423 raw31423Labels permutation200 permutation3
    _ = mixedMoment B node1861 node1861Labels := by rfl

def raw31424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -2, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31424step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31424step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw31424step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31424step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31424step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31424step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31424step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31424 raw31424Labels = mixedMoment B node4411 node4411Labels := by
  calc
    mixedMoment B raw31424 raw31424Labels = mixedMoment B raw31424step0 raw31424step0Labels := by
      have hz : ∀ j, raw31424 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31424step0 = (fun i j => raw31424 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31424step0 raw31424; decide +kernel
      have hl : raw31424step0Labels = raw31424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31424 raw31424Labels permutation434 hz
    mixedMoment B raw31424step0 raw31424step0Labels = mixedMoment B raw31424step1 raw31424step1Labels := by
      have ha : raw31424step1 = (fun i j => raw31424step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31424step1 raw31424step0; decide +kernel
      have hl : raw31424step1Labels = raw31424step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31424step0 raw31424step0Labels permutation36 permutation4
    mixedMoment B raw31424step1 raw31424step1Labels = mixedMoment B raw31424step2 raw31424step2Labels := by
      have ha : raw31424step2 = -raw31424step1 := by apply Matrix.ext; change ∀ i j, raw31424step2 i j = -(raw31424step1 i j); unfold raw31424step2 raw31424step1; decide +kernel
      have hl : raw31424step2Labels = raw31424step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31424step2 raw31424step2Labels = mixedMoment B raw31424step3 raw31424step3Labels := by
      have ha : raw31424step3 = raw31424step2 := by apply Matrix.ext; unfold raw31424step3 raw31424step2; decide +kernel
      have hl : raw31424step2Labels = labelEmbedding7 ∘ raw31424step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31424step2 raw31424step2Labels raw31424step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4411 node4411Labels := by rfl

def raw31425 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31425step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw31425step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31425step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31425step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31425step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31425step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31425 raw31425Labels = mixedMoment B node4784 node4784Labels := by
  calc
    mixedMoment B raw31425 raw31425Labels = mixedMoment B raw31425step0 raw31425step0Labels := by
      have ha : raw31425step0 = (fun i j => raw31425 (permutation204 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31425step0 raw31425; decide +kernel
      have hl : raw31425step0Labels = raw31425Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31425 raw31425Labels permutation204 permutation4
    mixedMoment B raw31425step0 raw31425step0Labels = mixedMoment B raw31425step1 raw31425step1Labels := by
      have ha : raw31425step1 = -raw31425step0 := by apply Matrix.ext; change ∀ i j, raw31425step1 i j = -(raw31425step0 i j); unfold raw31425step1 raw31425step0; decide +kernel
      have hl : raw31425step1Labels = raw31425step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31425step1 raw31425step1Labels = mixedMoment B raw31425step2 raw31425step2Labels := by
      have ha : raw31425step2 = raw31425step1 := by apply Matrix.ext; unfold raw31425step2 raw31425step1; decide +kernel
      have hl : raw31425step1Labels = labelEmbedding7 ∘ raw31425step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31425step1 raw31425step1Labels raw31425step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4784 node4784Labels := by rfl

def raw31426 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31426step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw31426step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw31426step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31426 raw31426Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw31426 raw31426Labels = mixedMoment B raw31426step0 raw31426step0Labels := by
      have hz : ∀ j, raw31426 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31426step0 = (fun i j => raw31426 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31426step0 raw31426; decide +kernel
      have hl : raw31426step0Labels = raw31426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31426 raw31426Labels permutation434 hz
    mixedMoment B raw31426step0 raw31426step0Labels = mixedMoment B raw31426step1 raw31426step1Labels := by
      have ha : raw31426step1 = (fun i j => raw31426step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31426step1 raw31426step0; decide +kernel
      have hl : raw31426step1Labels = raw31426step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31426step0 raw31426step0Labels permutation33 permutation6
    mixedMoment B raw31426step1 raw31426step1Labels = mixedMoment B raw31426step2 raw31426step2Labels := by
      have ha : raw31426step2 = raw31426step1 := by apply Matrix.ext; unfold raw31426step2 raw31426step1; decide +kernel
      have hl : raw31426step1Labels = labelEmbedding9 ∘ raw31426step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31426step1 raw31426step1Labels raw31426step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4821 node4821Labels := by rfl

def raw31427 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw31427step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw31427step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31427 raw31427Labels = mixedMoment B node4820 node4820Labels := by
  calc
    mixedMoment B raw31427 raw31427Labels = mixedMoment B raw31427step0 raw31427step0Labels := by
      have hz : ∀ j, raw31427 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31427step0 = (fun i j => raw31427 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31427step0 raw31427; decide +kernel
      have hl : raw31427step0Labels = raw31427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31427 raw31427Labels permutation434 hz
    mixedMoment B raw31427step0 raw31427step0Labels = mixedMoment B raw31427step1 raw31427step1Labels := by
      have ha : raw31427step1 = (fun i j => raw31427step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31427step1 raw31427step0; decide +kernel
      have hl : raw31427step1Labels = raw31427step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31427step0 raw31427step0Labels permutation33 permutation6
    mixedMoment B raw31427step1 raw31427step1Labels = mixedMoment B raw31427step2 raw31427step2Labels := by
      have ha : raw31427step2 = raw31427step1 := by apply Matrix.ext; unfold raw31427step2 raw31427step1; decide +kernel
      have hl : raw31427step1Labels = labelEmbedding9 ∘ raw31427step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31427step1 raw31427step1Labels raw31427step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4820 node4820Labels := by rfl

def raw31428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw31428step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31428step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31428step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31428step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31428step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31428 raw31428Labels = mixedMoment B node4406 node4406Labels := by
  calc
    mixedMoment B raw31428 raw31428Labels = mixedMoment B raw31428step0 raw31428step0Labels := by
      have ha : raw31428step0 = (fun i j => raw31428 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31428step0 raw31428; decide +kernel
      have hl : raw31428step0Labels = raw31428Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31428 raw31428Labels permutation170 permutation4
    mixedMoment B raw31428step0 raw31428step0Labels = mixedMoment B raw31428step1 raw31428step1Labels := by
      have ha : raw31428step1 = -raw31428step0 := by apply Matrix.ext; change ∀ i j, raw31428step1 i j = -(raw31428step0 i j); unfold raw31428step1 raw31428step0; decide +kernel
      have hl : raw31428step1Labels = raw31428step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31428step1 raw31428step1Labels = mixedMoment B raw31428step2 raw31428step2Labels := by
      have ha : raw31428step2 = raw31428step1 := by apply Matrix.ext; unfold raw31428step2 raw31428step1; decide +kernel
      have hl : raw31428step1Labels = labelEmbedding7 ∘ raw31428step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31428step1 raw31428step1Labels raw31428step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4406 node4406Labels := by rfl

def raw31429 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31429step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31429step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31429 raw31429Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw31429 raw31429Labels = mixedMoment B raw31429step0 raw31429step0Labels := by
      have ha : raw31429step0 = (fun i j => raw31429 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31429step0 raw31429; decide +kernel
      have hl : raw31429step0Labels = raw31429Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31429 raw31429Labels permutation153 permutation6
    mixedMoment B raw31429step0 raw31429step0Labels = mixedMoment B raw31429step1 raw31429step1Labels := by
      have ha : raw31429step1 = raw31429step0 := by apply Matrix.ext; unfold raw31429step1 raw31429step0; decide +kernel
      have hl : raw31429step0Labels = labelEmbedding9 ∘ raw31429step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31429step0 raw31429step0Labels raw31429step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4795 node4795Labels := by rfl

def raw31430 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31430step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31430step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31430step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31430 raw31430Labels = mixedMoment B node4794 node4794Labels := by
  calc
    mixedMoment B raw31430 raw31430Labels = mixedMoment B raw31430step0 raw31430step0Labels := by
      have ha : raw31430step0 = (fun i j => raw31430 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31430step0 raw31430; decide +kernel
      have hl : raw31430step0Labels = raw31430Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31430 raw31430Labels permutation153 permutation6
    mixedMoment B raw31430step0 raw31430step0Labels = mixedMoment B raw31430step1 raw31430step1Labels := by
      have ha : raw31430step1 = raw31430step0 := by apply Matrix.ext; unfold raw31430step1 raw31430step0; decide +kernel
      have hl : raw31430step0Labels = labelEmbedding9 ∘ raw31430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31430step0 raw31430step0Labels raw31430step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4794 node4794Labels := by rfl

def raw31431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31431step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw31431step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw31431step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31431step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw31431step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31431 raw31431Labels = mixedMoment B node4408 node4408Labels := by
  calc
    mixedMoment B raw31431 raw31431Labels = mixedMoment B raw31431step0 raw31431step0Labels := by
      have hz : ∀ j, raw31431 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31431step0 = (fun i j => raw31431 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31431step0 raw31431; decide +kernel
      have hl : raw31431step0Labels = raw31431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31431 raw31431Labels permutation434 hz
    mixedMoment B raw31431step0 raw31431step0Labels = mixedMoment B raw31431step1 raw31431step1Labels := by
      have ha : raw31431step1 = (fun i j => raw31431step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31431step1 raw31431step0; decide +kernel
      have hl : raw31431step1Labels = raw31431step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31431step0 raw31431step0Labels permutation36 permutation4
    mixedMoment B raw31431step1 raw31431step1Labels = mixedMoment B raw31431step2 raw31431step2Labels := by
      have ha : raw31431step2 = -raw31431step1 := by apply Matrix.ext; change ∀ i j, raw31431step2 i j = -(raw31431step1 i j); unfold raw31431step2 raw31431step1; decide +kernel
      have hl : raw31431step2Labels = raw31431step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31431step2 raw31431step2Labels = mixedMoment B raw31431step3 raw31431step3Labels := by
      have ha : raw31431step3 = raw31431step2 := by apply Matrix.ext; unfold raw31431step3 raw31431step2; decide +kernel
      have hl : raw31431step2Labels = labelEmbedding7 ∘ raw31431step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31431step2 raw31431step2Labels raw31431step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4408 node4408Labels := by rfl

def raw31432 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31432step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31432step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31432 raw31432Labels = mixedMoment B node4781 node4781Labels := by
  calc
    mixedMoment B raw31432 raw31432Labels = mixedMoment B raw31432step0 raw31432step0Labels := by
      have ha : raw31432step0 = (fun i j => raw31432 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31432step0 raw31432; decide +kernel
      have hl : raw31432step0Labels = raw31432Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31432 raw31432Labels permutation159 permutation6
    mixedMoment B raw31432step0 raw31432step0Labels = mixedMoment B raw31432step1 raw31432step1Labels := by
      have ha : raw31432step1 = raw31432step0 := by apply Matrix.ext; unfold raw31432step1 raw31432step0; decide +kernel
      have hl : raw31432step0Labels = labelEmbedding9 ∘ raw31432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31432step0 raw31432step0Labels raw31432step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4781 node4781Labels := by rfl

def raw31433 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw31433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw31433step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31433step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw31433step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31433step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw31433step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31433 raw31433Labels = mixedMoment B node4809 node4809Labels := by
  calc
    mixedMoment B raw31433 raw31433Labels = mixedMoment B raw31433step0 raw31433step0Labels := by
      have hz : ∀ j, raw31433 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31433step0 = (fun i j => raw31433 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31433step0 raw31433; decide +kernel
      have hl : raw31433step0Labels = raw31433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31433 raw31433Labels permutation434 hz
    mixedMoment B raw31433step0 raw31433step0Labels = mixedMoment B raw31433step1 raw31433step1Labels := by
      have ha : raw31433step1 = (fun i j => raw31433step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31433step1 raw31433step0; decide +kernel
      have hl : raw31433step1Labels = raw31433step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31433step0 raw31433step0Labels permutation33 permutation6
    mixedMoment B raw31433step1 raw31433step1Labels = mixedMoment B raw31433step2 raw31433step2Labels := by
      have ha : raw31433step2 = raw31433step1 := by apply Matrix.ext; unfold raw31433step2 raw31433step1; decide +kernel
      have hl : raw31433step1Labels = labelEmbedding9 ∘ raw31433step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31433step1 raw31433step1Labels raw31433step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4809 node4809Labels := by rfl

def raw31434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31434step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31434step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31434step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31434step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31434step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31434step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31434 raw31434Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw31434 raw31434Labels = mixedMoment B raw31434step0 raw31434step0Labels := by
      have hz : ∀ j, raw31434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31434step0 = (fun i j => raw31434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31434step0 raw31434; decide +kernel
      have hl : raw31434step0Labels = raw31434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31434 raw31434Labels permutation434 hz
    mixedMoment B raw31434step0 raw31434step0Labels = mixedMoment B raw31434step1 raw31434step1Labels := by
      have ha : raw31434step1 = (fun i j => raw31434step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31434step1 raw31434step0; decide +kernel
      have hl : raw31434step1Labels = raw31434step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31434step0 raw31434step0Labels permutation33 permutation4
    mixedMoment B raw31434step1 raw31434step1Labels = mixedMoment B raw31434step2 raw31434step2Labels := by
      have ha : raw31434step2 = -raw31434step1 := by apply Matrix.ext; change ∀ i j, raw31434step2 i j = -(raw31434step1 i j); unfold raw31434step2 raw31434step1; decide +kernel
      have hl : raw31434step2Labels = raw31434step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31434step2 raw31434step2Labels = mixedMoment B raw31434step3 raw31434step3Labels := by
      have ha : raw31434step3 = raw31434step2 := by apply Matrix.ext; unfold raw31434step3 raw31434step2; decide +kernel
      have hl : raw31434step2Labels = labelEmbedding7 ∘ raw31434step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31434step2 raw31434step2Labels raw31434step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

def raw31435 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31435Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31435step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31435step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31435 raw31435Labels = mixedMoment B node2990 node2990Labels := by
  calc
    mixedMoment B raw31435 raw31435Labels = mixedMoment B raw31435step0 raw31435step0Labels := by
      have hz : ∀ j, raw31435 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31435step0 = (fun i j => raw31435 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31435step0 raw31435; decide +kernel
      have hl : raw31435step0Labels = raw31435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31435 raw31435Labels permutation434 hz
    mixedMoment B raw31435step0 raw31435step0Labels = mixedMoment B raw31435step1 raw31435step1Labels := by
      have ha : raw31435step1 = (fun i j => raw31435step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31435step1 raw31435step0; decide +kernel
      have hl : raw31435step1Labels = raw31435step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31435step0 raw31435step0Labels permutation32 permutation7
    mixedMoment B raw31435step1 raw31435step1Labels = mixedMoment B raw31435step2 raw31435step2Labels := by
      have ha : raw31435step2 = raw31435step1 := by apply Matrix.ext; unfold raw31435step2 raw31435step1; decide +kernel
      have hl : raw31435step1Labels = labelEmbedding1 ∘ raw31435step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31435step1 raw31435step1Labels raw31435step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2990 node2990Labels := by rfl

def raw31436 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31436Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31436step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31436step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31436 raw31436Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw31436 raw31436Labels = mixedMoment B raw31436step0 raw31436step0Labels := by
      have ha : raw31436step0 = (fun i j => raw31436 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31436step0 raw31436; decide +kernel
      have hl : raw31436step0Labels = raw31436Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31436 raw31436Labels permutation152 permutation7
    mixedMoment B raw31436step0 raw31436step0Labels = mixedMoment B raw31436step1 raw31436step1Labels := by
      have ha : raw31436step1 = raw31436step0 := by apply Matrix.ext; unfold raw31436step1 raw31436step0; decide +kernel
      have hl : raw31436step0Labels = labelEmbedding1 ∘ raw31436step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31436step0 raw31436step0Labels raw31436step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2916 node2916Labels := by rfl

def raw31437 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31437Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31437step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31437step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31437step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31437step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31437 raw31437Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw31437 raw31437Labels = mixedMoment B raw31437step0 raw31437step0Labels := by
      have hz : ∀ j, raw31437 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31437step0 = (fun i j => raw31437 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31437step0 raw31437; decide +kernel
      have hl : raw31437step0Labels = raw31437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31437 raw31437Labels permutation434 hz
    mixedMoment B raw31437step0 raw31437step0Labels = mixedMoment B raw31437step1 raw31437step1Labels := by
      have ha : raw31437step1 = (fun i j => raw31437step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31437step1 raw31437step0; decide +kernel
      have hl : raw31437step1Labels = raw31437step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31437step0 raw31437step0Labels permutation32 permutation7
    mixedMoment B raw31437step1 raw31437step1Labels = mixedMoment B raw31437step2 raw31437step2Labels := by
      have ha : raw31437step2 = raw31437step1 := by apply Matrix.ext; unfold raw31437step2 raw31437step1; decide +kernel
      have hl : raw31437step1Labels = labelEmbedding1 ∘ raw31437step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31437step1 raw31437step1Labels raw31437step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw31438 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31438Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31438step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw31438step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31438step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw31438step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31438 raw31438Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw31438 raw31438Labels = mixedMoment B raw31438step0 raw31438step0Labels := by
      have hz : ∀ j, raw31438 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31438step0 = (fun i j => raw31438 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31438step0 raw31438; decide +kernel
      have hl : raw31438step0Labels = raw31438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31438 raw31438Labels permutation434 hz
    mixedMoment B raw31438step0 raw31438step0Labels = mixedMoment B raw31438step1 raw31438step1Labels := by
      have ha : raw31438step1 = (fun i j => raw31438step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31438step1 raw31438step0; decide +kernel
      have hl : raw31438step1Labels = raw31438step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31438step0 raw31438step0Labels permutation32 permutation7
    mixedMoment B raw31438step1 raw31438step1Labels = mixedMoment B raw31438step2 raw31438step2Labels := by
      have ha : raw31438step2 = raw31438step1 := by apply Matrix.ext; unfold raw31438step2 raw31438step1; decide +kernel
      have hl : raw31438step1Labels = labelEmbedding1 ∘ raw31438step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31438step1 raw31438step1Labels raw31438step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2930 node2930Labels := by rfl

def raw31439 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31439Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31439step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31439step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw31439step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31439step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw31439step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31439step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw31439step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31439 raw31439Labels = mixedMoment B node3187 node3187Labels := by
  calc
    mixedMoment B raw31439 raw31439Labels = mixedMoment B raw31439step0 raw31439step0Labels := by
      have hz : ∀ j, raw31439 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31439step0 = (fun i j => raw31439 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31439step0 raw31439; decide +kernel
      have hl : raw31439step0Labels = raw31439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31439 raw31439Labels permutation434 hz
    mixedMoment B raw31439step0 raw31439step0Labels = mixedMoment B raw31439step1 raw31439step1Labels := by
      have hz : ∀ j, raw31439step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31439step1 = (fun i j => raw31439step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31439step1 raw31439step0; decide +kernel
      have hl : raw31439step1Labels = raw31439step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31439step0 raw31439step0Labels permutation80 hz
    mixedMoment B raw31439step1 raw31439step1Labels = mixedMoment B raw31439step2 raw31439step2Labels := by
      have ha : raw31439step2 = (fun i j => raw31439step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31439step2 raw31439step1; decide +kernel
      have hl : raw31439step2Labels = raw31439step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31439step1 raw31439step1Labels permutation8 permutation7
    mixedMoment B raw31439step2 raw31439step2Labels = mixedMoment B raw31439step3 raw31439step3Labels := by
      have ha : raw31439step3 = raw31439step2 := by apply Matrix.ext; unfold raw31439step3 raw31439step2; decide +kernel
      have hl : raw31439step2Labels = labelEmbedding1 ∘ raw31439step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31439step2 raw31439step2Labels raw31439step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3187 node3187Labels := by rfl

def raw31440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31440Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -2, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31440step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw31440step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31440step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31440step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31440step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31440 raw31440Labels = mixedMoment B node1362 node1362Labels := by
  calc
    mixedMoment B raw31440 raw31440Labels = mixedMoment B raw31440step0 raw31440step0Labels := by
      have hz : ∀ j, raw31440 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31440step0 = (fun i j => raw31440 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31440step0 raw31440; decide +kernel
      have hl : raw31440step0Labels = raw31440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31440 raw31440Labels permutation434 hz
    mixedMoment B raw31440step0 raw31440step0Labels = mixedMoment B raw31440step1 raw31440step1Labels := by
      have ha : raw31440step1 = (fun i j => raw31440step0 (permutation51 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31440step1 raw31440step0; decide +kernel
      have hl : raw31440step1Labels = raw31440step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31440step0 raw31440step0Labels permutation51 permutation5
    mixedMoment B raw31440step1 raw31440step1Labels = mixedMoment B raw31440step2 raw31440step2Labels := by
      have ha : raw31440step2 = -raw31440step1 := by apply Matrix.ext; change ∀ i j, raw31440step2 i j = -(raw31440step1 i j); unfold raw31440step2 raw31440step1; decide +kernel
      have hl : raw31440step2Labels = raw31440step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31440step2 raw31440step2Labels = mixedMoment B raw31440step3 raw31440step3Labels := by
      have ha : raw31440step3 = raw31440step2 := by apply Matrix.ext; unfold raw31440step3 raw31440step2; decide +kernel
      have hl : raw31440step2Labels = labelEmbedding1 ∘ raw31440step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31440step2 raw31440step2Labels raw31440step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1362 node1362Labels := by rfl

def raw31441 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31441Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31441step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, -1, 0], ![0, 2, -2], ![-2, 2, 0], ![-2, 0, 2]]
def raw31441step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31441step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw31441step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31441step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw31441step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31441 raw31441Labels = mixedMoment B node3219 node3219Labels := by
  calc
    mixedMoment B raw31441 raw31441Labels = mixedMoment B raw31441step0 raw31441step0Labels := by
      have hz : ∀ j, raw31441 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31441step0 = (fun i j => raw31441 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31441step0 raw31441; decide +kernel
      have hl : raw31441step0Labels = raw31441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31441 raw31441Labels permutation434 hz
    mixedMoment B raw31441step0 raw31441step0Labels = mixedMoment B raw31441step1 raw31441step1Labels := by
      have ha : raw31441step1 = (fun i j => raw31441step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31441step1 raw31441step0; decide +kernel
      have hl : raw31441step1Labels = raw31441step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31441step0 raw31441step0Labels permutation37 permutation5
    mixedMoment B raw31441step1 raw31441step1Labels = mixedMoment B raw31441step2 raw31441step2Labels := by
      have ha : raw31441step2 = -raw31441step1 := by apply Matrix.ext; change ∀ i j, raw31441step2 i j = -(raw31441step1 i j); unfold raw31441step2 raw31441step1; decide +kernel
      have hl : raw31441step2Labels = raw31441step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31441step2 raw31441step2Labels = mixedMoment B raw31441step3 raw31441step3Labels := by
      have ha : raw31441step3 = raw31441step2 := by apply Matrix.ext; unfold raw31441step3 raw31441step2; decide +kernel
      have hl : raw31441step2Labels = labelEmbedding1 ∘ raw31441step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31441step2 raw31441step2Labels raw31441step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3219 node3219Labels := by rfl

def raw31442 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31442Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw31442step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31442step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31442step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31442 raw31442Labels = mixedMoment B node3194 node3194Labels := by
  calc
    mixedMoment B raw31442 raw31442Labels = mixedMoment B raw31442step0 raw31442step0Labels := by
      have ha : raw31442step0 = (fun i j => raw31442 (permutation219 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31442step0 raw31442; decide +kernel
      have hl : raw31442step0Labels = raw31442Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31442 raw31442Labels permutation219 permutation5
    mixedMoment B raw31442step0 raw31442step0Labels = mixedMoment B raw31442step1 raw31442step1Labels := by
      have ha : raw31442step1 = -raw31442step0 := by apply Matrix.ext; change ∀ i j, raw31442step1 i j = -(raw31442step0 i j); unfold raw31442step1 raw31442step0; decide +kernel
      have hl : raw31442step1Labels = raw31442step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31442step1 raw31442step1Labels = mixedMoment B raw31442step2 raw31442step2Labels := by
      have ha : raw31442step2 = raw31442step1 := by apply Matrix.ext; unfold raw31442step2 raw31442step1; decide +kernel
      have hl : raw31442step1Labels = labelEmbedding1 ∘ raw31442step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31442step1 raw31442step1Labels raw31442step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3194 node3194Labels := by rfl

def raw31443 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31443Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31443step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw31443step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw31443step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31443 raw31443Labels = mixedMoment B node3198 node3198Labels := by
  calc
    mixedMoment B raw31443 raw31443Labels = mixedMoment B raw31443step0 raw31443step0Labels := by
      have hz : ∀ j, raw31443 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31443step0 = (fun i j => raw31443 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31443step0 raw31443; decide +kernel
      have hl : raw31443step0Labels = raw31443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31443 raw31443Labels permutation434 hz
    mixedMoment B raw31443step0 raw31443step0Labels = mixedMoment B raw31443step1 raw31443step1Labels := by
      have ha : raw31443step1 = (fun i j => raw31443step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31443step1 raw31443step0; decide +kernel
      have hl : raw31443step1Labels = raw31443step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31443step0 raw31443step0Labels permutation32 permutation7
    mixedMoment B raw31443step1 raw31443step1Labels = mixedMoment B raw31443step2 raw31443step2Labels := by
      have ha : raw31443step2 = raw31443step1 := by apply Matrix.ext; unfold raw31443step2 raw31443step1; decide +kernel
      have hl : raw31443step1Labels = labelEmbedding1 ∘ raw31443step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31443step1 raw31443step1Labels raw31443step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3198 node3198Labels := by rfl

def raw31444 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31444step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw31444step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31444step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31444step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31444step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31444 raw31444Labels = mixedMoment B node3151 node3151Labels := by
  calc
    mixedMoment B raw31444 raw31444Labels = mixedMoment B raw31444step0 raw31444step0Labels := by
      have hz : ∀ j, raw31444 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31444step0 = (fun i j => raw31444 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31444step0 raw31444; decide +kernel
      have hl : raw31444step0Labels = raw31444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31444 raw31444Labels permutation434 hz
    mixedMoment B raw31444step0 raw31444step0Labels = mixedMoment B raw31444step1 raw31444step1Labels := by
      have ha : raw31444step1 = (fun i j => raw31444step0 (permutation51 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31444step1 raw31444step0; decide +kernel
      have hl : raw31444step1Labels = raw31444step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31444step0 raw31444step0Labels permutation51 permutation5
    mixedMoment B raw31444step1 raw31444step1Labels = mixedMoment B raw31444step2 raw31444step2Labels := by
      have ha : raw31444step2 = -raw31444step1 := by apply Matrix.ext; change ∀ i j, raw31444step2 i j = -(raw31444step1 i j); unfold raw31444step2 raw31444step1; decide +kernel
      have hl : raw31444step2Labels = raw31444step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31444step2 raw31444step2Labels = mixedMoment B raw31444step3 raw31444step3Labels := by
      have ha : raw31444step3 = raw31444step2 := by apply Matrix.ext; unfold raw31444step3 raw31444step2; decide +kernel
      have hl : raw31444step2Labels = labelEmbedding1 ∘ raw31444step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31444step2 raw31444step2Labels raw31444step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3151 node3151Labels := by rfl

def raw31445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31445Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw31445step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31445step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31445step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31445step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31445 raw31445Labels = mixedMoment B node1360 node1360Labels := by
  calc
    mixedMoment B raw31445 raw31445Labels = mixedMoment B raw31445step0 raw31445step0Labels := by
      have ha : raw31445step0 = (fun i j => raw31445 (permutation246 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31445step0 raw31445; decide +kernel
      have hl : raw31445step0Labels = raw31445Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31445 raw31445Labels permutation246 permutation5
    mixedMoment B raw31445step0 raw31445step0Labels = mixedMoment B raw31445step1 raw31445step1Labels := by
      have ha : raw31445step1 = -raw31445step0 := by apply Matrix.ext; change ∀ i j, raw31445step1 i j = -(raw31445step0 i j); unfold raw31445step1 raw31445step0; decide +kernel
      have hl : raw31445step1Labels = raw31445step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31445step1 raw31445step1Labels = mixedMoment B raw31445step2 raw31445step2Labels := by
      have ha : raw31445step2 = raw31445step1 := by apply Matrix.ext; unfold raw31445step2 raw31445step1; decide +kernel
      have hl : raw31445step1Labels = labelEmbedding1 ∘ raw31445step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31445step1 raw31445step1Labels raw31445step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1360 node1360Labels := by rfl

def raw31446 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw31446step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31446step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31446step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31446step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31446step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31446 raw31446Labels = mixedMoment B node3218 node3218Labels := by
  calc
    mixedMoment B raw31446 raw31446Labels = mixedMoment B raw31446step0 raw31446step0Labels := by
      have ha : raw31446step0 = (fun i j => raw31446 (permutation170 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31446step0 raw31446; decide +kernel
      have hl : raw31446step0Labels = raw31446Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31446 raw31446Labels permutation170 permutation5
    mixedMoment B raw31446step0 raw31446step0Labels = mixedMoment B raw31446step1 raw31446step1Labels := by
      have ha : raw31446step1 = -raw31446step0 := by apply Matrix.ext; change ∀ i j, raw31446step1 i j = -(raw31446step0 i j); unfold raw31446step1 raw31446step0; decide +kernel
      have hl : raw31446step1Labels = raw31446step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31446step1 raw31446step1Labels = mixedMoment B raw31446step2 raw31446step2Labels := by
      have ha : raw31446step2 = raw31446step1 := by apply Matrix.ext; unfold raw31446step2 raw31446step1; decide +kernel
      have hl : raw31446step1Labels = labelEmbedding1 ∘ raw31446step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31446step1 raw31446step1Labels raw31446step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3218 node3218Labels := by rfl

def raw31447 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31447Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31447step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31447step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31447 raw31447Labels = mixedMoment B node3199 node3199Labels := by
  calc
    mixedMoment B raw31447 raw31447Labels = mixedMoment B raw31447step0 raw31447step0Labels := by
      have ha : raw31447step0 = (fun i j => raw31447 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31447step0 raw31447; decide +kernel
      have hl : raw31447step0Labels = raw31447Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31447 raw31447Labels permutation152 permutation7
    mixedMoment B raw31447step0 raw31447step0Labels = mixedMoment B raw31447step1 raw31447step1Labels := by
      have ha : raw31447step1 = raw31447step0 := by apply Matrix.ext; unfold raw31447step1 raw31447step0; decide +kernel
      have hl : raw31447step0Labels = labelEmbedding1 ∘ raw31447step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31447step0 raw31447step0Labels raw31447step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3199 node3199Labels := by rfl

def raw31448 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw31448step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31448step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31448step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31448 raw31448Labels = mixedMoment B node3150 node3150Labels := by
  calc
    mixedMoment B raw31448 raw31448Labels = mixedMoment B raw31448step0 raw31448step0Labels := by
      have ha : raw31448step0 = (fun i j => raw31448 (permutation246 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31448step0 raw31448; decide +kernel
      have hl : raw31448step0Labels = raw31448Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31448 raw31448Labels permutation246 permutation5
    mixedMoment B raw31448step0 raw31448step0Labels = mixedMoment B raw31448step1 raw31448step1Labels := by
      have ha : raw31448step1 = -raw31448step0 := by apply Matrix.ext; change ∀ i j, raw31448step1 i j = -(raw31448step0 i j); unfold raw31448step1 raw31448step0; decide +kernel
      have hl : raw31448step1Labels = raw31448step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31448step1 raw31448step1Labels = mixedMoment B raw31448step2 raw31448step2Labels := by
      have ha : raw31448step2 = raw31448step1 := by apply Matrix.ext; unfold raw31448step2 raw31448step1; decide +kernel
      have hl : raw31448step1Labels = labelEmbedding1 ∘ raw31448step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31448step1 raw31448step1Labels raw31448step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3150 node3150Labels := by rfl

def raw31449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31449step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw31449step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31449step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31449step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31449step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31449step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31449 raw31449Labels = mixedMoment B node1361 node1361Labels := by
  calc
    mixedMoment B raw31449 raw31449Labels = mixedMoment B raw31449step0 raw31449step0Labels := by
      have hz : ∀ j, raw31449 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31449step0 = (fun i j => raw31449 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31449step0 raw31449; decide +kernel
      have hl : raw31449step0Labels = raw31449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31449 raw31449Labels permutation434 hz
    mixedMoment B raw31449step0 raw31449step0Labels = mixedMoment B raw31449step1 raw31449step1Labels := by
      have ha : raw31449step1 = (fun i j => raw31449step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31449step1 raw31449step0; decide +kernel
      have hl : raw31449step1Labels = raw31449step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31449step0 raw31449step0Labels permutation50 permutation5
    mixedMoment B raw31449step1 raw31449step1Labels = mixedMoment B raw31449step2 raw31449step2Labels := by
      have ha : raw31449step2 = -raw31449step1 := by apply Matrix.ext; change ∀ i j, raw31449step2 i j = -(raw31449step1 i j); unfold raw31449step2 raw31449step1; decide +kernel
      have hl : raw31449step2Labels = raw31449step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31449step2 raw31449step2Labels = mixedMoment B raw31449step3 raw31449step3Labels := by
      have ha : raw31449step3 = raw31449step2 := by apply Matrix.ext; unfold raw31449step3 raw31449step2; decide +kernel
      have hl : raw31449step2Labels = labelEmbedding1 ∘ raw31449step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31449step2 raw31449step2Labels raw31449step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1361 node1361Labels := by rfl

def raw31450 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31450step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw31450step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw31450step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31450 raw31450Labels = mixedMoment B node2948 node2948Labels := by
  calc
    mixedMoment B raw31450 raw31450Labels = mixedMoment B raw31450step0 raw31450step0Labels := by
      have hz : ∀ j, raw31450 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31450step0 = (fun i j => raw31450 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31450step0 raw31450; decide +kernel
      have hl : raw31450step0Labels = raw31450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31450 raw31450Labels permutation434 hz
    mixedMoment B raw31450step0 raw31450step0Labels = mixedMoment B raw31450step1 raw31450step1Labels := by
      have ha : raw31450step1 = (fun i j => raw31450step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31450step1 raw31450step0; decide +kernel
      have hl : raw31450step1Labels = raw31450step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31450step0 raw31450step0Labels permutation121 permutation5
    mixedMoment B raw31450step1 raw31450step1Labels = mixedMoment B raw31450step2 raw31450step2Labels := by
      have ha : raw31450step2 = raw31450step1 := by apply Matrix.ext; unfold raw31450step2 raw31450step1; decide +kernel
      have hl : raw31450step1Labels = labelEmbedding1 ∘ raw31450step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31450step1 raw31450step1Labels raw31450step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2948 node2948Labels := by rfl

def raw31451 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31451Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw31451step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31451step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw31451step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31451 raw31451Labels = mixedMoment B node2919 node2919Labels := by
  calc
    mixedMoment B raw31451 raw31451Labels = mixedMoment B raw31451step0 raw31451step0Labels := by
      have ha : raw31451step0 = (fun i j => raw31451 (permutation544 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31451step0 raw31451; decide +kernel
      have hl : raw31451step0Labels = raw31451Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31451 raw31451Labels permutation544 permutation5
    mixedMoment B raw31451step0 raw31451step0Labels = mixedMoment B raw31451step1 raw31451step1Labels := by
      have ha : raw31451step1 = raw31451step0 := by apply Matrix.ext; unfold raw31451step1 raw31451step0; decide +kernel
      have hl : raw31451step0Labels = labelEmbedding1 ∘ raw31451step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31451step0 raw31451step0Labels raw31451step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2919 node2919Labels := by rfl

def raw31452 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw31452Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw31452step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw31452step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31452step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw31452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31452 raw31452Labels = mixedMoment B node2929 node2929Labels := by
  calc
    mixedMoment B raw31452 raw31452Labels = mixedMoment B raw31452step0 raw31452step0Labels := by
      have hz : ∀ j, raw31452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31452step0 = (fun i j => raw31452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31452step0 raw31452; decide +kernel
      have hl : raw31452step0Labels = raw31452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31452 raw31452Labels permutation434 hz
    mixedMoment B raw31452step0 raw31452step0Labels = mixedMoment B raw31452step1 raw31452step1Labels := by
      have ha : raw31452step1 = (fun i j => raw31452step0 (permutation119 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31452step1 raw31452step0; decide +kernel
      have hl : raw31452step1Labels = raw31452step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31452step0 raw31452step0Labels permutation119 permutation5
    mixedMoment B raw31452step1 raw31452step1Labels = mixedMoment B raw31452step2 raw31452step2Labels := by
      have ha : raw31452step2 = raw31452step1 := by apply Matrix.ext; unfold raw31452step2 raw31452step1; decide +kernel
      have hl : raw31452step1Labels = labelEmbedding1 ∘ raw31452step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31452step1 raw31452step1Labels raw31452step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2929 node2929Labels := by rfl

def raw31453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31453Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31453step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw31453step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw31453step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31453step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw31453step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31453 raw31453Labels = mixedMoment B node1426 node1426Labels := by
  calc
    mixedMoment B raw31453 raw31453Labels = mixedMoment B raw31453step0 raw31453step0Labels := by
      have hz : ∀ j, raw31453 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31453step0 = (fun i j => raw31453 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31453step0 raw31453; decide +kernel
      have hl : raw31453step0Labels = raw31453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31453 raw31453Labels permutation434 hz
    mixedMoment B raw31453step0 raw31453step0Labels = mixedMoment B raw31453step1 raw31453step1Labels := by
      have ha : raw31453step1 = (fun i j => raw31453step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31453step1 raw31453step0; decide +kernel
      have hl : raw31453step1Labels = raw31453step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31453step0 raw31453step0Labels permutation36 permutation5
    mixedMoment B raw31453step1 raw31453step1Labels = mixedMoment B raw31453step2 raw31453step2Labels := by
      have ha : raw31453step2 = -raw31453step1 := by apply Matrix.ext; change ∀ i j, raw31453step2 i j = -(raw31453step1 i j); unfold raw31453step2 raw31453step1; decide +kernel
      have hl : raw31453step2Labels = raw31453step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31453step2 raw31453step2Labels = mixedMoment B raw31453step3 raw31453step3Labels := by
      have ha : raw31453step3 = raw31453step2 := by apply Matrix.ext; unfold raw31453step3 raw31453step2; decide +kernel
      have hl : raw31453step2Labels = labelEmbedding1 ∘ raw31453step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31453step2 raw31453step2Labels raw31453step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1426 node1426Labels := by rfl

def raw31454 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31454Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31454step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw31454step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw31454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31454 raw31454Labels = mixedMoment B node3220 node3220Labels := by
  calc
    mixedMoment B raw31454 raw31454Labels = mixedMoment B raw31454step0 raw31454step0Labels := by
      have hz : ∀ j, raw31454 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31454step0 = (fun i j => raw31454 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31454step0 raw31454; decide +kernel
      have hl : raw31454step0Labels = raw31454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31454 raw31454Labels permutation434 hz
    mixedMoment B raw31454step0 raw31454step0Labels = mixedMoment B raw31454step1 raw31454step1Labels := by
      have ha : raw31454step1 = (fun i j => raw31454step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31454step1 raw31454step0; decide +kernel
      have hl : raw31454step1Labels = raw31454step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31454step0 raw31454step0Labels permutation32 permutation7
    mixedMoment B raw31454step1 raw31454step1Labels = mixedMoment B raw31454step2 raw31454step2Labels := by
      have ha : raw31454step2 = raw31454step1 := by apply Matrix.ext; unfold raw31454step2 raw31454step1; decide +kernel
      have hl : raw31454step1Labels = labelEmbedding1 ∘ raw31454step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31454step1 raw31454step1Labels raw31454step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3220 node3220Labels := by rfl

def raw31455 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31455Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31455step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31455step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31455 raw31455Labels = mixedMoment B node3201 node3201Labels := by
  calc
    mixedMoment B raw31455 raw31455Labels = mixedMoment B raw31455step0 raw31455step0Labels := by
      have ha : raw31455step0 = (fun i j => raw31455 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31455step0 raw31455; decide +kernel
      have hl : raw31455step0Labels = raw31455Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31455 raw31455Labels permutation152 permutation7
    mixedMoment B raw31455step0 raw31455step0Labels = mixedMoment B raw31455step1 raw31455step1Labels := by
      have ha : raw31455step1 = raw31455step0 := by apply Matrix.ext; unfold raw31455step1 raw31455step0; decide +kernel
      have hl : raw31455step0Labels = labelEmbedding1 ∘ raw31455step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31455step0 raw31455step0Labels raw31455step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3201 node3201Labels := by rfl

def raw31456 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31456Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31456step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31456step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31456 raw31456Labels = mixedMoment B node3207 node3207Labels := by
  calc
    mixedMoment B raw31456 raw31456Labels = mixedMoment B raw31456step0 raw31456step0Labels := by
      have hz : ∀ j, raw31456 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31456step0 = (fun i j => raw31456 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31456step0 raw31456; decide +kernel
      have hl : raw31456step0Labels = raw31456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31456 raw31456Labels permutation434 hz
    mixedMoment B raw31456step0 raw31456step0Labels = mixedMoment B raw31456step1 raw31456step1Labels := by
      have ha : raw31456step1 = (fun i j => raw31456step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31456step1 raw31456step0; decide +kernel
      have hl : raw31456step1Labels = raw31456step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31456step0 raw31456step0Labels permutation32 permutation7
    mixedMoment B raw31456step1 raw31456step1Labels = mixedMoment B raw31456step2 raw31456step2Labels := by
      have ha : raw31456step2 = raw31456step1 := by apply Matrix.ext; unfold raw31456step2 raw31456step1; decide +kernel
      have hl : raw31456step1Labels = labelEmbedding1 ∘ raw31456step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31456step1 raw31456step1Labels raw31456step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3207 node3207Labels := by rfl

def raw31457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31457step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31457step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31457step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31457step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31457step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31457step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31457 raw31457Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw31457 raw31457Labels = mixedMoment B raw31457step0 raw31457step0Labels := by
      have hz : ∀ j, raw31457 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31457step0 = (fun i j => raw31457 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31457step0 raw31457; decide +kernel
      have hl : raw31457step0Labels = raw31457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31457 raw31457Labels permutation434 hz
    mixedMoment B raw31457step0 raw31457step0Labels = mixedMoment B raw31457step1 raw31457step1Labels := by
      have ha : raw31457step1 = (fun i j => raw31457step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31457step1 raw31457step0; decide +kernel
      have hl : raw31457step1Labels = raw31457step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31457step0 raw31457step0Labels permutation32 permutation7
    mixedMoment B raw31457step1 raw31457step1Labels = mixedMoment B raw31457step2 raw31457step2Labels := by
      have ha : raw31457step2 = -raw31457step1 := by apply Matrix.ext; change ∀ i j, raw31457step2 i j = -(raw31457step1 i j); unfold raw31457step2 raw31457step1; decide +kernel
      have hl : raw31457step2Labels = raw31457step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31457step2 raw31457step2Labels = mixedMoment B raw31457step3 raw31457step3Labels := by
      have ha : raw31457step3 = raw31457step2 := by apply Matrix.ext; unfold raw31457step3 raw31457step2; decide +kernel
      have hl : raw31457step2Labels = labelEmbedding10 ∘ raw31457step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31457step2 raw31457step2Labels raw31457step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5236 node5236Labels := by rfl

def raw31458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31458step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31458step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31458step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31458step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31458step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31458step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31458 raw31458Labels = mixedMoment B node5269 node5269Labels := by
  calc
    mixedMoment B raw31458 raw31458Labels = mixedMoment B raw31458step0 raw31458step0Labels := by
      have hz : ∀ j, raw31458 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31458step0 = (fun i j => raw31458 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31458step0 raw31458; decide +kernel
      have hl : raw31458step0Labels = raw31458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31458 raw31458Labels permutation434 hz
    mixedMoment B raw31458step0 raw31458step0Labels = mixedMoment B raw31458step1 raw31458step1Labels := by
      have ha : raw31458step1 = (fun i j => raw31458step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31458step1 raw31458step0; decide +kernel
      have hl : raw31458step1Labels = raw31458step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31458step0 raw31458step0Labels permutation32 permutation7
    mixedMoment B raw31458step1 raw31458step1Labels = mixedMoment B raw31458step2 raw31458step2Labels := by
      have ha : raw31458step2 = -raw31458step1 := by apply Matrix.ext; change ∀ i j, raw31458step2 i j = -(raw31458step1 i j); unfold raw31458step2 raw31458step1; decide +kernel
      have hl : raw31458step2Labels = raw31458step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31458step2 raw31458step2Labels = mixedMoment B raw31458step3 raw31458step3Labels := by
      have ha : raw31458step3 = raw31458step2 := by apply Matrix.ext; unfold raw31458step3 raw31458step2; decide +kernel
      have hl : raw31458step2Labels = labelEmbedding10 ∘ raw31458step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31458step2 raw31458step2Labels raw31458step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5269 node5269Labels := by rfl

def raw31459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31459step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31459step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31459step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31459step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31459 raw31459Labels = mixedMoment B node5246 node5246Labels := by
  calc
    mixedMoment B raw31459 raw31459Labels = mixedMoment B raw31459step0 raw31459step0Labels := by
      have ha : raw31459step0 = (fun i j => raw31459 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31459step0 raw31459; decide +kernel
      have hl : raw31459step0Labels = raw31459Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31459 raw31459Labels permutation158 permutation7
    mixedMoment B raw31459step0 raw31459step0Labels = mixedMoment B raw31459step1 raw31459step1Labels := by
      have ha : raw31459step1 = -raw31459step0 := by apply Matrix.ext; change ∀ i j, raw31459step1 i j = -(raw31459step0 i j); unfold raw31459step1 raw31459step0; decide +kernel
      have hl : raw31459step1Labels = raw31459step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31459step1 raw31459step1Labels = mixedMoment B raw31459step2 raw31459step2Labels := by
      have ha : raw31459step2 = raw31459step1 := by apply Matrix.ext; unfold raw31459step2 raw31459step1; decide +kernel
      have hl : raw31459step1Labels = labelEmbedding10 ∘ raw31459step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31459step1 raw31459step1Labels raw31459step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5246 node5246Labels := by rfl

def raw31460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31460step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw31460step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31460step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31460step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31460step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31460 raw31460Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw31460 raw31460Labels = mixedMoment B raw31460step0 raw31460step0Labels := by
      have hz : ∀ j, raw31460 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31460step0 = (fun i j => raw31460 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31460step0 raw31460; decide +kernel
      have hl : raw31460step0Labels = raw31460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31460 raw31460Labels permutation434 hz
    mixedMoment B raw31460step0 raw31460step0Labels = mixedMoment B raw31460step1 raw31460step1Labels := by
      have ha : raw31460step1 = (fun i j => raw31460step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31460step1 raw31460step0; decide +kernel
      have hl : raw31460step1Labels = raw31460step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31460step0 raw31460step0Labels permutation32 permutation7
    mixedMoment B raw31460step1 raw31460step1Labels = mixedMoment B raw31460step2 raw31460step2Labels := by
      have ha : raw31460step2 = -raw31460step1 := by apply Matrix.ext; change ∀ i j, raw31460step2 i j = -(raw31460step1 i j); unfold raw31460step2 raw31460step1; decide +kernel
      have hl : raw31460step2Labels = raw31460step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31460step2 raw31460step2Labels = mixedMoment B raw31460step3 raw31460step3Labels := by
      have ha : raw31460step3 = raw31460step2 := by apply Matrix.ext; unfold raw31460step3 raw31460step2; decide +kernel
      have hl : raw31460step2Labels = labelEmbedding10 ∘ raw31460step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31460step2 raw31460step2Labels raw31460step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw31461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31461step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw31461step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31461step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31461step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31461step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31461step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31461 raw31461Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw31461 raw31461Labels = mixedMoment B raw31461step0 raw31461step0Labels := by
      have hz : ∀ j, raw31461 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31461step0 = (fun i j => raw31461 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31461step0 raw31461; decide +kernel
      have hl : raw31461step0Labels = raw31461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31461 raw31461Labels permutation434 hz
    mixedMoment B raw31461step0 raw31461step0Labels = mixedMoment B raw31461step1 raw31461step1Labels := by
      have ha : raw31461step1 = (fun i j => raw31461step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31461step1 raw31461step0; decide +kernel
      have hl : raw31461step1Labels = raw31461step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31461step0 raw31461step0Labels permutation33 permutation7
    mixedMoment B raw31461step1 raw31461step1Labels = mixedMoment B raw31461step2 raw31461step2Labels := by
      have ha : raw31461step2 = -raw31461step1 := by apply Matrix.ext; change ∀ i j, raw31461step2 i j = -(raw31461step1 i j); unfold raw31461step2 raw31461step1; decide +kernel
      have hl : raw31461step2Labels = raw31461step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31461step2 raw31461step2Labels = mixedMoment B raw31461step3 raw31461step3Labels := by
      have ha : raw31461step3 = raw31461step2 := by apply Matrix.ext; unfold raw31461step3 raw31461step2; decide +kernel
      have hl : raw31461step2Labels = labelEmbedding10 ∘ raw31461step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31461step2 raw31461step2Labels raw31461step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw31462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31462step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31462step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31462step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31462 raw31462Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw31462 raw31462Labels = mixedMoment B raw31462step0 raw31462step0Labels := by
      have hz : ∀ j, raw31462 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31462step0 = (fun i j => raw31462 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31462step0 raw31462; decide +kernel
      have hl : raw31462step0Labels = raw31462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31462 raw31462Labels permutation434 hz
    mixedMoment B raw31462step0 raw31462step0Labels = mixedMoment B raw31462step1 raw31462step1Labels := by
      have hz : ∀ j, raw31462step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31462step1 = (fun i j => raw31462step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31462step1 raw31462step0; decide +kernel
      have hl : raw31462step1Labels = raw31462step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31462step0 raw31462step0Labels permutation56 hz
    _ = mixedMoment B node4467 node4467Labels := by rfl

def raw31463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31463step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31463step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31463step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31463 raw31463Labels = mixedMoment B node4875 node4875Labels := by
  calc
    mixedMoment B raw31463 raw31463Labels = mixedMoment B raw31463step0 raw31463step0Labels := by
      have hz : ∀ j, raw31463 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31463step0 = (fun i j => raw31463 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31463step0 raw31463; decide +kernel
      have hl : raw31463step0Labels = raw31463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31463 raw31463Labels permutation434 hz
    mixedMoment B raw31463step0 raw31463step0Labels = mixedMoment B raw31463step1 raw31463step1Labels := by
      have hz : ∀ j, raw31463step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31463step1 = (fun i j => raw31463step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31463step1 raw31463step0; decide +kernel
      have hl : raw31463step1Labels = raw31463step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31463step0 raw31463step0Labels permutation56 hz
    _ = mixedMoment B node4875 node4875Labels := by rfl

def raw31464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31464step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31464step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31464 raw31464Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw31464 raw31464Labels = mixedMoment B raw31464step0 raw31464step0Labels := by
      have hz : ∀ j, raw31464 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw31464step0 = (fun i j => raw31464 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw31464step0 raw31464; decide +kernel
      have hl : raw31464step0Labels = raw31464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31464 raw31464Labels permutation265 hz
    mixedMoment B raw31464step0 raw31464step0Labels = mixedMoment B raw31464step1 raw31464step1Labels := by
      have ha : raw31464step1 = (fun i j => raw31464step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31464step1 raw31464step0; decide +kernel
      have hl : raw31464step1Labels = raw31464step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31464step0 raw31464step0Labels permutation38 permutation2
    _ = mixedMoment B node4811 node4811Labels := by rfl

def raw31465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31465step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31465step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31465step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31465 raw31465Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw31465 raw31465Labels = mixedMoment B raw31465step0 raw31465step0Labels := by
      have hz : ∀ j, raw31465 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31465step0 = (fun i j => raw31465 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31465step0 raw31465; decide +kernel
      have hl : raw31465step0Labels = raw31465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31465 raw31465Labels permutation434 hz
    mixedMoment B raw31465step0 raw31465step0Labels = mixedMoment B raw31465step1 raw31465step1Labels := by
      have hz : ∀ j, raw31465step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31465step1 = (fun i j => raw31465step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31465step1 raw31465step0; decide +kernel
      have hl : raw31465step1Labels = raw31465step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31465step0 raw31465step0Labels permutation56 hz
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw31466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31466step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31466step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31466step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31466step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31466step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31466 raw31466Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw31466 raw31466Labels = mixedMoment B raw31466step0 raw31466step0Labels := by
      have hz : ∀ j, raw31466 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31466step0 = (fun i j => raw31466 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31466step0 raw31466; decide +kernel
      have hl : raw31466step0Labels = raw31466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31466 raw31466Labels permutation434 hz
    mixedMoment B raw31466step0 raw31466step0Labels = mixedMoment B raw31466step1 raw31466step1Labels := by
      have hz : ∀ j, raw31466step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31466step1 = (fun i j => raw31466step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31466step1 raw31466step0; decide +kernel
      have hl : raw31466step1Labels = raw31466step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31466step0 raw31466step0Labels permutation56 hz
    mixedMoment B raw31466step1 raw31466step1Labels = mixedMoment B raw31466step2 raw31466step2Labels := by
      have ha : raw31466step2 = (fun i j => raw31466step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31466step2 raw31466step1; decide +kernel
      have hl : raw31466step2Labels = raw31466step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31466step1 raw31466step1Labels permutation9 permutation2
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw31467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31467 raw31467Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw31467 raw31467Labels = mixedMoment B raw31467step0 raw31467step0Labels := by
      have hz : ∀ j, raw31467 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31467step0 = (fun i j => raw31467 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31467step0 raw31467; decide +kernel
      have hl : raw31467step0Labels = raw31467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31467 raw31467Labels permutation434 hz
    _ = mixedMoment B node4355 node4355Labels := by rfl

def raw31468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31468 raw31468Labels = mixedMoment B node4689 node4689Labels := by
  calc
    mixedMoment B raw31468 raw31468Labels = mixedMoment B raw31468step0 raw31468step0Labels := by
      have hz : ∀ j, raw31468 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31468step0 = (fun i j => raw31468 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31468step0 raw31468; decide +kernel
      have hl : raw31468step0Labels = raw31468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31468 raw31468Labels permutation434 hz
    _ = mixedMoment B node4689 node4689Labels := by rfl

def raw31469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31469 raw31469Labels = mixedMoment B node4767 node4767Labels := by
  calc
    mixedMoment B raw31469 raw31469Labels = mixedMoment B raw31469step0 raw31469step0Labels := by
      have ha : raw31469step0 = (fun i j => raw31469 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31469step0 raw31469; decide +kernel
      have hl : raw31469step0Labels = raw31469Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31469 raw31469Labels permutation158 permutation2
    _ = mixedMoment B node4767 node4767Labels := by rfl

def raw31470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31470 raw31470Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw31470 raw31470Labels = mixedMoment B raw31470step0 raw31470step0Labels := by
      have hz : ∀ j, raw31470 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31470step0 = (fun i j => raw31470 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31470step0 raw31470; decide +kernel
      have hl : raw31470step0Labels = raw31470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31470 raw31470Labels permutation434 hz
    _ = mixedMoment B node4838 node4838Labels := by rfl

def raw31471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31471 raw31471Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw31471 raw31471Labels = mixedMoment B raw31471step0 raw31471step0Labels := by
      have hz : ∀ j, raw31471 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31471step0 = (fun i j => raw31471 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31471step0 raw31471; decide +kernel
      have hl : raw31471step0Labels = raw31471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31471 raw31471Labels permutation434 hz
    mixedMoment B raw31471step0 raw31471step0Labels = mixedMoment B raw31471step1 raw31471step1Labels := by
      have ha : raw31471step1 = (fun i j => raw31471step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31471step1 raw31471step0; decide +kernel
      have hl : raw31471step1Labels = raw31471step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31471step0 raw31471step0Labels permutation33 permutation2
    _ = mixedMoment B node4838 node4838Labels := by rfl

def raw31472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31472 raw31472Labels = mixedMoment B node4329 node4329Labels := by
  calc
    _ = mixedMoment B node4329 node4329Labels := by rfl

def raw31473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31473 raw31473Labels = mixedMoment B node4666 node4666Labels := by
  calc
    _ = mixedMoment B node4666 node4666Labels := by rfl

def raw31474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31474 raw31474Labels = mixedMoment B node4774 node4774Labels := by
  calc
    _ = mixedMoment B node4774 node4774Labels := by rfl

def raw31475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31475 raw31475Labels = mixedMoment B node4802 node4802Labels := by
  calc
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw31476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31476 raw31476Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw31476 raw31476Labels = mixedMoment B raw31476step0 raw31476step0Labels := by
      have ha : raw31476step0 = (fun i j => raw31476 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31476step0 raw31476; decide +kernel
      have hl : raw31476step0Labels = raw31476Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31476 raw31476Labels permutation153 permutation2
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw31477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31477step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31477 raw31477Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw31477 raw31477Labels = mixedMoment B raw31477step0 raw31477step0Labels := by
      have hz : ∀ j, raw31477 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31477step0 = (fun i j => raw31477 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31477step0 raw31477; decide +kernel
      have hl : raw31477step0Labels = raw31477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31477 raw31477Labels permutation434 hz
    mixedMoment B raw31477step0 raw31477step0Labels = mixedMoment B raw31477step1 raw31477step1Labels := by
      have ha : raw31477step1 = (fun i j => raw31477step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31477step1 raw31477step0; decide +kernel
      have hl : raw31477step1Labels = raw31477step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31477step0 raw31477step0Labels permutation33 permutation2
    _ = mixedMoment B node4335 node4335Labels := by rfl

def raw31478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31478 raw31478Labels = mixedMoment B node4670 node4670Labels := by
  calc
    mixedMoment B raw31478 raw31478Labels = mixedMoment B raw31478step0 raw31478step0Labels := by
      have hz : ∀ j, raw31478 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31478step0 = (fun i j => raw31478 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31478step0 raw31478; decide +kernel
      have hl : raw31478step0Labels = raw31478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31478 raw31478Labels permutation434 hz
    mixedMoment B raw31478step0 raw31478step0Labels = mixedMoment B raw31478step1 raw31478step1Labels := by
      have ha : raw31478step1 = (fun i j => raw31478step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31478step1 raw31478step0; decide +kernel
      have hl : raw31478step1Labels = raw31478step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31478step0 raw31478step0Labels permutation33 permutation2
    _ = mixedMoment B node4670 node4670Labels := by rfl

def raw31479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31479 raw31479Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw31479 raw31479Labels = mixedMoment B raw31479step0 raw31479step0Labels := by
      have hz : ∀ j, raw31479 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31479step0 = (fun i j => raw31479 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31479step0 raw31479; decide +kernel
      have hl : raw31479step0Labels = raw31479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31479 raw31479Labels permutation434 hz
    mixedMoment B raw31479step0 raw31479step0Labels = mixedMoment B raw31479step1 raw31479step1Labels := by
      have ha : raw31479step1 = (fun i j => raw31479step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31479step1 raw31479step0; decide +kernel
      have hl : raw31479step1Labels = raw31479step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31479step0 raw31479step0Labels permutation33 permutation2
    _ = mixedMoment B node4777 node4777Labels := by rfl

def raw31480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31480 raw31480Labels = mixedMoment B node4757 node4757Labels := by
  calc
    mixedMoment B raw31480 raw31480Labels = mixedMoment B raw31480step0 raw31480step0Labels := by
      have ha : raw31480step0 = (fun i j => raw31480 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31480step0 raw31480; decide +kernel
      have hl : raw31480step0Labels = raw31480Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31480 raw31480Labels permutation159 permutation2
    _ = mixedMoment B node4757 node4757Labels := by rfl

def raw31481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1], ![1, 0, -1]]
def raw31481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31481 raw31481Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw31481 raw31481Labels = mixedMoment B raw31481step0 raw31481step0Labels := by
      have hz : ∀ j, raw31481 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31481step0 = (fun i j => raw31481 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31481step0 raw31481; decide +kernel
      have hl : raw31481step0Labels = raw31481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31481 raw31481Labels permutation434 hz
    mixedMoment B raw31481step0 raw31481step0Labels = mixedMoment B raw31481step1 raw31481step1Labels := by
      have ha : raw31481step1 = (fun i j => raw31481step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31481step1 raw31481step0; decide +kernel
      have hl : raw31481step1Labels = raw31481step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31481step0 raw31481step0Labels permutation33 permutation2
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw31482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31482 raw31482Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw31482 raw31482Labels = mixedMoment B raw31482step0 raw31482step0Labels := by
      have hz : ∀ j, raw31482 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31482step0 = (fun i j => raw31482 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31482step0 raw31482; decide +kernel
      have hl : raw31482step0Labels = raw31482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31482 raw31482Labels permutation434 hz
    _ = mixedMoment B node4335 node4335Labels := by rfl

def raw31483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31483 raw31483Labels = mixedMoment B node4670 node4670Labels := by
  calc
    mixedMoment B raw31483 raw31483Labels = mixedMoment B raw31483step0 raw31483step0Labels := by
      have hz : ∀ j, raw31483 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31483step0 = (fun i j => raw31483 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31483step0 raw31483; decide +kernel
      have hl : raw31483step0Labels = raw31483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31483 raw31483Labels permutation434 hz
    _ = mixedMoment B node4670 node4670Labels := by rfl

def raw31484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31484 raw31484Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw31484 raw31484Labels = mixedMoment B raw31484step0 raw31484step0Labels := by
      have hz : ∀ j, raw31484 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31484step0 = (fun i j => raw31484 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31484step0 raw31484; decide +kernel
      have hl : raw31484step0Labels = raw31484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31484 raw31484Labels permutation434 hz
    _ = mixedMoment B node4777 node4777Labels := by rfl

def raw31485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31485 raw31485Labels = mixedMoment B node4757 node4757Labels := by
  calc
    mixedMoment B raw31485 raw31485Labels = mixedMoment B raw31485step0 raw31485step0Labels := by
      have ha : raw31485step0 = (fun i j => raw31485 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31485step0 raw31485; decide +kernel
      have hl : raw31485step0Labels = raw31485Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31485 raw31485Labels permutation158 permutation2
    _ = mixedMoment B node4757 node4757Labels := by rfl

def raw31486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw31486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31486step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31486 raw31486Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw31486 raw31486Labels = mixedMoment B raw31486step0 raw31486step0Labels := by
      have hz : ∀ j, raw31486 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31486step0 = (fun i j => raw31486 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31486step0 raw31486; decide +kernel
      have hl : raw31486step0Labels = raw31486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31486 raw31486Labels permutation434 hz
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw31487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 2, -1], ![-1, 0, 1]]
def raw31487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw31487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31487 raw31487Labels = mixedMoment B node3115 node3115Labels := by
  calc
    mixedMoment B raw31487 raw31487Labels = mixedMoment B raw31487step0 raw31487step0Labels := by
      have hz : ∀ j, raw31487 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31487step0 = (fun i j => raw31487 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31487step0 raw31487; decide +kernel
      have hl : raw31487step0Labels = raw31487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31487 raw31487Labels permutation434 hz
    mixedMoment B raw31487step0 raw31487step0Labels = mixedMoment B raw31487step1 raw31487step1Labels := by
      have ha : raw31487step1 = (fun i j => raw31487step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31487step1 raw31487step0; decide +kernel
      have hl : raw31487step1Labels = raw31487step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31487step0 raw31487step0Labels permutation35 permutation6
    mixedMoment B raw31487step1 raw31487step1Labels = mixedMoment B raw31487step2 raw31487step2Labels := by
      have ha : raw31487step2 = -raw31487step1 := by apply Matrix.ext; change ∀ i j, raw31487step2 i j = -(raw31487step1 i j); unfold raw31487step2 raw31487step1; decide +kernel
      have hl : raw31487step2Labels = raw31487step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3115 node3115Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
