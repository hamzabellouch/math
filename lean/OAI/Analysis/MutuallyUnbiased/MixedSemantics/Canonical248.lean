import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw31744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31744 raw31744Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw31744 raw31744Labels = mixedMoment B raw31744step0 raw31744step0Labels := by
      have hz : ∀ j, raw31744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31744step0 = (fun i j => raw31744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31744step0 raw31744; decide +kernel
      have hl : raw31744step0Labels = raw31744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31744 raw31744Labels permutation346 hz
    _ = mixedMoment B node4770 node4770Labels := by rfl

def raw31745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31745step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31745step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31745step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw31745step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31745step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw31745step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31745step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw31745step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31745 raw31745Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw31745 raw31745Labels = mixedMoment B raw31745step0 raw31745step0Labels := by
      have hz : ∀ j, raw31745 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31745step0 = (fun i j => raw31745 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31745step0 raw31745; decide +kernel
      have hl : raw31745step0Labels = raw31745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31745 raw31745Labels permutation434 hz
    mixedMoment B raw31745step0 raw31745step0Labels = mixedMoment B raw31745step1 raw31745step1Labels := by
      have hz : ∀ j, raw31745step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31745step1 = (fun i j => raw31745step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31745step1 raw31745step0; decide +kernel
      have hl : raw31745step1Labels = raw31745step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31745step0 raw31745step0Labels permutation80 hz
    mixedMoment B raw31745step1 raw31745step1Labels = mixedMoment B raw31745step2 raw31745step2Labels := by
      have ha : raw31745step2 = (fun i j => raw31745step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31745step2 raw31745step1; decide +kernel
      have hl : raw31745step2Labels = raw31745step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31745step1 raw31745step1Labels permutation9 permutation7
    mixedMoment B raw31745step2 raw31745step2Labels = mixedMoment B raw31745step3 raw31745step3Labels := by
      have ha : raw31745step3 = -raw31745step2 := by apply Matrix.ext; change ∀ i j, raw31745step3 i j = -(raw31745step2 i j); unfold raw31745step3 raw31745step2; decide +kernel
      have hl : raw31745step3Labels = raw31745step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31745step3 raw31745step3Labels = mixedMoment B raw31745step4 raw31745step4Labels := by
      have ha : raw31745step4 = raw31745step3 := by apply Matrix.ext; unfold raw31745step4 raw31745step3; decide +kernel
      have hl : raw31745step3Labels = labelEmbedding1 ∘ raw31745step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31745step3 raw31745step3Labels raw31745step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2686 node2686Labels := by rfl

def raw31746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31746step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31746step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31746step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31746step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31746 raw31746Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw31746 raw31746Labels = mixedMoment B raw31746step0 raw31746step0Labels := by
      have hz : ∀ j, raw31746 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31746step0 = (fun i j => raw31746 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31746step0 raw31746; decide +kernel
      have hl : raw31746step0Labels = raw31746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31746 raw31746Labels permutation434 hz
    mixedMoment B raw31746step0 raw31746step0Labels = mixedMoment B raw31746step1 raw31746step1Labels := by
      have ha : raw31746step1 = (fun i j => raw31746step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31746step1 raw31746step0; decide +kernel
      have hl : raw31746step1Labels = raw31746step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31746step0 raw31746step0Labels permutation33 permutation7
    mixedMoment B raw31746step1 raw31746step1Labels = mixedMoment B raw31746step2 raw31746step2Labels := by
      have ha : raw31746step2 = -raw31746step1 := by apply Matrix.ext; change ∀ i j, raw31746step2 i j = -(raw31746step1 i j); unfold raw31746step2 raw31746step1; decide +kernel
      have hl : raw31746step2Labels = raw31746step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31746step2 raw31746step2Labels = mixedMoment B raw31746step3 raw31746step3Labels := by
      have ha : raw31746step3 = raw31746step2 := by apply Matrix.ext; unfold raw31746step3 raw31746step2; decide +kernel
      have hl : raw31746step2Labels = labelEmbedding1 ∘ raw31746step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31746step2 raw31746step2Labels raw31746step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2705 node2705Labels := by rfl

def raw31747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31747step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31747step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31747step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31747step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31747step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31747 raw31747Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw31747 raw31747Labels = mixedMoment B raw31747step0 raw31747step0Labels := by
      have hz : ∀ j, raw31747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31747step0 = (fun i j => raw31747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31747step0 raw31747; decide +kernel
      have hl : raw31747step0Labels = raw31747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31747 raw31747Labels permutation346 hz
    mixedMoment B raw31747step0 raw31747step0Labels = mixedMoment B raw31747step1 raw31747step1Labels := by
      have ha : raw31747step1 = (fun i j => raw31747step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31747step1 raw31747step0; decide +kernel
      have hl : raw31747step1Labels = raw31747step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31747step0 raw31747step0Labels permutation33 permutation7
    mixedMoment B raw31747step1 raw31747step1Labels = mixedMoment B raw31747step2 raw31747step2Labels := by
      have ha : raw31747step2 = -raw31747step1 := by apply Matrix.ext; change ∀ i j, raw31747step2 i j = -(raw31747step1 i j); unfold raw31747step2 raw31747step1; decide +kernel
      have hl : raw31747step2Labels = raw31747step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31747step2 raw31747step2Labels = mixedMoment B raw31747step3 raw31747step3Labels := by
      have ha : raw31747step3 = raw31747step2 := by apply Matrix.ext; unfold raw31747step3 raw31747step2; decide +kernel
      have hl : raw31747step2Labels = labelEmbedding1 ∘ raw31747step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31747step2 raw31747step2Labels raw31747step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2705 node2705Labels := by rfl

def raw31748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31748step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31748step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31748step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw31748step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31748step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw31748step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31748step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw31748step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31748 raw31748Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw31748 raw31748Labels = mixedMoment B raw31748step0 raw31748step0Labels := by
      have hz : ∀ j, raw31748 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31748step0 = (fun i j => raw31748 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31748step0 raw31748; decide +kernel
      have hl : raw31748step0Labels = raw31748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31748 raw31748Labels permutation434 hz
    mixedMoment B raw31748step0 raw31748step0Labels = mixedMoment B raw31748step1 raw31748step1Labels := by
      have hz : ∀ j, raw31748step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31748step1 = (fun i j => raw31748step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31748step1 raw31748step0; decide +kernel
      have hl : raw31748step1Labels = raw31748step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31748step0 raw31748step0Labels permutation80 hz
    mixedMoment B raw31748step1 raw31748step1Labels = mixedMoment B raw31748step2 raw31748step2Labels := by
      have ha : raw31748step2 = (fun i j => raw31748step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31748step2 raw31748step1; decide +kernel
      have hl : raw31748step2Labels = raw31748step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31748step1 raw31748step1Labels permutation9 permutation7
    mixedMoment B raw31748step2 raw31748step2Labels = mixedMoment B raw31748step3 raw31748step3Labels := by
      have ha : raw31748step3 = -raw31748step2 := by apply Matrix.ext; change ∀ i j, raw31748step3 i j = -(raw31748step2 i j); unfold raw31748step3 raw31748step2; decide +kernel
      have hl : raw31748step3Labels = raw31748step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31748step3 raw31748step3Labels = mixedMoment B raw31748step4 raw31748step4Labels := by
      have ha : raw31748step4 = raw31748step3 := by apply Matrix.ext; unfold raw31748step4 raw31748step3; decide +kernel
      have hl : raw31748step3Labels = labelEmbedding1 ∘ raw31748step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31748step3 raw31748step3Labels raw31748step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw31749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31749step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31749step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31749step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31749step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31749step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31749step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31749step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31749step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31749 raw31749Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw31749 raw31749Labels = mixedMoment B raw31749step0 raw31749step0Labels := by
      have hz : ∀ j, raw31749 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31749step0 = (fun i j => raw31749 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31749step0 raw31749; decide +kernel
      have hl : raw31749step0Labels = raw31749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31749 raw31749Labels permutation434 hz
    mixedMoment B raw31749step0 raw31749step0Labels = mixedMoment B raw31749step1 raw31749step1Labels := by
      have hz : ∀ j, raw31749step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31749step1 = (fun i j => raw31749step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31749step1 raw31749step0; decide +kernel
      have hl : raw31749step1Labels = raw31749step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31749step0 raw31749step0Labels permutation80 hz
    mixedMoment B raw31749step1 raw31749step1Labels = mixedMoment B raw31749step2 raw31749step2Labels := by
      have ha : raw31749step2 = (fun i j => raw31749step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31749step2 raw31749step1; decide +kernel
      have hl : raw31749step2Labels = raw31749step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31749step1 raw31749step1Labels permutation9 permutation7
    mixedMoment B raw31749step2 raw31749step2Labels = mixedMoment B raw31749step3 raw31749step3Labels := by
      have ha : raw31749step3 = -raw31749step2 := by apply Matrix.ext; change ∀ i j, raw31749step3 i j = -(raw31749step2 i j); unfold raw31749step3 raw31749step2; decide +kernel
      have hl : raw31749step3Labels = raw31749step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31749step3 raw31749step3Labels = mixedMoment B raw31749step4 raw31749step4Labels := by
      have ha : raw31749step4 = raw31749step3 := by apply Matrix.ext; unfold raw31749step4 raw31749step3; decide +kernel
      have hl : raw31749step3Labels = labelEmbedding1 ∘ raw31749step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31749step3 raw31749step3Labels raw31749step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

def raw31750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31750Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31750step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31750step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31750step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31750step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31750step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31750 raw31750Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw31750 raw31750Labels = mixedMoment B raw31750step0 raw31750step0Labels := by
      have hz : ∀ j, raw31750 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31750step0 = (fun i j => raw31750 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31750step0 raw31750; decide +kernel
      have hl : raw31750step0Labels = raw31750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31750 raw31750Labels permutation434 hz
    mixedMoment B raw31750step0 raw31750step0Labels = mixedMoment B raw31750step1 raw31750step1Labels := by
      have ha : raw31750step1 = (fun i j => raw31750step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31750step1 raw31750step0; decide +kernel
      have hl : raw31750step1Labels = raw31750step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31750step0 raw31750step0Labels permutation33 permutation7
    mixedMoment B raw31750step1 raw31750step1Labels = mixedMoment B raw31750step2 raw31750step2Labels := by
      have ha : raw31750step2 = -raw31750step1 := by apply Matrix.ext; change ∀ i j, raw31750step2 i j = -(raw31750step1 i j); unfold raw31750step2 raw31750step1; decide +kernel
      have hl : raw31750step2Labels = raw31750step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31750step2 raw31750step2Labels = mixedMoment B raw31750step3 raw31750step3Labels := by
      have ha : raw31750step3 = raw31750step2 := by apply Matrix.ext; unfold raw31750step3 raw31750step2; decide +kernel
      have hl : raw31750step2Labels = labelEmbedding1 ∘ raw31750step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31750step2 raw31750step2Labels raw31750step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2152 node2152Labels := by rfl

def raw31751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31751Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31751step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31751step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31751step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31751 raw31751Labels = mixedMoment B node2174 node2174Labels := by
  calc
    mixedMoment B raw31751 raw31751Labels = mixedMoment B raw31751step0 raw31751step0Labels := by
      have ha : raw31751step0 = (fun i j => raw31751 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31751step0 raw31751; decide +kernel
      have hl : raw31751step0Labels = raw31751Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31751 raw31751Labels permutation159 permutation7
    mixedMoment B raw31751step0 raw31751step0Labels = mixedMoment B raw31751step1 raw31751step1Labels := by
      have ha : raw31751step1 = -raw31751step0 := by apply Matrix.ext; change ∀ i j, raw31751step1 i j = -(raw31751step0 i j); unfold raw31751step1 raw31751step0; decide +kernel
      have hl : raw31751step1Labels = raw31751step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31751step1 raw31751step1Labels = mixedMoment B raw31751step2 raw31751step2Labels := by
      have ha : raw31751step2 = raw31751step1 := by apply Matrix.ext; unfold raw31751step2 raw31751step1; decide +kernel
      have hl : raw31751step1Labels = labelEmbedding1 ∘ raw31751step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31751step1 raw31751step1Labels raw31751step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2174 node2174Labels := by rfl

def raw31752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31752Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31752step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw31752step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31752step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31752step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31752step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31752 raw31752Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw31752 raw31752Labels = mixedMoment B raw31752step0 raw31752step0Labels := by
      have hz : ∀ j, raw31752 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31752step0 = (fun i j => raw31752 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31752step0 raw31752; decide +kernel
      have hl : raw31752step0Labels = raw31752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31752 raw31752Labels permutation434 hz
    mixedMoment B raw31752step0 raw31752step0Labels = mixedMoment B raw31752step1 raw31752step1Labels := by
      have ha : raw31752step1 = (fun i j => raw31752step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31752step1 raw31752step0; decide +kernel
      have hl : raw31752step1Labels = raw31752step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31752step0 raw31752step0Labels permutation33 permutation7
    mixedMoment B raw31752step1 raw31752step1Labels = mixedMoment B raw31752step2 raw31752step2Labels := by
      have ha : raw31752step2 = -raw31752step1 := by apply Matrix.ext; change ∀ i j, raw31752step2 i j = -(raw31752step1 i j); unfold raw31752step2 raw31752step1; decide +kernel
      have hl : raw31752step2Labels = raw31752step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31752step2 raw31752step2Labels = mixedMoment B raw31752step3 raw31752step3Labels := by
      have ha : raw31752step3 = raw31752step2 := by apply Matrix.ext; unfold raw31752step3 raw31752step2; decide +kernel
      have hl : raw31752step2Labels = labelEmbedding1 ∘ raw31752step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31752step2 raw31752step2Labels raw31752step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw31753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31753Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31753step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31753step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw31753step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31753step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw31753step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31753 raw31753Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw31753 raw31753Labels = mixedMoment B raw31753step0 raw31753step0Labels := by
      have hz : ∀ j, raw31753 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31753step0 = (fun i j => raw31753 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31753step0 raw31753; decide +kernel
      have hl : raw31753step0Labels = raw31753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31753 raw31753Labels permutation434 hz
    mixedMoment B raw31753step0 raw31753step0Labels = mixedMoment B raw31753step1 raw31753step1Labels := by
      have ha : raw31753step1 = (fun i j => raw31753step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31753step1 raw31753step0; decide +kernel
      have hl : raw31753step1Labels = raw31753step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31753step0 raw31753step0Labels permutation33 permutation7
    mixedMoment B raw31753step1 raw31753step1Labels = mixedMoment B raw31753step2 raw31753step2Labels := by
      have ha : raw31753step2 = -raw31753step1 := by apply Matrix.ext; change ∀ i j, raw31753step2 i j = -(raw31753step1 i j); unfold raw31753step2 raw31753step1; decide +kernel
      have hl : raw31753step2Labels = raw31753step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31753step2 raw31753step2Labels = mixedMoment B raw31753step3 raw31753step3Labels := by
      have ha : raw31753step3 = raw31753step2 := by apply Matrix.ext; unfold raw31753step3 raw31753step2; decide +kernel
      have hl : raw31753step2Labels = labelEmbedding1 ∘ raw31753step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31753step2 raw31753step2Labels raw31753step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

def raw31754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31754Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31754step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31754step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31754step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31754step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31754step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31754 raw31754Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw31754 raw31754Labels = mixedMoment B raw31754step0 raw31754step0Labels := by
      have hz : ∀ j, raw31754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31754step0 = (fun i j => raw31754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31754step0 raw31754; decide +kernel
      have hl : raw31754step0Labels = raw31754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31754 raw31754Labels permutation346 hz
    mixedMoment B raw31754step0 raw31754step0Labels = mixedMoment B raw31754step1 raw31754step1Labels := by
      have ha : raw31754step1 = (fun i j => raw31754step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31754step1 raw31754step0; decide +kernel
      have hl : raw31754step1Labels = raw31754step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31754step0 raw31754step0Labels permutation33 permutation7
    mixedMoment B raw31754step1 raw31754step1Labels = mixedMoment B raw31754step2 raw31754step2Labels := by
      have ha : raw31754step2 = -raw31754step1 := by apply Matrix.ext; change ∀ i j, raw31754step2 i j = -(raw31754step1 i j); unfold raw31754step2 raw31754step1; decide +kernel
      have hl : raw31754step2Labels = raw31754step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31754step2 raw31754step2Labels = mixedMoment B raw31754step3 raw31754step3Labels := by
      have ha : raw31754step3 = raw31754step2 := by apply Matrix.ext; unfold raw31754step3 raw31754step2; decide +kernel
      have hl : raw31754step2Labels = labelEmbedding1 ∘ raw31754step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31754step2 raw31754step2Labels raw31754step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2152 node2152Labels := by rfl

def raw31755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31755Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31755step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31755step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31755step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31755step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31755 raw31755Labels = mixedMoment B node2174 node2174Labels := by
  calc
    mixedMoment B raw31755 raw31755Labels = mixedMoment B raw31755step0 raw31755step0Labels := by
      have ha : raw31755step0 = (fun i j => raw31755 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31755step0 raw31755; decide +kernel
      have hl : raw31755step0Labels = raw31755Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31755 raw31755Labels permutation153 permutation7
    mixedMoment B raw31755step0 raw31755step0Labels = mixedMoment B raw31755step1 raw31755step1Labels := by
      have ha : raw31755step1 = -raw31755step0 := by apply Matrix.ext; change ∀ i j, raw31755step1 i j = -(raw31755step0 i j); unfold raw31755step1 raw31755step0; decide +kernel
      have hl : raw31755step1Labels = raw31755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31755step1 raw31755step1Labels = mixedMoment B raw31755step2 raw31755step2Labels := by
      have ha : raw31755step2 = raw31755step1 := by apply Matrix.ext; unfold raw31755step2 raw31755step1; decide +kernel
      have hl : raw31755step1Labels = labelEmbedding1 ∘ raw31755step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31755step1 raw31755step1Labels raw31755step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2174 node2174Labels := by rfl

def raw31756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31756Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31756step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw31756step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31756step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31756step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31756step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31756 raw31756Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw31756 raw31756Labels = mixedMoment B raw31756step0 raw31756step0Labels := by
      have hz : ∀ j, raw31756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31756step0 = (fun i j => raw31756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31756step0 raw31756; decide +kernel
      have hl : raw31756step0Labels = raw31756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31756 raw31756Labels permutation346 hz
    mixedMoment B raw31756step0 raw31756step0Labels = mixedMoment B raw31756step1 raw31756step1Labels := by
      have ha : raw31756step1 = (fun i j => raw31756step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31756step1 raw31756step0; decide +kernel
      have hl : raw31756step1Labels = raw31756step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31756step0 raw31756step0Labels permutation33 permutation7
    mixedMoment B raw31756step1 raw31756step1Labels = mixedMoment B raw31756step2 raw31756step2Labels := by
      have ha : raw31756step2 = -raw31756step1 := by apply Matrix.ext; change ∀ i j, raw31756step2 i j = -(raw31756step1 i j); unfold raw31756step2 raw31756step1; decide +kernel
      have hl : raw31756step2Labels = raw31756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31756step2 raw31756step2Labels = mixedMoment B raw31756step3 raw31756step3Labels := by
      have ha : raw31756step3 = raw31756step2 := by apply Matrix.ext; unfold raw31756step3 raw31756step2; decide +kernel
      have hl : raw31756step2Labels = labelEmbedding1 ∘ raw31756step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31756step2 raw31756step2Labels raw31756step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw31757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31757Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31757step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31757step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw31757step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31757step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw31757step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31757 raw31757Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw31757 raw31757Labels = mixedMoment B raw31757step0 raw31757step0Labels := by
      have hz : ∀ j, raw31757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31757step0 = (fun i j => raw31757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31757step0 raw31757; decide +kernel
      have hl : raw31757step0Labels = raw31757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31757 raw31757Labels permutation346 hz
    mixedMoment B raw31757step0 raw31757step0Labels = mixedMoment B raw31757step1 raw31757step1Labels := by
      have ha : raw31757step1 = (fun i j => raw31757step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31757step1 raw31757step0; decide +kernel
      have hl : raw31757step1Labels = raw31757step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31757step0 raw31757step0Labels permutation33 permutation7
    mixedMoment B raw31757step1 raw31757step1Labels = mixedMoment B raw31757step2 raw31757step2Labels := by
      have ha : raw31757step2 = -raw31757step1 := by apply Matrix.ext; change ∀ i j, raw31757step2 i j = -(raw31757step1 i j); unfold raw31757step2 raw31757step1; decide +kernel
      have hl : raw31757step2Labels = raw31757step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31757step2 raw31757step2Labels = mixedMoment B raw31757step3 raw31757step3Labels := by
      have ha : raw31757step3 = raw31757step2 := by apply Matrix.ext; unfold raw31757step3 raw31757step2; decide +kernel
      have hl : raw31757step2Labels = labelEmbedding1 ∘ raw31757step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31757step2 raw31757step2Labels raw31757step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

def raw31758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31758Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31758step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31758step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -1, 2], ![-2, -1, 3]]
def raw31758step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31758step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw31758step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31758step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw31758step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31758 raw31758Labels = mixedMoment B node2168 node2168Labels := by
  calc
    mixedMoment B raw31758 raw31758Labels = mixedMoment B raw31758step0 raw31758step0Labels := by
      have hz : ∀ j, raw31758 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31758step0 = (fun i j => raw31758 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31758step0 raw31758; decide +kernel
      have hl : raw31758step0Labels = raw31758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31758 raw31758Labels permutation434 hz
    mixedMoment B raw31758step0 raw31758step0Labels = mixedMoment B raw31758step1 raw31758step1Labels := by
      have hz : ∀ j, raw31758step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31758step1 = (fun i j => raw31758step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31758step1 raw31758step0; decide +kernel
      have hl : raw31758step1Labels = raw31758step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31758step0 raw31758step0Labels permutation80 hz
    mixedMoment B raw31758step1 raw31758step1Labels = mixedMoment B raw31758step2 raw31758step2Labels := by
      have ha : raw31758step2 = (fun i j => raw31758step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31758step2 raw31758step1; decide +kernel
      have hl : raw31758step2Labels = raw31758step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31758step1 raw31758step1Labels permutation9 permutation7
    mixedMoment B raw31758step2 raw31758step2Labels = mixedMoment B raw31758step3 raw31758step3Labels := by
      have ha : raw31758step3 = -raw31758step2 := by apply Matrix.ext; change ∀ i j, raw31758step3 i j = -(raw31758step2 i j); unfold raw31758step3 raw31758step2; decide +kernel
      have hl : raw31758step3Labels = raw31758step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31758step3 raw31758step3Labels = mixedMoment B raw31758step4 raw31758step4Labels := by
      have ha : raw31758step4 = raw31758step3 := by apply Matrix.ext; unfold raw31758step4 raw31758step3; decide +kernel
      have hl : raw31758step3Labels = labelEmbedding1 ∘ raw31758step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31758step3 raw31758step3Labels raw31758step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2168 node2168Labels := by rfl

def raw31759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31759Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31759step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw31759step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw31759step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31759step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw31759step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31759 raw31759Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw31759 raw31759Labels = mixedMoment B raw31759step0 raw31759step0Labels := by
      have hz : ∀ j, raw31759 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31759step0 = (fun i j => raw31759 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31759step0 raw31759; decide +kernel
      have hl : raw31759step0Labels = raw31759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31759 raw31759Labels permutation434 hz
    mixedMoment B raw31759step0 raw31759step0Labels = mixedMoment B raw31759step1 raw31759step1Labels := by
      have ha : raw31759step1 = (fun i j => raw31759step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31759step1 raw31759step0; decide +kernel
      have hl : raw31759step1Labels = raw31759step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31759step0 raw31759step0Labels permutation33 permutation7
    mixedMoment B raw31759step1 raw31759step1Labels = mixedMoment B raw31759step2 raw31759step2Labels := by
      have ha : raw31759step2 = -raw31759step1 := by apply Matrix.ext; change ∀ i j, raw31759step2 i j = -(raw31759step1 i j); unfold raw31759step2 raw31759step1; decide +kernel
      have hl : raw31759step2Labels = raw31759step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31759step2 raw31759step2Labels = mixedMoment B raw31759step3 raw31759step3Labels := by
      have ha : raw31759step3 = raw31759step2 := by apply Matrix.ext; unfold raw31759step3 raw31759step2; decide +kernel
      have hl : raw31759step2Labels = labelEmbedding1 ∘ raw31759step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31759step2 raw31759step2Labels raw31759step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2185 node2185Labels := by rfl

def raw31760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31760Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31760step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw31760step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31760step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw31760step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31760step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw31760step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31760 raw31760Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw31760 raw31760Labels = mixedMoment B raw31760step0 raw31760step0Labels := by
      have hz : ∀ j, raw31760 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31760step0 = (fun i j => raw31760 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31760step0 raw31760; decide +kernel
      have hl : raw31760step0Labels = raw31760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31760 raw31760Labels permutation346 hz
    mixedMoment B raw31760step0 raw31760step0Labels = mixedMoment B raw31760step1 raw31760step1Labels := by
      have ha : raw31760step1 = (fun i j => raw31760step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31760step1 raw31760step0; decide +kernel
      have hl : raw31760step1Labels = raw31760step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31760step0 raw31760step0Labels permutation33 permutation7
    mixedMoment B raw31760step1 raw31760step1Labels = mixedMoment B raw31760step2 raw31760step2Labels := by
      have ha : raw31760step2 = -raw31760step1 := by apply Matrix.ext; change ∀ i j, raw31760step2 i j = -(raw31760step1 i j); unfold raw31760step2 raw31760step1; decide +kernel
      have hl : raw31760step2Labels = raw31760step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31760step2 raw31760step2Labels = mixedMoment B raw31760step3 raw31760step3Labels := by
      have ha : raw31760step3 = raw31760step2 := by apply Matrix.ext; unfold raw31760step3 raw31760step2; decide +kernel
      have hl : raw31760step2Labels = labelEmbedding1 ∘ raw31760step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31760step2 raw31760step2Labels raw31760step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2185 node2185Labels := by rfl

def raw31761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw31761Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw31761step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![3, -1, -2], ![1, 0, -1]]
def raw31761step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31761step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw31761step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31761step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw31761step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31761step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw31761step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31761 raw31761Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw31761 raw31761Labels = mixedMoment B raw31761step0 raw31761step0Labels := by
      have hz : ∀ j, raw31761 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31761step0 = (fun i j => raw31761 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31761step0 raw31761; decide +kernel
      have hl : raw31761step0Labels = raw31761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31761 raw31761Labels permutation434 hz
    mixedMoment B raw31761step0 raw31761step0Labels = mixedMoment B raw31761step1 raw31761step1Labels := by
      have hz : ∀ j, raw31761step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31761step1 = (fun i j => raw31761step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31761step1 raw31761step0; decide +kernel
      have hl : raw31761step1Labels = raw31761step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31761step0 raw31761step0Labels permutation80 hz
    mixedMoment B raw31761step1 raw31761step1Labels = mixedMoment B raw31761step2 raw31761step2Labels := by
      have ha : raw31761step2 = (fun i j => raw31761step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31761step2 raw31761step1; decide +kernel
      have hl : raw31761step2Labels = raw31761step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31761step1 raw31761step1Labels permutation9 permutation7
    mixedMoment B raw31761step2 raw31761step2Labels = mixedMoment B raw31761step3 raw31761step3Labels := by
      have ha : raw31761step3 = -raw31761step2 := by apply Matrix.ext; change ∀ i j, raw31761step3 i j = -(raw31761step2 i j); unfold raw31761step3 raw31761step2; decide +kernel
      have hl : raw31761step3Labels = raw31761step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31761step3 raw31761step3Labels = mixedMoment B raw31761step4 raw31761step4Labels := by
      have ha : raw31761step4 = raw31761step3 := by apply Matrix.ext; unfold raw31761step4 raw31761step3; decide +kernel
      have hl : raw31761step3Labels = labelEmbedding1 ∘ raw31761step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31761step3 raw31761step3Labels raw31761step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

def raw31762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31762Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31762step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31762step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw31762step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31762step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw31762step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31762step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw31762step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31762 raw31762Labels = mixedMoment B node2169 node2169Labels := by
  calc
    mixedMoment B raw31762 raw31762Labels = mixedMoment B raw31762step0 raw31762step0Labels := by
      have hz : ∀ j, raw31762 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31762step0 = (fun i j => raw31762 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31762step0 raw31762; decide +kernel
      have hl : raw31762step0Labels = raw31762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31762 raw31762Labels permutation434 hz
    mixedMoment B raw31762step0 raw31762step0Labels = mixedMoment B raw31762step1 raw31762step1Labels := by
      have hz : ∀ j, raw31762step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31762step1 = (fun i j => raw31762step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31762step1 raw31762step0; decide +kernel
      have hl : raw31762step1Labels = raw31762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31762step0 raw31762step0Labels permutation80 hz
    mixedMoment B raw31762step1 raw31762step1Labels = mixedMoment B raw31762step2 raw31762step2Labels := by
      have ha : raw31762step2 = (fun i j => raw31762step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31762step2 raw31762step1; decide +kernel
      have hl : raw31762step2Labels = raw31762step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31762step1 raw31762step1Labels permutation9 permutation7
    mixedMoment B raw31762step2 raw31762step2Labels = mixedMoment B raw31762step3 raw31762step3Labels := by
      have ha : raw31762step3 = -raw31762step2 := by apply Matrix.ext; change ∀ i j, raw31762step3 i j = -(raw31762step2 i j); unfold raw31762step3 raw31762step2; decide +kernel
      have hl : raw31762step3Labels = raw31762step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31762step3 raw31762step3Labels = mixedMoment B raw31762step4 raw31762step4Labels := by
      have ha : raw31762step4 = raw31762step3 := by apply Matrix.ext; unfold raw31762step4 raw31762step3; decide +kernel
      have hl : raw31762step3Labels = labelEmbedding1 ∘ raw31762step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31762step3 raw31762step3Labels raw31762step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2169 node2169Labels := by rfl

def raw31763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31763Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31763step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw31763step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw31763step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31763step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw31763step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31763 raw31763Labels = mixedMoment B node2186 node2186Labels := by
  calc
    mixedMoment B raw31763 raw31763Labels = mixedMoment B raw31763step0 raw31763step0Labels := by
      have hz : ∀ j, raw31763 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31763step0 = (fun i j => raw31763 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31763step0 raw31763; decide +kernel
      have hl : raw31763step0Labels = raw31763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31763 raw31763Labels permutation434 hz
    mixedMoment B raw31763step0 raw31763step0Labels = mixedMoment B raw31763step1 raw31763step1Labels := by
      have ha : raw31763step1 = (fun i j => raw31763step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31763step1 raw31763step0; decide +kernel
      have hl : raw31763step1Labels = raw31763step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31763step0 raw31763step0Labels permutation33 permutation7
    mixedMoment B raw31763step1 raw31763step1Labels = mixedMoment B raw31763step2 raw31763step2Labels := by
      have ha : raw31763step2 = -raw31763step1 := by apply Matrix.ext; change ∀ i j, raw31763step2 i j = -(raw31763step1 i j); unfold raw31763step2 raw31763step1; decide +kernel
      have hl : raw31763step2Labels = raw31763step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31763step2 raw31763step2Labels = mixedMoment B raw31763step3 raw31763step3Labels := by
      have ha : raw31763step3 = raw31763step2 := by apply Matrix.ext; unfold raw31763step3 raw31763step2; decide +kernel
      have hl : raw31763step2Labels = labelEmbedding1 ∘ raw31763step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31763step2 raw31763step2Labels raw31763step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2186 node2186Labels := by rfl

def raw31764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31764Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31764step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw31764step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw31764step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31764step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw31764step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31764 raw31764Labels = mixedMoment B node2186 node2186Labels := by
  calc
    mixedMoment B raw31764 raw31764Labels = mixedMoment B raw31764step0 raw31764step0Labels := by
      have hz : ∀ j, raw31764 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31764step0 = (fun i j => raw31764 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31764step0 raw31764; decide +kernel
      have hl : raw31764step0Labels = raw31764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31764 raw31764Labels permutation346 hz
    mixedMoment B raw31764step0 raw31764step0Labels = mixedMoment B raw31764step1 raw31764step1Labels := by
      have ha : raw31764step1 = (fun i j => raw31764step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31764step1 raw31764step0; decide +kernel
      have hl : raw31764step1Labels = raw31764step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31764step0 raw31764step0Labels permutation33 permutation7
    mixedMoment B raw31764step1 raw31764step1Labels = mixedMoment B raw31764step2 raw31764step2Labels := by
      have ha : raw31764step2 = -raw31764step1 := by apply Matrix.ext; change ∀ i j, raw31764step2 i j = -(raw31764step1 i j); unfold raw31764step2 raw31764step1; decide +kernel
      have hl : raw31764step2Labels = raw31764step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31764step2 raw31764step2Labels = mixedMoment B raw31764step3 raw31764step3Labels := by
      have ha : raw31764step3 = raw31764step2 := by apply Matrix.ext; unfold raw31764step3 raw31764step2; decide +kernel
      have hl : raw31764step2Labels = labelEmbedding1 ∘ raw31764step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31764step2 raw31764step2Labels raw31764step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2186 node2186Labels := by rfl

def raw31765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31765step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31765step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31765step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31765 raw31765Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw31765 raw31765Labels = mixedMoment B raw31765step0 raw31765step0Labels := by
      have hz : ∀ j, raw31765 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31765step0 = (fun i j => raw31765 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31765step0 raw31765; decide +kernel
      have hl : raw31765step0Labels = raw31765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31765 raw31765Labels permutation434 hz
    mixedMoment B raw31765step0 raw31765step0Labels = mixedMoment B raw31765step1 raw31765step1Labels := by
      have hz : ∀ j, raw31765step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31765step1 = (fun i j => raw31765step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31765step1 raw31765step0; decide +kernel
      have hl : raw31765step1Labels = raw31765step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31765step0 raw31765step0Labels permutation80 hz
    mixedMoment B raw31765step1 raw31765step1Labels = mixedMoment B raw31765step2 raw31765step2Labels := by
      have ha : raw31765step2 = (fun i j => raw31765step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31765step2 raw31765step1; decide +kernel
      have hl : raw31765step2Labels = raw31765step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31765step1 raw31765step1Labels permutation9 permutation2
    _ = mixedMoment B node3397 node3397Labels := by rfl

def raw31766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31766step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31766step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31766step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31766 raw31766Labels = mixedMoment B node2066 node2066Labels := by
  calc
    mixedMoment B raw31766 raw31766Labels = mixedMoment B raw31766step0 raw31766step0Labels := by
      have hz : ∀ j, raw31766 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31766step0 = (fun i j => raw31766 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31766step0 raw31766; decide +kernel
      have hl : raw31766step0Labels = raw31766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31766 raw31766Labels permutation434 hz
    mixedMoment B raw31766step0 raw31766step0Labels = mixedMoment B raw31766step1 raw31766step1Labels := by
      have hz : ∀ j, raw31766step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31766step1 = (fun i j => raw31766step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31766step1 raw31766step0; decide +kernel
      have hl : raw31766step1Labels = raw31766step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31766step0 raw31766step0Labels permutation80 hz
    mixedMoment B raw31766step1 raw31766step1Labels = mixedMoment B raw31766step2 raw31766step2Labels := by
      have ha : raw31766step2 = (fun i j => raw31766step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31766step2 raw31766step1; decide +kernel
      have hl : raw31766step2Labels = raw31766step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31766step1 raw31766step1Labels permutation9 permutation2
    _ = mixedMoment B node2066 node2066Labels := by rfl

def raw31767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31767Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31767 raw31767Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw31767 raw31767Labels = mixedMoment B raw31767step0 raw31767step0Labels := by
      have hz : ∀ j, raw31767 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31767step0 = (fun i j => raw31767 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31767step0 raw31767; decide +kernel
      have hl : raw31767step0Labels = raw31767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31767 raw31767Labels permutation434 hz
    mixedMoment B raw31767step0 raw31767step0Labels = mixedMoment B raw31767step1 raw31767step1Labels := by
      have ha : raw31767step1 = (fun i j => raw31767step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31767step1 raw31767step0; decide +kernel
      have hl : raw31767step1Labels = raw31767step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31767step0 raw31767step0Labels permutation33 permutation2
    _ = mixedMoment B node1810 node1810Labels := by rfl

def raw31768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31768 raw31768Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw31768 raw31768Labels = mixedMoment B raw31768step0 raw31768step0Labels := by
      have hz : ∀ j, raw31768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31768step0 = (fun i j => raw31768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31768step0 raw31768; decide +kernel
      have hl : raw31768step0Labels = raw31768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31768 raw31768Labels permutation346 hz
    mixedMoment B raw31768step0 raw31768step0Labels = mixedMoment B raw31768step1 raw31768step1Labels := by
      have ha : raw31768step1 = (fun i j => raw31768step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31768step1 raw31768step0; decide +kernel
      have hl : raw31768step1Labels = raw31768step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31768step0 raw31768step0Labels permutation33 permutation2
    _ = mixedMoment B node1810 node1810Labels := by rfl

def raw31769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31769Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31769step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31769step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31769step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31769 raw31769Labels = mixedMoment B node1818 node1818Labels := by
  calc
    mixedMoment B raw31769 raw31769Labels = mixedMoment B raw31769step0 raw31769step0Labels := by
      have hz : ∀ j, raw31769 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31769step0 = (fun i j => raw31769 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31769step0 raw31769; decide +kernel
      have hl : raw31769step0Labels = raw31769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31769 raw31769Labels permutation434 hz
    mixedMoment B raw31769step0 raw31769step0Labels = mixedMoment B raw31769step1 raw31769step1Labels := by
      have hz : ∀ j, raw31769step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31769step1 = (fun i j => raw31769step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31769step1 raw31769step0; decide +kernel
      have hl : raw31769step1Labels = raw31769step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31769step0 raw31769step0Labels permutation80 hz
    mixedMoment B raw31769step1 raw31769step1Labels = mixedMoment B raw31769step2 raw31769step2Labels := by
      have ha : raw31769step2 = (fun i j => raw31769step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31769step2 raw31769step1; decide +kernel
      have hl : raw31769step2Labels = raw31769step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31769step1 raw31769step1Labels permutation9 permutation2
    _ = mixedMoment B node1818 node1818Labels := by rfl

def raw31770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31770Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31770step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31770 raw31770Labels = mixedMoment B node1819 node1819Labels := by
  calc
    mixedMoment B raw31770 raw31770Labels = mixedMoment B raw31770step0 raw31770step0Labels := by
      have hz : ∀ j, raw31770 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31770step0 = (fun i j => raw31770 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31770step0 raw31770; decide +kernel
      have hl : raw31770step0Labels = raw31770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31770 raw31770Labels permutation434 hz
    mixedMoment B raw31770step0 raw31770step0Labels = mixedMoment B raw31770step1 raw31770step1Labels := by
      have hz : ∀ j, raw31770step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31770step1 = (fun i j => raw31770step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31770step1 raw31770step0; decide +kernel
      have hl : raw31770step1Labels = raw31770step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31770step0 raw31770step0Labels permutation80 hz
    _ = mixedMoment B node1819 node1819Labels := by rfl

def raw31771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw31771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw31771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-2, 0, 2], ![-2, 0, 2]]
def raw31771step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw31771step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31771step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw31771step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31771 raw31771Labels = mixedMoment B node5125 node5125Labels := by
  calc
    mixedMoment B raw31771 raw31771Labels = mixedMoment B raw31771step0 raw31771step0Labels := by
      have hz : ∀ j, raw31771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31771step0 = (fun i j => raw31771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31771step0 raw31771; decide +kernel
      have hl : raw31771step0Labels = raw31771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31771 raw31771Labels permutation346 hz
    mixedMoment B raw31771step0 raw31771step0Labels = mixedMoment B raw31771step1 raw31771step1Labels := by
      have ha : raw31771step1 = (fun i j => raw31771step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31771step1 raw31771step0; decide +kernel
      have hl : raw31771step1Labels = raw31771step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31771step0 raw31771step0Labels permutation38 permutation7
    mixedMoment B raw31771step1 raw31771step1Labels = mixedMoment B raw31771step2 raw31771step2Labels := by
      have ha : raw31771step2 = -raw31771step1 := by apply Matrix.ext; change ∀ i j, raw31771step2 i j = -(raw31771step1 i j); unfold raw31771step2 raw31771step1; decide +kernel
      have hl : raw31771step2Labels = raw31771step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31771step2 raw31771step2Labels = mixedMoment B raw31771step3 raw31771step3Labels := by
      have ha : raw31771step3 = raw31771step2 := by apply Matrix.ext; unfold raw31771step3 raw31771step2; decide +kernel
      have hl : raw31771step2Labels = labelEmbedding10 ∘ raw31771step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31771step2 raw31771step2Labels raw31771step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5125 node5125Labels := by rfl

def raw31772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw31772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw31772step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31772step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw31772step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31772step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw31772step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31772 raw31772Labels = mixedMoment B node5126 node5126Labels := by
  calc
    mixedMoment B raw31772 raw31772Labels = mixedMoment B raw31772step0 raw31772step0Labels := by
      have ha : raw31772step0 = (fun i j => raw31772 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31772step0 raw31772; decide +kernel
      have hl : raw31772step0Labels = raw31772Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31772 raw31772Labels permutation200 permutation7
    mixedMoment B raw31772step0 raw31772step0Labels = mixedMoment B raw31772step1 raw31772step1Labels := by
      have ha : raw31772step1 = -raw31772step0 := by apply Matrix.ext; change ∀ i j, raw31772step1 i j = -(raw31772step0 i j); unfold raw31772step1 raw31772step0; decide +kernel
      have hl : raw31772step1Labels = raw31772step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31772step1 raw31772step1Labels = mixedMoment B raw31772step2 raw31772step2Labels := by
      have ha : raw31772step2 = raw31772step1 := by apply Matrix.ext; unfold raw31772step2 raw31772step1; decide +kernel
      have hl : raw31772step1Labels = labelEmbedding10 ∘ raw31772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31772step1 raw31772step1Labels raw31772step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5126 node5126Labels := by rfl

def raw31773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw31773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw31773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw31773step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw31773step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31773step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw31773step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31773 raw31773Labels = mixedMoment B node5063 node5063Labels := by
  calc
    mixedMoment B raw31773 raw31773Labels = mixedMoment B raw31773step0 raw31773step0Labels := by
      have hz : ∀ j, raw31773 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31773step0 = (fun i j => raw31773 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31773step0 raw31773; decide +kernel
      have hl : raw31773step0Labels = raw31773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31773 raw31773Labels permutation346 hz
    mixedMoment B raw31773step0 raw31773step0Labels = mixedMoment B raw31773step1 raw31773step1Labels := by
      have ha : raw31773step1 = (fun i j => raw31773step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31773step1 raw31773step0; decide +kernel
      have hl : raw31773step1Labels = raw31773step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31773step0 raw31773step0Labels permutation38 permutation7
    mixedMoment B raw31773step1 raw31773step1Labels = mixedMoment B raw31773step2 raw31773step2Labels := by
      have ha : raw31773step2 = -raw31773step1 := by apply Matrix.ext; change ∀ i j, raw31773step2 i j = -(raw31773step1 i j); unfold raw31773step2 raw31773step1; decide +kernel
      have hl : raw31773step2Labels = raw31773step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31773step2 raw31773step2Labels = mixedMoment B raw31773step3 raw31773step3Labels := by
      have ha : raw31773step3 = raw31773step2 := by apply Matrix.ext; unfold raw31773step3 raw31773step2; decide +kernel
      have hl : raw31773step2Labels = labelEmbedding10 ∘ raw31773step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31773step2 raw31773step2Labels raw31773step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5063 node5063Labels := by rfl

def raw31774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw31774step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31774step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31774step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31774step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31774 raw31774Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw31774 raw31774Labels = mixedMoment B raw31774step0 raw31774step0Labels := by
      have hz : ∀ j, raw31774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31774step0 = (fun i j => raw31774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31774step0 raw31774; decide +kernel
      have hl : raw31774step0Labels = raw31774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31774 raw31774Labels permutation346 hz
    mixedMoment B raw31774step0 raw31774step0Labels = mixedMoment B raw31774step1 raw31774step1Labels := by
      have ha : raw31774step1 = (fun i j => raw31774step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31774step1 raw31774step0; decide +kernel
      have hl : raw31774step1Labels = raw31774step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31774step0 raw31774step0Labels permutation38 permutation7
    mixedMoment B raw31774step1 raw31774step1Labels = mixedMoment B raw31774step2 raw31774step2Labels := by
      have ha : raw31774step2 = -raw31774step1 := by apply Matrix.ext; change ∀ i j, raw31774step2 i j = -(raw31774step1 i j); unfold raw31774step2 raw31774step1; decide +kernel
      have hl : raw31774step2Labels = raw31774step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31774step2 raw31774step2Labels = mixedMoment B raw31774step3 raw31774step3Labels := by
      have ha : raw31774step3 = raw31774step2 := by apply Matrix.ext; unfold raw31774step3 raw31774step2; decide +kernel
      have hl : raw31774step2Labels = labelEmbedding10 ∘ raw31774step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31774step2 raw31774step2Labels raw31774step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw31775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw31775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw31775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw31775step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31775step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31775step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31775step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31775 raw31775Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw31775 raw31775Labels = mixedMoment B raw31775step0 raw31775step0Labels := by
      have hz : ∀ j, raw31775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31775step0 = (fun i j => raw31775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31775step0 raw31775; decide +kernel
      have hl : raw31775step0Labels = raw31775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31775 raw31775Labels permutation346 hz
    mixedMoment B raw31775step0 raw31775step0Labels = mixedMoment B raw31775step1 raw31775step1Labels := by
      have ha : raw31775step1 = (fun i j => raw31775step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31775step1 raw31775step0; decide +kernel
      have hl : raw31775step1Labels = raw31775step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31775step0 raw31775step0Labels permutation39 permutation7
    mixedMoment B raw31775step1 raw31775step1Labels = mixedMoment B raw31775step2 raw31775step2Labels := by
      have ha : raw31775step2 = -raw31775step1 := by apply Matrix.ext; change ∀ i j, raw31775step2 i j = -(raw31775step1 i j); unfold raw31775step2 raw31775step1; decide +kernel
      have hl : raw31775step2Labels = raw31775step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31775step2 raw31775step2Labels = mixedMoment B raw31775step3 raw31775step3Labels := by
      have ha : raw31775step3 = raw31775step2 := by apply Matrix.ext; unfold raw31775step3 raw31775step2; decide +kernel
      have hl : raw31775step2Labels = labelEmbedding10 ∘ raw31775step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31775step2 raw31775step2Labels raw31775step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw31776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw31776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw31776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw31776step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31776 raw31776Labels = mixedMoment B node4432 node4432Labels := by
  calc
    mixedMoment B raw31776 raw31776Labels = mixedMoment B raw31776step0 raw31776step0Labels := by
      have hz : ∀ j, raw31776 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31776step0 = (fun i j => raw31776 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31776step0 raw31776; decide +kernel
      have hl : raw31776step0Labels = raw31776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31776 raw31776Labels permutation346 hz
    mixedMoment B raw31776step0 raw31776step0Labels = mixedMoment B raw31776step1 raw31776step1Labels := by
      have hz : ∀ j, raw31776step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31776step1 = (fun i j => raw31776step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31776step1 raw31776step0; decide +kernel
      have hl : raw31776step1Labels = raw31776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31776step0 raw31776step0Labels permutation56 hz
    _ = mixedMoment B node4432 node4432Labels := by rfl

def raw31777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw31777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw31777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31777 raw31777Labels = mixedMoment B node4659 node4659Labels := by
  calc
    mixedMoment B raw31777 raw31777Labels = mixedMoment B raw31777step0 raw31777step0Labels := by
      have ha : raw31777step0 = (fun i j => raw31777 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31777step0 raw31777; decide +kernel
      have hl : raw31777step0Labels = raw31777Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31777 raw31777Labels permutation158 permutation2
    _ = mixedMoment B node4659 node4659Labels := by rfl

def raw31778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw31778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw31778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31778 raw31778Labels = mixedMoment B node4711 node4711Labels := by
  calc
    mixedMoment B raw31778 raw31778Labels = mixedMoment B raw31778step0 raw31778step0Labels := by
      have ha : raw31778step0 = (fun i j => raw31778 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31778step0 raw31778; decide +kernel
      have hl : raw31778step0Labels = raw31778Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31778 raw31778Labels permutation200 permutation2
    _ = mixedMoment B node4711 node4711Labels := by rfl

def raw31779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw31779step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31779step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31779step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31779step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31779 raw31779Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw31779 raw31779Labels = mixedMoment B raw31779step0 raw31779step0Labels := by
      have ha : raw31779step0 = (fun i j => raw31779 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31779step0 raw31779; decide +kernel
      have hl : raw31779step0Labels = raw31779Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31779 raw31779Labels permutation200 permutation7
    mixedMoment B raw31779step0 raw31779step0Labels = mixedMoment B raw31779step1 raw31779step1Labels := by
      have ha : raw31779step1 = -raw31779step0 := by apply Matrix.ext; change ∀ i j, raw31779step1 i j = -(raw31779step0 i j); unfold raw31779step1 raw31779step0; decide +kernel
      have hl : raw31779step1Labels = raw31779step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31779step1 raw31779step1Labels = mixedMoment B raw31779step2 raw31779step2Labels := by
      have ha : raw31779step2 = raw31779step1 := by apply Matrix.ext; unfold raw31779step2 raw31779step1; decide +kernel
      have hl : raw31779step1Labels = labelEmbedding10 ∘ raw31779step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31779step1 raw31779step1Labels raw31779step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

def raw31780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw31780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw31780step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31780step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31780step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31780step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31780step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31780 raw31780Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw31780 raw31780Labels = mixedMoment B raw31780step0 raw31780step0Labels := by
      have ha : raw31780step0 = (fun i j => raw31780 (permutation201 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31780step0 raw31780; decide +kernel
      have hl : raw31780step0Labels = raw31780Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31780 raw31780Labels permutation201 permutation7
    mixedMoment B raw31780step0 raw31780step0Labels = mixedMoment B raw31780step1 raw31780step1Labels := by
      have ha : raw31780step1 = -raw31780step0 := by apply Matrix.ext; change ∀ i j, raw31780step1 i j = -(raw31780step0 i j); unfold raw31780step1 raw31780step0; decide +kernel
      have hl : raw31780step1Labels = raw31780step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31780step1 raw31780step1Labels = mixedMoment B raw31780step2 raw31780step2Labels := by
      have ha : raw31780step2 = raw31780step1 := by apply Matrix.ext; unfold raw31780step2 raw31780step1; decide +kernel
      have hl : raw31780step1Labels = labelEmbedding10 ∘ raw31780step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31780step1 raw31780step1Labels raw31780step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

def raw31781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw31781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw31781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31781 raw31781Labels = mixedMoment B node4674 node4674Labels := by
  calc
    mixedMoment B raw31781 raw31781Labels = mixedMoment B raw31781step0 raw31781step0Labels := by
      have hz : ∀ j, raw31781 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31781step0 = (fun i j => raw31781 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31781step0 raw31781; decide +kernel
      have hl : raw31781step0Labels = raw31781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31781 raw31781Labels permutation346 hz
    _ = mixedMoment B node4674 node4674Labels := by rfl

def raw31782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw31782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31782 raw31782Labels = mixedMoment B node4758 node4758Labels := by
  calc
    _ = mixedMoment B node4758 node4758Labels := by rfl

def raw31783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31783 raw31783Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw31783 raw31783Labels = mixedMoment B raw31783step0 raw31783step0Labels := by
      have hz : ∀ j, raw31783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31783step0 = (fun i j => raw31783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31783step0 raw31783; decide +kernel
      have hl : raw31783step0Labels = raw31783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31783 raw31783Labels permutation346 hz
    _ = mixedMoment B node4828 node4828Labels := by rfl

def raw31784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw31784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw31784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31784step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31784 raw31784Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw31784 raw31784Labels = mixedMoment B raw31784step0 raw31784step0Labels := by
      have hz : ∀ j, raw31784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31784step0 = (fun i j => raw31784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31784step0 raw31784; decide +kernel
      have hl : raw31784step0Labels = raw31784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31784 raw31784Labels permutation346 hz
    mixedMoment B raw31784step0 raw31784step0Labels = mixedMoment B raw31784step1 raw31784step1Labels := by
      have ha : raw31784step1 = (fun i j => raw31784step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31784step1 raw31784step0; decide +kernel
      have hl : raw31784step1Labels = raw31784step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31784step0 raw31784step0Labels permutation33 permutation2
    _ = mixedMoment B node4828 node4828Labels := by rfl

def raw31785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw31785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw31785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw31785step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31785 raw31785Labels = mixedMoment B node4662 node4662Labels := by
  calc
    mixedMoment B raw31785 raw31785Labels = mixedMoment B raw31785step0 raw31785step0Labels := by
      have hz : ∀ j, raw31785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31785step0 = (fun i j => raw31785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31785step0 raw31785; decide +kernel
      have hl : raw31785step0Labels = raw31785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31785 raw31785Labels permutation346 hz
    mixedMoment B raw31785step0 raw31785step0Labels = mixedMoment B raw31785step1 raw31785step1Labels := by
      have ha : raw31785step1 = (fun i j => raw31785step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31785step1 raw31785step0; decide +kernel
      have hl : raw31785step1Labels = raw31785step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31785step0 raw31785step0Labels permutation33 permutation2
    _ = mixedMoment B node4662 node4662Labels := by rfl

def raw31786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw31786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw31786step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31786 raw31786Labels = mixedMoment B node4755 node4755Labels := by
  calc
    mixedMoment B raw31786 raw31786Labels = mixedMoment B raw31786step0 raw31786step0Labels := by
      have ha : raw31786step0 = (fun i j => raw31786 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31786step0 raw31786; decide +kernel
      have hl : raw31786step0Labels = raw31786Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31786 raw31786Labels permutation153 permutation2
    _ = mixedMoment B node4755 node4755Labels := by rfl

def raw31787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw31787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw31787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw31787step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31787 raw31787Labels = mixedMoment B node4718 node4718Labels := by
  calc
    mixedMoment B raw31787 raw31787Labels = mixedMoment B raw31787step0 raw31787step0Labels := by
      have hz : ∀ j, raw31787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31787step0 = (fun i j => raw31787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31787step0 raw31787; decide +kernel
      have hl : raw31787step0Labels = raw31787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31787 raw31787Labels permutation346 hz
    mixedMoment B raw31787step0 raw31787step0Labels = mixedMoment B raw31787step1 raw31787step1Labels := by
      have ha : raw31787step1 = (fun i j => raw31787step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31787step1 raw31787step0; decide +kernel
      have hl : raw31787step1Labels = raw31787step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31787step0 raw31787step0Labels permutation39 permutation2
    _ = mixedMoment B node4718 node4718Labels := by rfl

def raw31788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw31788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw31788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw31788step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31788 raw31788Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw31788 raw31788Labels = mixedMoment B raw31788step0 raw31788step0Labels := by
      have hz : ∀ j, raw31788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31788step0 = (fun i j => raw31788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31788step0 raw31788; decide +kernel
      have hl : raw31788step0Labels = raw31788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31788 raw31788Labels permutation346 hz
    mixedMoment B raw31788step0 raw31788step0Labels = mixedMoment B raw31788step1 raw31788step1Labels := by
      have ha : raw31788step1 = (fun i j => raw31788step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31788step1 raw31788step0; decide +kernel
      have hl : raw31788step1Labels = raw31788step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31788step0 raw31788step0Labels permutation33 permutation2
    _ = mixedMoment B node4788 node4788Labels := by rfl

def raw31789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw31789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw31789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31789 raw31789Labels = mixedMoment B node4662 node4662Labels := by
  calc
    mixedMoment B raw31789 raw31789Labels = mixedMoment B raw31789step0 raw31789step0Labels := by
      have hz : ∀ j, raw31789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31789step0 = (fun i j => raw31789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31789step0 raw31789; decide +kernel
      have hl : raw31789step0Labels = raw31789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31789 raw31789Labels permutation346 hz
    _ = mixedMoment B node4662 node4662Labels := by rfl

def raw31790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw31790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31790 raw31790Labels = mixedMoment B node4755 node4755Labels := by
  calc
    _ = mixedMoment B node4755 node4755Labels := by rfl

def raw31791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw31791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw31791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw31791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31791 raw31791Labels = mixedMoment B node4718 node4718Labels := by
  calc
    mixedMoment B raw31791 raw31791Labels = mixedMoment B raw31791step0 raw31791step0Labels := by
      have hz : ∀ j, raw31791 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31791step0 = (fun i j => raw31791 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31791step0 raw31791; decide +kernel
      have hl : raw31791step0Labels = raw31791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31791 raw31791Labels permutation346 hz
    mixedMoment B raw31791step0 raw31791step0Labels = mixedMoment B raw31791step1 raw31791step1Labels := by
      have ha : raw31791step1 = (fun i j => raw31791step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31791step1 raw31791step0; decide +kernel
      have hl : raw31791step1Labels = raw31791step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31791step0 raw31791step0Labels permutation38 permutation2
    _ = mixedMoment B node4718 node4718Labels := by rfl

def raw31792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw31792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw31792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31792 raw31792Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw31792 raw31792Labels = mixedMoment B raw31792step0 raw31792step0Labels := by
      have hz : ∀ j, raw31792 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31792step0 = (fun i j => raw31792 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31792step0 raw31792; decide +kernel
      have hl : raw31792step0Labels = raw31792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31792 raw31792Labels permutation346 hz
    _ = mixedMoment B node4788 node4788Labels := by rfl

def raw31793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31793Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2], ![2, -2, 0]]
def raw31793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31793step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31793 raw31793Labels = mixedMoment B node891 node891Labels := by
  calc
    mixedMoment B raw31793 raw31793Labels = mixedMoment B raw31793step0 raw31793step0Labels := by
      have hz : ∀ j, raw31793 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31793step0 = (fun i j => raw31793 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31793step0 raw31793; decide +kernel
      have hl : raw31793step0Labels = raw31793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31793 raw31793Labels permutation434 hz
    mixedMoment B raw31793step0 raw31793step0Labels = mixedMoment B raw31793step1 raw31793step1Labels := by
      have ha : raw31793step1 = (fun i j => raw31793step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31793step1 raw31793step0; decide +kernel
      have hl : raw31793step1Labels = raw31793step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31793step0 raw31793step0Labels permutation33 permutation2
    _ = mixedMoment B node891 node891Labels := by rfl

def raw31794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31794Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, 0, -2], ![2, -2, 0]]
def raw31794step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31794 raw31794Labels = mixedMoment B node1781 node1781Labels := by
  calc
    mixedMoment B raw31794 raw31794Labels = mixedMoment B raw31794step0 raw31794step0Labels := by
      have hz : ∀ j, raw31794 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31794step0 = (fun i j => raw31794 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31794step0 raw31794; decide +kernel
      have hl : raw31794step0Labels = raw31794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31794 raw31794Labels permutation434 hz
    mixedMoment B raw31794step0 raw31794step0Labels = mixedMoment B raw31794step1 raw31794step1Labels := by
      have ha : raw31794step1 = (fun i j => raw31794step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31794step1 raw31794step0; decide +kernel
      have hl : raw31794step1Labels = raw31794step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31794step0 raw31794step0Labels permutation33 permutation2
    _ = mixedMoment B node1781 node1781Labels := by rfl

def raw31795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31795Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, 0, -2], ![2, -2, 0]]
def raw31795step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31795 raw31795Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw31795 raw31795Labels = mixedMoment B raw31795step0 raw31795step0Labels := by
      have hz : ∀ j, raw31795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31795step0 = (fun i j => raw31795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31795step0 raw31795; decide +kernel
      have hl : raw31795step0Labels = raw31795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31795 raw31795Labels permutation434 hz
    mixedMoment B raw31795step0 raw31795step0Labels = mixedMoment B raw31795step1 raw31795step1Labels := by
      have ha : raw31795step1 = (fun i j => raw31795step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31795step1 raw31795step0; decide +kernel
      have hl : raw31795step1Labels = raw31795step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31795step0 raw31795step0Labels permutation33 permutation2
    _ = mixedMoment B node1928 node1928Labels := by rfl

def raw31796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31796Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31796step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31796 raw31796Labels = mixedMoment B node1870 node1870Labels := by
  calc
    mixedMoment B raw31796 raw31796Labels = mixedMoment B raw31796step0 raw31796step0Labels := by
      have ha : raw31796step0 = (fun i j => raw31796 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31796step0 raw31796; decide +kernel
      have hl : raw31796step0Labels = raw31796Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31796 raw31796Labels permutation159 permutation2
    _ = mixedMoment B node1870 node1870Labels := by rfl

def raw31797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31797Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw31797step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31797 raw31797Labels = mixedMoment B node1949 node1949Labels := by
  calc
    mixedMoment B raw31797 raw31797Labels = mixedMoment B raw31797step0 raw31797step0Labels := by
      have hz : ∀ j, raw31797 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31797step0 = (fun i j => raw31797 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31797step0 raw31797; decide +kernel
      have hl : raw31797step0Labels = raw31797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31797 raw31797Labels permutation434 hz
    _ = mixedMoment B node1949 node1949Labels := by rfl

def raw31798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31798Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2], ![1, -1, 0]]
def raw31798step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31798 raw31798Labels = mixedMoment B node1945 node1945Labels := by
  calc
    mixedMoment B raw31798 raw31798Labels = mixedMoment B raw31798step0 raw31798step0Labels := by
      have hz : ∀ j, raw31798 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31798step0 = (fun i j => raw31798 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31798step0 raw31798; decide +kernel
      have hl : raw31798step0Labels = raw31798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31798 raw31798Labels permutation434 hz
    mixedMoment B raw31798step0 raw31798step0Labels = mixedMoment B raw31798step1 raw31798step1Labels := by
      have ha : raw31798step1 = (fun i j => raw31798step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31798step1 raw31798step0; decide +kernel
      have hl : raw31798step1Labels = raw31798step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31798step0 raw31798step0Labels permutation36 permutation2
    _ = mixedMoment B node1945 node1945Labels := by rfl

def raw31799 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![0, 0], ![2, -2], ![0, 0]]
def raw31799Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31799step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![0, 0], ![2, -2]]
def raw31799step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31799step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw31799step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31799 raw31799Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw31799 raw31799Labels = mixedMoment B raw31799step0 raw31799step0Labels := by
      have hz : ∀ j, raw31799 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw31799step0 = (fun i j => raw31799 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw31799step0 raw31799; decide +kernel
      have hl : raw31799step0Labels = raw31799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31799 raw31799Labels permutation590 hz
    mixedMoment B raw31799step0 raw31799step0Labels = mixedMoment B raw31799step1 raw31799step1Labels := by
      have hz : ∀ j, raw31799step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw31799step1 = (fun i j => raw31799step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw31799step1 raw31799step0; decide +kernel
      have hl : raw31799step1Labels = raw31799step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31799step0 raw31799step0Labels permutation104 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw31800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31800Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31800step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31800 raw31800Labels = mixedMoment B node892 node892Labels := by
  calc
    mixedMoment B raw31800 raw31800Labels = mixedMoment B raw31800step0 raw31800step0Labels := by
      have hz : ∀ j, raw31800 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31800step0 = (fun i j => raw31800 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31800step0 raw31800; decide +kernel
      have hl : raw31800step0Labels = raw31800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31800 raw31800Labels permutation434 hz
    _ = mixedMoment B node892 node892Labels := by rfl

def raw31801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31801Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31801step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31801 raw31801Labels = mixedMoment B node1782 node1782Labels := by
  calc
    mixedMoment B raw31801 raw31801Labels = mixedMoment B raw31801step0 raw31801step0Labels := by
      have hz : ∀ j, raw31801 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31801step0 = (fun i j => raw31801 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31801step0 raw31801; decide +kernel
      have hl : raw31801step0Labels = raw31801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31801 raw31801Labels permutation434 hz
    _ = mixedMoment B node1782 node1782Labels := by rfl

def raw31802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31802Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31802step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31802 raw31802Labels = mixedMoment B node1929 node1929Labels := by
  calc
    mixedMoment B raw31802 raw31802Labels = mixedMoment B raw31802step0 raw31802step0Labels := by
      have hz : ∀ j, raw31802 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31802step0 = (fun i j => raw31802 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31802step0 raw31802; decide +kernel
      have hl : raw31802step0Labels = raw31802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31802 raw31802Labels permutation434 hz
    _ = mixedMoment B node1929 node1929Labels := by rfl

def raw31803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31803Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31803 raw31803Labels = mixedMoment B node1871 node1871Labels := by
  calc
    mixedMoment B raw31803 raw31803Labels = mixedMoment B raw31803step0 raw31803step0Labels := by
      have ha : raw31803step0 = (fun i j => raw31803 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31803step0 raw31803; decide +kernel
      have hl : raw31803step0Labels = raw31803Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31803 raw31803Labels permutation158 permutation2
    _ = mixedMoment B node1871 node1871Labels := by rfl

def raw31804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31804Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw31804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31804 raw31804Labels = mixedMoment B node1947 node1947Labels := by
  calc
    mixedMoment B raw31804 raw31804Labels = mixedMoment B raw31804step0 raw31804step0Labels := by
      have hz : ∀ j, raw31804 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31804step0 = (fun i j => raw31804 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31804step0 raw31804; decide +kernel
      have hl : raw31804step0Labels = raw31804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31804 raw31804Labels permutation434 hz
    mixedMoment B raw31804step0 raw31804step0Labels = mixedMoment B raw31804step1 raw31804step1Labels := by
      have ha : raw31804step1 = (fun i j => raw31804step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31804step1 raw31804step0; decide +kernel
      have hl : raw31804step1Labels = raw31804step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31804step0 raw31804step0Labels permutation34 permutation2
    _ = mixedMoment B node1947 node1947Labels := by rfl

def raw31805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31805Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw31805step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31805 raw31805Labels = mixedMoment B node1947 node1947Labels := by
  calc
    mixedMoment B raw31805 raw31805Labels = mixedMoment B raw31805step0 raw31805step0Labels := by
      have hz : ∀ j, raw31805 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31805step0 = (fun i j => raw31805 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31805step0 raw31805; decide +kernel
      have hl : raw31805step0Labels = raw31805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31805 raw31805Labels permutation434 hz
    mixedMoment B raw31805step0 raw31805step0Labels = mixedMoment B raw31805step1 raw31805step1Labels := by
      have ha : raw31805step1 = (fun i j => raw31805step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31805step1 raw31805step0; decide +kernel
      have hl : raw31805step1Labels = raw31805step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31805step0 raw31805step0Labels permutation36 permutation2
    _ = mixedMoment B node1947 node1947Labels := by rfl

def raw31806 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![0, 0], ![1, -1], ![1, -1]]
def raw31806Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31806step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw31806step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31806step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw31806step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31806 raw31806Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw31806 raw31806Labels = mixedMoment B raw31806step0 raw31806step0Labels := by
      have hz : ∀ j, raw31806 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31806step0 = (fun i j => raw31806 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31806step0 raw31806; decide +kernel
      have hl : raw31806step0Labels = raw31806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31806 raw31806Labels permutation434 hz
    mixedMoment B raw31806step0 raw31806step0Labels = mixedMoment B raw31806step1 raw31806step1Labels := by
      have ha : raw31806step1 = (fun i j => raw31806step0 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31806step1 raw31806step0; decide +kernel
      have hl : raw31806step1Labels = raw31806step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31806step0 raw31806step0Labels permutation35 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw31807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -1, -1]]
def raw31807step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31807step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31807step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31807step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31807step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31807step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31807 raw31807Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw31807 raw31807Labels = mixedMoment B raw31807step0 raw31807step0Labels := by
      have hz : ∀ j, raw31807 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31807step0 = (fun i j => raw31807 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31807step0 raw31807; decide +kernel
      have hl : raw31807step0Labels = raw31807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31807 raw31807Labels permutation434 hz
    mixedMoment B raw31807step0 raw31807step0Labels = mixedMoment B raw31807step1 raw31807step1Labels := by
      have ha : raw31807step1 = (fun i j => raw31807step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31807step1 raw31807step0; decide +kernel
      have hl : raw31807step1Labels = raw31807step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31807step0 raw31807step0Labels permutation33 permutation7
    mixedMoment B raw31807step1 raw31807step1Labels = mixedMoment B raw31807step2 raw31807step2Labels := by
      have ha : raw31807step2 = -raw31807step1 := by apply Matrix.ext; change ∀ i j, raw31807step2 i j = -(raw31807step1 i j); unfold raw31807step2 raw31807step1; decide +kernel
      have hl : raw31807step2Labels = raw31807step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31807step2 raw31807step2Labels = mixedMoment B raw31807step3 raw31807step3Labels := by
      have ha : raw31807step3 = raw31807step2 := by apply Matrix.ext; unfold raw31807step3 raw31807step2; decide +kernel
      have hl : raw31807step2Labels = labelEmbedding10 ∘ raw31807step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31807step2 raw31807step2Labels raw31807step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw31808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -1, -1]]
def raw31808step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31808step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31808step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31808step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31808step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31808 raw31808Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw31808 raw31808Labels = mixedMoment B raw31808step0 raw31808step0Labels := by
      have hz : ∀ j, raw31808 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31808step0 = (fun i j => raw31808 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31808step0 raw31808; decide +kernel
      have hl : raw31808step0Labels = raw31808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31808 raw31808Labels permutation434 hz
    mixedMoment B raw31808step0 raw31808step0Labels = mixedMoment B raw31808step1 raw31808step1Labels := by
      have ha : raw31808step1 = (fun i j => raw31808step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31808step1 raw31808step0; decide +kernel
      have hl : raw31808step1Labels = raw31808step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31808step0 raw31808step0Labels permutation33 permutation7
    mixedMoment B raw31808step1 raw31808step1Labels = mixedMoment B raw31808step2 raw31808step2Labels := by
      have ha : raw31808step2 = -raw31808step1 := by apply Matrix.ext; change ∀ i j, raw31808step2 i j = -(raw31808step1 i j); unfold raw31808step2 raw31808step1; decide +kernel
      have hl : raw31808step2Labels = raw31808step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31808step2 raw31808step2Labels = mixedMoment B raw31808step3 raw31808step3Labels := by
      have ha : raw31808step3 = raw31808step2 := by apply Matrix.ext; unfold raw31808step3 raw31808step2; decide +kernel
      have hl : raw31808step2Labels = labelEmbedding10 ∘ raw31808step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31808step2 raw31808step2Labels raw31808step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5095 node5095Labels := by rfl

def raw31809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31809step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31809step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31809step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31809step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31809step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31809 raw31809Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw31809 raw31809Labels = mixedMoment B raw31809step0 raw31809step0Labels := by
      have ha : raw31809step0 = (fun i j => raw31809 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31809step0 raw31809; decide +kernel
      have hl : raw31809step0Labels = raw31809Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31809 raw31809Labels permutation159 permutation7
    mixedMoment B raw31809step0 raw31809step0Labels = mixedMoment B raw31809step1 raw31809step1Labels := by
      have ha : raw31809step1 = -raw31809step0 := by apply Matrix.ext; change ∀ i j, raw31809step1 i j = -(raw31809step0 i j); unfold raw31809step1 raw31809step0; decide +kernel
      have hl : raw31809step1Labels = raw31809step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31809step1 raw31809step1Labels = mixedMoment B raw31809step2 raw31809step2Labels := by
      have ha : raw31809step2 = raw31809step1 := by apply Matrix.ext; unfold raw31809step2 raw31809step1; decide +kernel
      have hl : raw31809step1Labels = labelEmbedding10 ∘ raw31809step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31809step1 raw31809step1Labels raw31809step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw31810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw31810step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31810step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31810step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31810step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31810 raw31810Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw31810 raw31810Labels = mixedMoment B raw31810step0 raw31810step0Labels := by
      have hz : ∀ j, raw31810 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31810step0 = (fun i j => raw31810 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31810step0 raw31810; decide +kernel
      have hl : raw31810step0Labels = raw31810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31810 raw31810Labels permutation434 hz
    mixedMoment B raw31810step0 raw31810step0Labels = mixedMoment B raw31810step1 raw31810step1Labels := by
      have ha : raw31810step1 = (fun i j => raw31810step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31810step1 raw31810step0; decide +kernel
      have hl : raw31810step1Labels = raw31810step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31810step0 raw31810step0Labels permutation33 permutation7
    mixedMoment B raw31810step1 raw31810step1Labels = mixedMoment B raw31810step2 raw31810step2Labels := by
      have ha : raw31810step2 = -raw31810step1 := by apply Matrix.ext; change ∀ i j, raw31810step2 i j = -(raw31810step1 i j); unfold raw31810step2 raw31810step1; decide +kernel
      have hl : raw31810step2Labels = raw31810step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31810step2 raw31810step2Labels = mixedMoment B raw31810step3 raw31810step3Labels := by
      have ha : raw31810step3 = raw31810step2 := by apply Matrix.ext; unfold raw31810step3 raw31810step2; decide +kernel
      have hl : raw31810step2Labels = labelEmbedding10 ∘ raw31810step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31810step2 raw31810step2Labels raw31810step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw31811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![1, 0, -1]]
def raw31811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw31811step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31811step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31811step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31811step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31811 raw31811Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw31811 raw31811Labels = mixedMoment B raw31811step0 raw31811step0Labels := by
      have hz : ∀ j, raw31811 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31811step0 = (fun i j => raw31811 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31811step0 raw31811; decide +kernel
      have hl : raw31811step0Labels = raw31811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31811 raw31811Labels permutation434 hz
    mixedMoment B raw31811step0 raw31811step0Labels = mixedMoment B raw31811step1 raw31811step1Labels := by
      have ha : raw31811step1 = (fun i j => raw31811step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31811step1 raw31811step0; decide +kernel
      have hl : raw31811step1Labels = raw31811step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31811step0 raw31811step0Labels permutation33 permutation7
    mixedMoment B raw31811step1 raw31811step1Labels = mixedMoment B raw31811step2 raw31811step2Labels := by
      have ha : raw31811step2 = -raw31811step1 := by apply Matrix.ext; change ∀ i j, raw31811step2 i j = -(raw31811step1 i j); unfold raw31811step2 raw31811step1; decide +kernel
      have hl : raw31811step2Labels = raw31811step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31811step2 raw31811step2Labels = mixedMoment B raw31811step3 raw31811step3Labels := by
      have ha : raw31811step3 = raw31811step2 := by apply Matrix.ext; unfold raw31811step3 raw31811step2; decide +kernel
      have hl : raw31811step2Labels = labelEmbedding10 ∘ raw31811step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31811step2 raw31811step2Labels raw31811step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5101 node5101Labels := by rfl

def raw31812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -1, -1]]
def raw31812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31812step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31812 raw31812Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw31812 raw31812Labels = mixedMoment B raw31812step0 raw31812step0Labels := by
      have hz : ∀ j, raw31812 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31812step0 = (fun i j => raw31812 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31812step0 raw31812; decide +kernel
      have hl : raw31812step0Labels = raw31812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31812 raw31812Labels permutation434 hz
    mixedMoment B raw31812step0 raw31812step0Labels = mixedMoment B raw31812step1 raw31812step1Labels := by
      have ha : raw31812step1 = (fun i j => raw31812step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31812step1 raw31812step0; decide +kernel
      have hl : raw31812step1Labels = raw31812step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31812step0 raw31812step0Labels permutation33 permutation2
    _ = mixedMoment B node4404 node4404Labels := by rfl

def raw31813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -1, -1]]
def raw31813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31813step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31813step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31813step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31813step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31813step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31813 raw31813Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw31813 raw31813Labels = mixedMoment B raw31813step0 raw31813step0Labels := by
      have hz : ∀ j, raw31813 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31813step0 = (fun i j => raw31813 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31813step0 raw31813; decide +kernel
      have hl : raw31813step0Labels = raw31813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31813 raw31813Labels permutation434 hz
    mixedMoment B raw31813step0 raw31813step0Labels = mixedMoment B raw31813step1 raw31813step1Labels := by
      have ha : raw31813step1 = (fun i j => raw31813step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31813step1 raw31813step0; decide +kernel
      have hl : raw31813step1Labels = raw31813step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31813step0 raw31813step0Labels permutation33 permutation7
    mixedMoment B raw31813step1 raw31813step1Labels = mixedMoment B raw31813step2 raw31813step2Labels := by
      have ha : raw31813step2 = -raw31813step1 := by apply Matrix.ext; change ∀ i j, raw31813step2 i j = -(raw31813step1 i j); unfold raw31813step2 raw31813step1; decide +kernel
      have hl : raw31813step2Labels = raw31813step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31813step2 raw31813step2Labels = mixedMoment B raw31813step3 raw31813step3Labels := by
      have ha : raw31813step3 = raw31813step2 := by apply Matrix.ext; unfold raw31813step3 raw31813step2; decide +kernel
      have hl : raw31813step2Labels = labelEmbedding10 ∘ raw31813step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31813step2 raw31813step2Labels raw31813step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

def raw31814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31814step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31814 raw31814Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw31814 raw31814Labels = mixedMoment B raw31814step0 raw31814step0Labels := by
      have ha : raw31814step0 = (fun i j => raw31814 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31814step0 raw31814; decide +kernel
      have hl : raw31814step0Labels = raw31814Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31814 raw31814Labels permutation201 permutation2
    _ = mixedMoment B node4782 node4782Labels := by rfl

def raw31815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw31815step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31815step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31815step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31815step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31815 raw31815Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw31815 raw31815Labels = mixedMoment B raw31815step0 raw31815step0Labels := by
      have hz : ∀ j, raw31815 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31815step0 = (fun i j => raw31815 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31815step0 raw31815; decide +kernel
      have hl : raw31815step0Labels = raw31815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31815 raw31815Labels permutation434 hz
    mixedMoment B raw31815step0 raw31815step0Labels = mixedMoment B raw31815step1 raw31815step1Labels := by
      have ha : raw31815step1 = (fun i j => raw31815step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31815step1 raw31815step0; decide +kernel
      have hl : raw31815step1Labels = raw31815step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31815step0 raw31815step0Labels permutation33 permutation7
    mixedMoment B raw31815step1 raw31815step1Labels = mixedMoment B raw31815step2 raw31815step2Labels := by
      have ha : raw31815step2 = -raw31815step1 := by apply Matrix.ext; change ∀ i j, raw31815step2 i j = -(raw31815step1 i j); unfold raw31815step2 raw31815step1; decide +kernel
      have hl : raw31815step2Labels = raw31815step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31815step2 raw31815step2Labels = mixedMoment B raw31815step3 raw31815step3Labels := by
      have ha : raw31815step3 = raw31815step2 := by apply Matrix.ext; unfold raw31815step3 raw31815step2; decide +kernel
      have hl : raw31815step2Labels = labelEmbedding10 ∘ raw31815step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31815step2 raw31815step2Labels raw31815step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw31816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, 0, -1]]
def raw31816step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw31816step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31816step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31816step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31816step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31816 raw31816Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw31816 raw31816Labels = mixedMoment B raw31816step0 raw31816step0Labels := by
      have hz : ∀ j, raw31816 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31816step0 = (fun i j => raw31816 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31816step0 raw31816; decide +kernel
      have hl : raw31816step0Labels = raw31816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31816 raw31816Labels permutation434 hz
    mixedMoment B raw31816step0 raw31816step0Labels = mixedMoment B raw31816step1 raw31816step1Labels := by
      have ha : raw31816step1 = (fun i j => raw31816step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31816step1 raw31816step0; decide +kernel
      have hl : raw31816step1Labels = raw31816step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31816step0 raw31816step0Labels permutation33 permutation7
    mixedMoment B raw31816step1 raw31816step1Labels = mixedMoment B raw31816step2 raw31816step2Labels := by
      have ha : raw31816step2 = -raw31816step1 := by apply Matrix.ext; change ∀ i j, raw31816step2 i j = -(raw31816step1 i j); unfold raw31816step2 raw31816step1; decide +kernel
      have hl : raw31816step2Labels = raw31816step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31816step2 raw31816step2Labels = mixedMoment B raw31816step3 raw31816step3Labels := by
      have ha : raw31816step3 = raw31816step2 := by apply Matrix.ext; unfold raw31816step3 raw31816step2; decide +kernel
      have hl : raw31816step2Labels = labelEmbedding10 ∘ raw31816step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31816step2 raw31816step2Labels raw31816step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw31817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![2, -1, -1]]
def raw31817step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31817step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31817 raw31817Labels = mixedMoment B node4311 node4311Labels := by
  calc
    mixedMoment B raw31817 raw31817Labels = mixedMoment B raw31817step0 raw31817step0Labels := by
      have hz : ∀ j, raw31817 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31817step0 = (fun i j => raw31817 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31817step0 raw31817; decide +kernel
      have hl : raw31817step0Labels = raw31817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31817 raw31817Labels permutation434 hz
    mixedMoment B raw31817step0 raw31817step0Labels = mixedMoment B raw31817step1 raw31817step1Labels := by
      have ha : raw31817step1 = (fun i j => raw31817step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31817step1 raw31817step0; decide +kernel
      have hl : raw31817step1Labels = raw31817step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31817step0 raw31817step0Labels permutation33 permutation2
    _ = mixedMoment B node4311 node4311Labels := by rfl

def raw31818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, 0, -2], ![2, -1, -1]]
def raw31818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31818step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31818 raw31818Labels = mixedMoment B node4652 node4652Labels := by
  calc
    mixedMoment B raw31818 raw31818Labels = mixedMoment B raw31818step0 raw31818step0Labels := by
      have hz : ∀ j, raw31818 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31818step0 = (fun i j => raw31818 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31818step0 raw31818; decide +kernel
      have hl : raw31818step0Labels = raw31818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31818 raw31818Labels permutation434 hz
    mixedMoment B raw31818step0 raw31818step0Labels = mixedMoment B raw31818step1 raw31818step1Labels := by
      have ha : raw31818step1 = (fun i j => raw31818step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31818step1 raw31818step0; decide +kernel
      have hl : raw31818step1Labels = raw31818step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31818step0 raw31818step0Labels permutation33 permutation2
    _ = mixedMoment B node4652 node4652Labels := by rfl

def raw31819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31819 raw31819Labels = mixedMoment B node4715 node4715Labels := by
  calc
    mixedMoment B raw31819 raw31819Labels = mixedMoment B raw31819step0 raw31819step0Labels := by
      have ha : raw31819step0 = (fun i j => raw31819 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31819step0 raw31819; decide +kernel
      have hl : raw31819step0Labels = raw31819Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31819 raw31819Labels permutation159 permutation2
    _ = mixedMoment B node4715 node4715Labels := by rfl

def raw31820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31820 raw31820Labels = mixedMoment B node4752 node4752Labels := by
  calc
    mixedMoment B raw31820 raw31820Labels = mixedMoment B raw31820step0 raw31820step0Labels := by
      have hz : ∀ j, raw31820 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31820step0 = (fun i j => raw31820 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31820step0 raw31820; decide +kernel
      have hl : raw31820step0Labels = raw31820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31820 raw31820Labels permutation434 hz
    _ = mixedMoment B node4752 node4752Labels := by rfl

def raw31821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![1, 0, -1]]
def raw31821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31821step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]
def raw31821step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw31821step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw31821step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw31821step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw31821step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31821 raw31821Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw31821 raw31821Labels = mixedMoment B raw31821step0 raw31821step0Labels := by
      have hz : ∀ j, raw31821 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31821step0 = (fun i j => raw31821 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31821step0 raw31821; decide +kernel
      have hl : raw31821step0Labels = raw31821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31821 raw31821Labels permutation434 hz
    mixedMoment B raw31821step0 raw31821step0Labels = mixedMoment B raw31821step1 raw31821step1Labels := by
      have hz : ∀ i, raw31821step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw31821step1 = (fun i j => raw31821step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw31821step1 raw31821step0; decide +kernel
      have hl : raw31821step1Labels = (fun j => raw31821step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31821step0 raw31821step0Labels permutation4 hz
    mixedMoment B raw31821step1 raw31821step1Labels = mixedMoment B raw31821step2 raw31821step2Labels := by
      have ha : raw31821step2 = (fun i j => raw31821step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31821step2 raw31821step1; decide +kernel
      have hl : raw31821step2Labels = raw31821step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31821step1 raw31821step1Labels permutation33 permutation0
    mixedMoment B raw31821step2 raw31821step2Labels = mixedMoment B raw31821step3 raw31821step3Labels := by
      have ha : raw31821step3 = raw31821step2 := by apply Matrix.ext; unfold raw31821step3 raw31821step2; decide +kernel
      have hl : raw31821step2Labels = labelEmbedding2 ∘ raw31821step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31821step2 raw31821step2Labels raw31821step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw31822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31822 raw31822Labels = mixedMoment B node4288 node4288Labels := by
  calc
    mixedMoment B raw31822 raw31822Labels = mixedMoment B raw31822step0 raw31822step0Labels := by
      have ha : raw31822step0 = (fun i j => raw31822 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31822step0 raw31822; decide +kernel
      have hl : raw31822step0Labels = raw31822Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31822 raw31822Labels permutation153 permutation2
    _ = mixedMoment B node4288 node4288Labels := by rfl

def raw31823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31823 raw31823Labels = mixedMoment B node4632 node4632Labels := by
  calc
    mixedMoment B raw31823 raw31823Labels = mixedMoment B raw31823step0 raw31823step0Labels := by
      have ha : raw31823step0 = (fun i j => raw31823 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31823step0 raw31823; decide +kernel
      have hl : raw31823step0Labels = raw31823Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31823 raw31823Labels permutation153 permutation2
    _ = mixedMoment B node4632 node4632Labels := by rfl

def raw31824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31824 raw31824Labels = mixedMoment B node4722 node4722Labels := by
  calc
    mixedMoment B raw31824 raw31824Labels = mixedMoment B raw31824step0 raw31824step0Labels := by
      have ha : raw31824step0 = (fun i j => raw31824 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31824step0 raw31824; decide +kernel
      have hl : raw31824step0Labels = raw31824Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31824 raw31824Labels permutation153 permutation2
    _ = mixedMoment B node4722 node4722Labels := by rfl

def raw31825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31825 raw31825Labels = mixedMoment B node4737 node4737Labels := by
  calc
    _ = mixedMoment B node4737 node4737Labels := by rfl

def raw31826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31826 raw31826Labels = mixedMoment B node4736 node4736Labels := by
  calc
    mixedMoment B raw31826 raw31826Labels = mixedMoment B raw31826step0 raw31826step0Labels := by
      have ha : raw31826step0 = (fun i j => raw31826 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31826step0 raw31826; decide +kernel
      have hl : raw31826step0Labels = raw31826Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31826 raw31826Labels permutation153 permutation2
    _ = mixedMoment B node4736 node4736Labels := by rfl

def raw31827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![3, -1, -2], ![2, -1, -1]]
def raw31827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31827 raw31827Labels = mixedMoment B node4295 node4295Labels := by
  calc
    mixedMoment B raw31827 raw31827Labels = mixedMoment B raw31827step0 raw31827step0Labels := by
      have hz : ∀ j, raw31827 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31827step0 = (fun i j => raw31827 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31827step0 raw31827; decide +kernel
      have hl : raw31827step0Labels = raw31827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31827 raw31827Labels permutation434 hz
    mixedMoment B raw31827step0 raw31827step0Labels = mixedMoment B raw31827step1 raw31827step1Labels := by
      have ha : raw31827step1 = (fun i j => raw31827step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31827step1 raw31827step0; decide +kernel
      have hl : raw31827step1Labels = raw31827step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31827step0 raw31827step0Labels permutation33 permutation2
    _ = mixedMoment B node4295 node4295Labels := by rfl

def raw31828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![3, -1, -2], ![2, -1, -1]]
def raw31828step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31828step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31828 raw31828Labels = mixedMoment B node4637 node4637Labels := by
  calc
    mixedMoment B raw31828 raw31828Labels = mixedMoment B raw31828step0 raw31828step0Labels := by
      have hz : ∀ j, raw31828 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31828step0 = (fun i j => raw31828 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31828step0 raw31828; decide +kernel
      have hl : raw31828step0Labels = raw31828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31828 raw31828Labels permutation434 hz
    mixedMoment B raw31828step0 raw31828step0Labels = mixedMoment B raw31828step1 raw31828step1Labels := by
      have ha : raw31828step1 = (fun i j => raw31828step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31828step1 raw31828step0; decide +kernel
      have hl : raw31828step1Labels = raw31828step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31828step0 raw31828step0Labels permutation33 permutation2
    _ = mixedMoment B node4637 node4637Labels := by rfl

def raw31829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![3, -1, -2], ![2, -1, -1]]
def raw31829step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31829step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31829 raw31829Labels = mixedMoment B node4726 node4726Labels := by
  calc
    mixedMoment B raw31829 raw31829Labels = mixedMoment B raw31829step0 raw31829step0Labels := by
      have hz : ∀ j, raw31829 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31829step0 = (fun i j => raw31829 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31829step0 raw31829; decide +kernel
      have hl : raw31829step0Labels = raw31829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31829 raw31829Labels permutation434 hz
    mixedMoment B raw31829step0 raw31829step0Labels = mixedMoment B raw31829step1 raw31829step1Labels := by
      have ha : raw31829step1 = (fun i j => raw31829step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31829step1 raw31829step0; decide +kernel
      have hl : raw31829step1Labels = raw31829step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31829step0 raw31829step0Labels permutation33 permutation2
    _ = mixedMoment B node4726 node4726Labels := by rfl

def raw31830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31830 raw31830Labels = mixedMoment B node4706 node4706Labels := by
  calc
    mixedMoment B raw31830 raw31830Labels = mixedMoment B raw31830step0 raw31830step0Labels := by
      have ha : raw31830step0 = (fun i j => raw31830 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31830step0 raw31830; decide +kernel
      have hl : raw31830step0Labels = raw31830Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31830 raw31830Labels permutation159 permutation2
    _ = mixedMoment B node4706 node4706Labels := by rfl

def raw31831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw31831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![3, -1, -2], ![1, 0, -1]]
def raw31831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw31831step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31831 raw31831Labels = mixedMoment B node4741 node4741Labels := by
  calc
    mixedMoment B raw31831 raw31831Labels = mixedMoment B raw31831step0 raw31831step0Labels := by
      have hz : ∀ j, raw31831 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31831step0 = (fun i j => raw31831 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31831step0 raw31831; decide +kernel
      have hl : raw31831step0Labels = raw31831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31831 raw31831Labels permutation434 hz
    mixedMoment B raw31831step0 raw31831step0Labels = mixedMoment B raw31831step1 raw31831step1Labels := by
      have ha : raw31831step1 = (fun i j => raw31831step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31831step1 raw31831step0; decide +kernel
      have hl : raw31831step1Labels = raw31831step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31831step0 raw31831step0Labels permutation33 permutation2
    _ = mixedMoment B node4741 node4741Labels := by rfl

def raw31832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31832step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31832 raw31832Labels = mixedMoment B node4296 node4296Labels := by
  calc
    mixedMoment B raw31832 raw31832Labels = mixedMoment B raw31832step0 raw31832step0Labels := by
      have hz : ∀ j, raw31832 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31832step0 = (fun i j => raw31832 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31832step0 raw31832; decide +kernel
      have hl : raw31832step0Labels = raw31832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31832 raw31832Labels permutation434 hz
    _ = mixedMoment B node4296 node4296Labels := by rfl

def raw31833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31833 raw31833Labels = mixedMoment B node4638 node4638Labels := by
  calc
    mixedMoment B raw31833 raw31833Labels = mixedMoment B raw31833step0 raw31833step0Labels := by
      have hz : ∀ j, raw31833 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31833step0 = (fun i j => raw31833 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31833step0 raw31833; decide +kernel
      have hl : raw31833step0Labels = raw31833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31833 raw31833Labels permutation434 hz
    _ = mixedMoment B node4638 node4638Labels := by rfl

def raw31834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31834step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31834 raw31834Labels = mixedMoment B node4727 node4727Labels := by
  calc
    mixedMoment B raw31834 raw31834Labels = mixedMoment B raw31834step0 raw31834step0Labels := by
      have hz : ∀ j, raw31834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31834step0 = (fun i j => raw31834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31834step0 raw31834; decide +kernel
      have hl : raw31834step0Labels = raw31834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31834 raw31834Labels permutation434 hz
    _ = mixedMoment B node4727 node4727Labels := by rfl

def raw31835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31835step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31835 raw31835Labels = mixedMoment B node4707 node4707Labels := by
  calc
    mixedMoment B raw31835 raw31835Labels = mixedMoment B raw31835step0 raw31835step0Labels := by
      have ha : raw31835step0 = (fun i j => raw31835 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31835step0 raw31835; decide +kernel
      have hl : raw31835step0Labels = raw31835Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31835 raw31835Labels permutation158 permutation2
    _ = mixedMoment B node4707 node4707Labels := by rfl

def raw31836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw31836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw31836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31836 raw31836Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw31836 raw31836Labels = mixedMoment B raw31836step0 raw31836step0Labels := by
      have hz : ∀ j, raw31836 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31836step0 = (fun i j => raw31836 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31836step0 raw31836; decide +kernel
      have hl : raw31836step0Labels = raw31836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31836 raw31836Labels permutation434 hz
    _ = mixedMoment B node4742 node4742Labels := by rfl

def raw31837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31837Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -1, -1]]
def raw31837step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31837step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31837step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31837step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31837step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31837 raw31837Labels = mixedMoment B node2400 node2400Labels := by
  calc
    mixedMoment B raw31837 raw31837Labels = mixedMoment B raw31837step0 raw31837step0Labels := by
      have hz : ∀ j, raw31837 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31837step0 = (fun i j => raw31837 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31837step0 raw31837; decide +kernel
      have hl : raw31837step0Labels = raw31837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31837 raw31837Labels permutation434 hz
    mixedMoment B raw31837step0 raw31837step0Labels = mixedMoment B raw31837step1 raw31837step1Labels := by
      have ha : raw31837step1 = (fun i j => raw31837step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31837step1 raw31837step0; decide +kernel
      have hl : raw31837step1Labels = raw31837step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31837step0 raw31837step0Labels permutation33 permutation7
    mixedMoment B raw31837step1 raw31837step1Labels = mixedMoment B raw31837step2 raw31837step2Labels := by
      have ha : raw31837step2 = -raw31837step1 := by apply Matrix.ext; change ∀ i j, raw31837step2 i j = -(raw31837step1 i j); unfold raw31837step2 raw31837step1; decide +kernel
      have hl : raw31837step2Labels = raw31837step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31837step2 raw31837step2Labels = mixedMoment B raw31837step3 raw31837step3Labels := by
      have ha : raw31837step3 = raw31837step2 := by apply Matrix.ext; unfold raw31837step3 raw31837step2; decide +kernel
      have hl : raw31837step2Labels = labelEmbedding1 ∘ raw31837step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31837step2 raw31837step2Labels raw31837step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2400 node2400Labels := by rfl

def raw31838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31838Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -1, -1]]
def raw31838step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31838step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31838step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31838step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31838step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31838step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31838 raw31838Labels = mixedMoment B node2505 node2505Labels := by
  calc
    mixedMoment B raw31838 raw31838Labels = mixedMoment B raw31838step0 raw31838step0Labels := by
      have hz : ∀ j, raw31838 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31838step0 = (fun i j => raw31838 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31838step0 raw31838; decide +kernel
      have hl : raw31838step0Labels = raw31838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31838 raw31838Labels permutation434 hz
    mixedMoment B raw31838step0 raw31838step0Labels = mixedMoment B raw31838step1 raw31838step1Labels := by
      have ha : raw31838step1 = (fun i j => raw31838step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31838step1 raw31838step0; decide +kernel
      have hl : raw31838step1Labels = raw31838step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31838step0 raw31838step0Labels permutation33 permutation7
    mixedMoment B raw31838step1 raw31838step1Labels = mixedMoment B raw31838step2 raw31838step2Labels := by
      have ha : raw31838step2 = -raw31838step1 := by apply Matrix.ext; change ∀ i j, raw31838step2 i j = -(raw31838step1 i j); unfold raw31838step2 raw31838step1; decide +kernel
      have hl : raw31838step2Labels = raw31838step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31838step2 raw31838step2Labels = mixedMoment B raw31838step3 raw31838step3Labels := by
      have ha : raw31838step3 = raw31838step2 := by apply Matrix.ext; unfold raw31838step3 raw31838step2; decide +kernel
      have hl : raw31838step2Labels = labelEmbedding1 ∘ raw31838step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31838step2 raw31838step2Labels raw31838step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2505 node2505Labels := by rfl

def raw31839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31839Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31839step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31839step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31839step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31839step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31839step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31839 raw31839Labels = mixedMoment B node2459 node2459Labels := by
  calc
    mixedMoment B raw31839 raw31839Labels = mixedMoment B raw31839step0 raw31839step0Labels := by
      have ha : raw31839step0 = (fun i j => raw31839 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31839step0 raw31839; decide +kernel
      have hl : raw31839step0Labels = raw31839Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31839 raw31839Labels permutation159 permutation7
    mixedMoment B raw31839step0 raw31839step0Labels = mixedMoment B raw31839step1 raw31839step1Labels := by
      have ha : raw31839step1 = -raw31839step0 := by apply Matrix.ext; change ∀ i j, raw31839step1 i j = -(raw31839step0 i j); unfold raw31839step1 raw31839step0; decide +kernel
      have hl : raw31839step1Labels = raw31839step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31839step1 raw31839step1Labels = mixedMoment B raw31839step2 raw31839step2Labels := by
      have ha : raw31839step2 = raw31839step1 := by apply Matrix.ext; unfold raw31839step2 raw31839step1; decide +kernel
      have hl : raw31839step1Labels = labelEmbedding1 ∘ raw31839step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31839step1 raw31839step1Labels raw31839step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2459 node2459Labels := by rfl

def raw31840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31840Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31840step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw31840step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31840step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31840step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31840step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31840 raw31840Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw31840 raw31840Labels = mixedMoment B raw31840step0 raw31840step0Labels := by
      have hz : ∀ j, raw31840 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31840step0 = (fun i j => raw31840 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31840step0 raw31840; decide +kernel
      have hl : raw31840step0Labels = raw31840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31840 raw31840Labels permutation434 hz
    mixedMoment B raw31840step0 raw31840step0Labels = mixedMoment B raw31840step1 raw31840step1Labels := by
      have ha : raw31840step1 = (fun i j => raw31840step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31840step1 raw31840step0; decide +kernel
      have hl : raw31840step1Labels = raw31840step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31840step0 raw31840step0Labels permutation33 permutation7
    mixedMoment B raw31840step1 raw31840step1Labels = mixedMoment B raw31840step2 raw31840step2Labels := by
      have ha : raw31840step2 = -raw31840step1 := by apply Matrix.ext; change ∀ i j, raw31840step2 i j = -(raw31840step1 i j); unfold raw31840step2 raw31840step1; decide +kernel
      have hl : raw31840step2Labels = raw31840step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31840step2 raw31840step2Labels = mixedMoment B raw31840step3 raw31840step3Labels := by
      have ha : raw31840step3 = raw31840step2 := by apply Matrix.ext; unfold raw31840step3 raw31840step2; decide +kernel
      have hl : raw31840step2Labels = labelEmbedding1 ∘ raw31840step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31840step2 raw31840step2Labels raw31840step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw31841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31841Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![1, 0, -1]]
def raw31841step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw31841step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31841step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31841step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31841step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31841step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31841 raw31841Labels = mixedMoment B node2511 node2511Labels := by
  calc
    mixedMoment B raw31841 raw31841Labels = mixedMoment B raw31841step0 raw31841step0Labels := by
      have hz : ∀ j, raw31841 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31841step0 = (fun i j => raw31841 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31841step0 raw31841; decide +kernel
      have hl : raw31841step0Labels = raw31841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31841 raw31841Labels permutation434 hz
    mixedMoment B raw31841step0 raw31841step0Labels = mixedMoment B raw31841step1 raw31841step1Labels := by
      have ha : raw31841step1 = (fun i j => raw31841step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31841step1 raw31841step0; decide +kernel
      have hl : raw31841step1Labels = raw31841step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31841step0 raw31841step0Labels permutation33 permutation7
    mixedMoment B raw31841step1 raw31841step1Labels = mixedMoment B raw31841step2 raw31841step2Labels := by
      have ha : raw31841step2 = -raw31841step1 := by apply Matrix.ext; change ∀ i j, raw31841step2 i j = -(raw31841step1 i j); unfold raw31841step2 raw31841step1; decide +kernel
      have hl : raw31841step2Labels = raw31841step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31841step2 raw31841step2Labels = mixedMoment B raw31841step3 raw31841step3Labels := by
      have ha : raw31841step3 = raw31841step2 := by apply Matrix.ext; unfold raw31841step3 raw31841step2; decide +kernel
      have hl : raw31841step2Labels = labelEmbedding1 ∘ raw31841step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31841step2 raw31841step2Labels raw31841step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2511 node2511Labels := by rfl

def raw31842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31842Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -1, -1]]
def raw31842step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31842step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31842step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31842step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31842step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31842step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31842 raw31842Labels = mixedMoment B node1618 node1618Labels := by
  calc
    mixedMoment B raw31842 raw31842Labels = mixedMoment B raw31842step0 raw31842step0Labels := by
      have hz : ∀ j, raw31842 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31842step0 = (fun i j => raw31842 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31842step0 raw31842; decide +kernel
      have hl : raw31842step0Labels = raw31842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31842 raw31842Labels permutation434 hz
    mixedMoment B raw31842step0 raw31842step0Labels = mixedMoment B raw31842step1 raw31842step1Labels := by
      have ha : raw31842step1 = (fun i j => raw31842step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31842step1 raw31842step0; decide +kernel
      have hl : raw31842step1Labels = raw31842step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31842step0 raw31842step0Labels permutation33 permutation7
    mixedMoment B raw31842step1 raw31842step1Labels = mixedMoment B raw31842step2 raw31842step2Labels := by
      have ha : raw31842step2 = -raw31842step1 := by apply Matrix.ext; change ∀ i j, raw31842step2 i j = -(raw31842step1 i j); unfold raw31842step2 raw31842step1; decide +kernel
      have hl : raw31842step2Labels = raw31842step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31842step2 raw31842step2Labels = mixedMoment B raw31842step3 raw31842step3Labels := by
      have ha : raw31842step3 = raw31842step2 := by apply Matrix.ext; unfold raw31842step3 raw31842step2; decide +kernel
      have hl : raw31842step2Labels = labelEmbedding1 ∘ raw31842step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31842step2 raw31842step2Labels raw31842step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1618 node1618Labels := by rfl

def raw31843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31843Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -1, -1]]
def raw31843step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31843step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31843step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31843step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31843step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31843step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31843 raw31843Labels = mixedMoment B node2048 node2048Labels := by
  calc
    mixedMoment B raw31843 raw31843Labels = mixedMoment B raw31843step0 raw31843step0Labels := by
      have hz : ∀ j, raw31843 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31843step0 = (fun i j => raw31843 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31843step0 raw31843; decide +kernel
      have hl : raw31843step0Labels = raw31843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31843 raw31843Labels permutation434 hz
    mixedMoment B raw31843step0 raw31843step0Labels = mixedMoment B raw31843step1 raw31843step1Labels := by
      have ha : raw31843step1 = (fun i j => raw31843step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31843step1 raw31843step0; decide +kernel
      have hl : raw31843step1Labels = raw31843step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31843step0 raw31843step0Labels permutation33 permutation7
    mixedMoment B raw31843step1 raw31843step1Labels = mixedMoment B raw31843step2 raw31843step2Labels := by
      have ha : raw31843step2 = -raw31843step1 := by apply Matrix.ext; change ∀ i j, raw31843step2 i j = -(raw31843step1 i j); unfold raw31843step2 raw31843step1; decide +kernel
      have hl : raw31843step2Labels = raw31843step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31843step2 raw31843step2Labels = mixedMoment B raw31843step3 raw31843step3Labels := by
      have ha : raw31843step3 = raw31843step2 := by apply Matrix.ext; unfold raw31843step3 raw31843step2; decide +kernel
      have hl : raw31843step2Labels = labelEmbedding1 ∘ raw31843step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31843step2 raw31843step2Labels raw31843step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2048 node2048Labels := by rfl

def raw31844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31844Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31844step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31844step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31844step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31844step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31844step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31844 raw31844Labels = mixedMoment B node1997 node1997Labels := by
  calc
    mixedMoment B raw31844 raw31844Labels = mixedMoment B raw31844step0 raw31844step0Labels := by
      have ha : raw31844step0 = (fun i j => raw31844 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31844step0 raw31844; decide +kernel
      have hl : raw31844step0Labels = raw31844Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31844 raw31844Labels permutation159 permutation7
    mixedMoment B raw31844step0 raw31844step0Labels = mixedMoment B raw31844step1 raw31844step1Labels := by
      have ha : raw31844step1 = -raw31844step0 := by apply Matrix.ext; change ∀ i j, raw31844step1 i j = -(raw31844step0 i j); unfold raw31844step1 raw31844step0; decide +kernel
      have hl : raw31844step1Labels = raw31844step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31844step1 raw31844step1Labels = mixedMoment B raw31844step2 raw31844step2Labels := by
      have ha : raw31844step2 = raw31844step1 := by apply Matrix.ext; unfold raw31844step2 raw31844step1; decide +kernel
      have hl : raw31844step1Labels = labelEmbedding1 ∘ raw31844step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31844step1 raw31844step1Labels raw31844step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1997 node1997Labels := by rfl

def raw31845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31845Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31845step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw31845step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31845step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31845step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31845step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31845 raw31845Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw31845 raw31845Labels = mixedMoment B raw31845step0 raw31845step0Labels := by
      have hz : ∀ j, raw31845 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31845step0 = (fun i j => raw31845 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31845step0 raw31845; decide +kernel
      have hl : raw31845step0Labels = raw31845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31845 raw31845Labels permutation434 hz
    mixedMoment B raw31845step0 raw31845step0Labels = mixedMoment B raw31845step1 raw31845step1Labels := by
      have ha : raw31845step1 = (fun i j => raw31845step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31845step1 raw31845step0; decide +kernel
      have hl : raw31845step1Labels = raw31845step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31845step0 raw31845step0Labels permutation33 permutation7
    mixedMoment B raw31845step1 raw31845step1Labels = mixedMoment B raw31845step2 raw31845step2Labels := by
      have ha : raw31845step2 = -raw31845step1 := by apply Matrix.ext; change ∀ i j, raw31845step2 i j = -(raw31845step1 i j); unfold raw31845step2 raw31845step1; decide +kernel
      have hl : raw31845step2Labels = raw31845step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31845step2 raw31845step2Labels = mixedMoment B raw31845step3 raw31845step3Labels := by
      have ha : raw31845step3 = raw31845step2 := by apply Matrix.ext; unfold raw31845step3 raw31845step2; decide +kernel
      have hl : raw31845step2Labels = labelEmbedding1 ∘ raw31845step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31845step2 raw31845step2Labels raw31845step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2054 node2054Labels := by rfl

def raw31846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31846Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, 0, -1]]
def raw31846step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw31846step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31846step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31846step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31846step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31846step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31846 raw31846Labels = mixedMoment B node2053 node2053Labels := by
  calc
    mixedMoment B raw31846 raw31846Labels = mixedMoment B raw31846step0 raw31846step0Labels := by
      have hz : ∀ j, raw31846 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31846step0 = (fun i j => raw31846 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31846step0 raw31846; decide +kernel
      have hl : raw31846step0Labels = raw31846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31846 raw31846Labels permutation434 hz
    mixedMoment B raw31846step0 raw31846step0Labels = mixedMoment B raw31846step1 raw31846step1Labels := by
      have ha : raw31846step1 = (fun i j => raw31846step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31846step1 raw31846step0; decide +kernel
      have hl : raw31846step1Labels = raw31846step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31846step0 raw31846step0Labels permutation33 permutation7
    mixedMoment B raw31846step1 raw31846step1Labels = mixedMoment B raw31846step2 raw31846step2Labels := by
      have ha : raw31846step2 = -raw31846step1 := by apply Matrix.ext; change ∀ i j, raw31846step2 i j = -(raw31846step1 i j); unfold raw31846step2 raw31846step1; decide +kernel
      have hl : raw31846step2Labels = raw31846step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31846step2 raw31846step2Labels = mixedMoment B raw31846step3 raw31846step3Labels := by
      have ha : raw31846step3 = raw31846step2 := by apply Matrix.ext; unfold raw31846step3 raw31846step2; decide +kernel
      have hl : raw31846step2Labels = labelEmbedding1 ∘ raw31846step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31846step2 raw31846step2Labels raw31846step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2053 node2053Labels := by rfl

def raw31847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31847Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![2, -1, -1]]
def raw31847step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31847step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31847step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31847step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31847step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31847step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31847 raw31847Labels = mixedMoment B node1572 node1572Labels := by
  calc
    mixedMoment B raw31847 raw31847Labels = mixedMoment B raw31847step0 raw31847step0Labels := by
      have hz : ∀ j, raw31847 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31847step0 = (fun i j => raw31847 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31847step0 raw31847; decide +kernel
      have hl : raw31847step0Labels = raw31847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31847 raw31847Labels permutation434 hz
    mixedMoment B raw31847step0 raw31847step0Labels = mixedMoment B raw31847step1 raw31847step1Labels := by
      have ha : raw31847step1 = (fun i j => raw31847step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31847step1 raw31847step0; decide +kernel
      have hl : raw31847step1Labels = raw31847step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31847step0 raw31847step0Labels permutation33 permutation7
    mixedMoment B raw31847step1 raw31847step1Labels = mixedMoment B raw31847step2 raw31847step2Labels := by
      have ha : raw31847step2 = -raw31847step1 := by apply Matrix.ext; change ∀ i j, raw31847step2 i j = -(raw31847step1 i j); unfold raw31847step2 raw31847step1; decide +kernel
      have hl : raw31847step2Labels = raw31847step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31847step2 raw31847step2Labels = mixedMoment B raw31847step3 raw31847step3Labels := by
      have ha : raw31847step3 = raw31847step2 := by apply Matrix.ext; unfold raw31847step3 raw31847step2; decide +kernel
      have hl : raw31847step2Labels = labelEmbedding1 ∘ raw31847step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31847step2 raw31847step2Labels raw31847step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1572 node1572Labels := by rfl

def raw31848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31848Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, 0, -2], ![2, -1, -1]]
def raw31848step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31848step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31848step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31848step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31848step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31848step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31848 raw31848Labels = mixedMoment B node1853 node1853Labels := by
  calc
    mixedMoment B raw31848 raw31848Labels = mixedMoment B raw31848step0 raw31848step0Labels := by
      have hz : ∀ j, raw31848 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31848step0 = (fun i j => raw31848 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31848step0 raw31848; decide +kernel
      have hl : raw31848step0Labels = raw31848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31848 raw31848Labels permutation434 hz
    mixedMoment B raw31848step0 raw31848step0Labels = mixedMoment B raw31848step1 raw31848step1Labels := by
      have ha : raw31848step1 = (fun i j => raw31848step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31848step1 raw31848step0; decide +kernel
      have hl : raw31848step1Labels = raw31848step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31848step0 raw31848step0Labels permutation33 permutation7
    mixedMoment B raw31848step1 raw31848step1Labels = mixedMoment B raw31848step2 raw31848step2Labels := by
      have ha : raw31848step2 = -raw31848step1 := by apply Matrix.ext; change ∀ i j, raw31848step2 i j = -(raw31848step1 i j); unfold raw31848step2 raw31848step1; decide +kernel
      have hl : raw31848step2Labels = raw31848step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31848step2 raw31848step2Labels = mixedMoment B raw31848step3 raw31848step3Labels := by
      have ha : raw31848step3 = raw31848step2 := by apply Matrix.ext; unfold raw31848step3 raw31848step2; decide +kernel
      have hl : raw31848step2Labels = labelEmbedding1 ∘ raw31848step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31848step2 raw31848step2Labels raw31848step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1853 node1853Labels := by rfl

def raw31849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31849Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31849step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31849step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31849step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw31849step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31849 raw31849Labels = mixedMoment B node1890 node1890Labels := by
  calc
    mixedMoment B raw31849 raw31849Labels = mixedMoment B raw31849step0 raw31849step0Labels := by
      have ha : raw31849step0 = (fun i j => raw31849 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31849step0 raw31849; decide +kernel
      have hl : raw31849step0Labels = raw31849Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31849 raw31849Labels permutation159 permutation7
    mixedMoment B raw31849step0 raw31849step0Labels = mixedMoment B raw31849step1 raw31849step1Labels := by
      have ha : raw31849step1 = -raw31849step0 := by apply Matrix.ext; change ∀ i j, raw31849step1 i j = -(raw31849step0 i j); unfold raw31849step1 raw31849step0; decide +kernel
      have hl : raw31849step1Labels = raw31849step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31849step1 raw31849step1Labels = mixedMoment B raw31849step2 raw31849step2Labels := by
      have ha : raw31849step2 = raw31849step1 := by apply Matrix.ext; unfold raw31849step2 raw31849step1; decide +kernel
      have hl : raw31849step1Labels = labelEmbedding1 ∘ raw31849step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31849step1 raw31849step1Labels raw31849step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1890 node1890Labels := by rfl

def raw31850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31850Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31850step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw31850step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31850step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31850step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31850step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31850 raw31850Labels = mixedMoment B node1947 node1947Labels := by
  calc
    mixedMoment B raw31850 raw31850Labels = mixedMoment B raw31850step0 raw31850step0Labels := by
      have hz : ∀ j, raw31850 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31850step0 = (fun i j => raw31850 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31850step0 raw31850; decide +kernel
      have hl : raw31850step0Labels = raw31850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31850 raw31850Labels permutation434 hz
    mixedMoment B raw31850step0 raw31850step0Labels = mixedMoment B raw31850step1 raw31850step1Labels := by
      have ha : raw31850step1 = (fun i j => raw31850step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31850step1 raw31850step0; decide +kernel
      have hl : raw31850step1Labels = raw31850step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31850step0 raw31850step0Labels permutation33 permutation7
    mixedMoment B raw31850step1 raw31850step1Labels = mixedMoment B raw31850step2 raw31850step2Labels := by
      have ha : raw31850step2 = -raw31850step1 := by apply Matrix.ext; change ∀ i j, raw31850step2 i j = -(raw31850step1 i j); unfold raw31850step2 raw31850step1; decide +kernel
      have hl : raw31850step2Labels = raw31850step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31850step2 raw31850step2Labels = mixedMoment B raw31850step3 raw31850step3Labels := by
      have ha : raw31850step3 = raw31850step2 := by apply Matrix.ext; unfold raw31850step3 raw31850step2; decide +kernel
      have hl : raw31850step2Labels = labelEmbedding1 ∘ raw31850step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31850step2 raw31850step2Labels raw31850step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1947 node1947Labels := by rfl

def raw31851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31851Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![1, 0, -1]]
def raw31851step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31851step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]
def raw31851step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31851step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw31851step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31851 raw31851Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw31851 raw31851Labels = mixedMoment B raw31851step0 raw31851step0Labels := by
      have hz : ∀ j, raw31851 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31851step0 = (fun i j => raw31851 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31851step0 raw31851; decide +kernel
      have hl : raw31851step0Labels = raw31851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31851 raw31851Labels permutation434 hz
    mixedMoment B raw31851step0 raw31851step0Labels = mixedMoment B raw31851step1 raw31851step1Labels := by
      have hz : ∀ i, raw31851step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw31851step1 = (fun i j => raw31851step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw31851step1 raw31851step0; decide +kernel
      have hl : raw31851step1Labels = (fun j => raw31851step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw31851step0 raw31851step0Labels permutation4 hz
    mixedMoment B raw31851step1 raw31851step1Labels = mixedMoment B raw31851step2 raw31851step2Labels := by
      have ha : raw31851step2 = (fun i j => raw31851step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31851step2 raw31851step1; decide +kernel
      have hl : raw31851step2Labels = raw31851step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31851step1 raw31851step1Labels permutation33 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw31852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31852Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31852step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31852step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31852step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31852step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31852 raw31852Labels = mixedMoment B node1554 node1554Labels := by
  calc
    mixedMoment B raw31852 raw31852Labels = mixedMoment B raw31852step0 raw31852step0Labels := by
      have ha : raw31852step0 = (fun i j => raw31852 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31852step0 raw31852; decide +kernel
      have hl : raw31852step0Labels = raw31852Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31852 raw31852Labels permutation159 permutation7
    mixedMoment B raw31852step0 raw31852step0Labels = mixedMoment B raw31852step1 raw31852step1Labels := by
      have ha : raw31852step1 = -raw31852step0 := by apply Matrix.ext; change ∀ i j, raw31852step1 i j = -(raw31852step0 i j); unfold raw31852step1 raw31852step0; decide +kernel
      have hl : raw31852step1Labels = raw31852step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31852step1 raw31852step1Labels = mixedMoment B raw31852step2 raw31852step2Labels := by
      have ha : raw31852step2 = raw31852step1 := by apply Matrix.ext; unfold raw31852step2 raw31852step1; decide +kernel
      have hl : raw31852step1Labels = labelEmbedding1 ∘ raw31852step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31852step1 raw31852step1Labels raw31852step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1554 node1554Labels := by rfl

def raw31853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31853Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31853step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31853step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31853step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31853step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31853 raw31853Labels = mixedMoment B node1837 node1837Labels := by
  calc
    mixedMoment B raw31853 raw31853Labels = mixedMoment B raw31853step0 raw31853step0Labels := by
      have ha : raw31853step0 = (fun i j => raw31853 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31853step0 raw31853; decide +kernel
      have hl : raw31853step0Labels = raw31853Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31853 raw31853Labels permutation159 permutation7
    mixedMoment B raw31853step0 raw31853step0Labels = mixedMoment B raw31853step1 raw31853step1Labels := by
      have ha : raw31853step1 = -raw31853step0 := by apply Matrix.ext; change ∀ i j, raw31853step1 i j = -(raw31853step0 i j); unfold raw31853step1 raw31853step0; decide +kernel
      have hl : raw31853step1Labels = raw31853step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31853step1 raw31853step1Labels = mixedMoment B raw31853step2 raw31853step2Labels := by
      have ha : raw31853step2 = raw31853step1 := by apply Matrix.ext; unfold raw31853step2 raw31853step1; decide +kernel
      have hl : raw31853step1Labels = labelEmbedding1 ∘ raw31853step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31853step1 raw31853step1Labels raw31853step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1837 node1837Labels := by rfl

def raw31854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw31854Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31854step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31854step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31854step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31854step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31854 raw31854Labels = mixedMoment B node1906 node1906Labels := by
  calc
    mixedMoment B raw31854 raw31854Labels = mixedMoment B raw31854step0 raw31854step0Labels := by
      have ha : raw31854step0 = (fun i j => raw31854 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31854step0 raw31854; decide +kernel
      have hl : raw31854step0Labels = raw31854Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31854 raw31854Labels permutation159 permutation7
    mixedMoment B raw31854step0 raw31854step0Labels = mixedMoment B raw31854step1 raw31854step1Labels := by
      have ha : raw31854step1 = -raw31854step0 := by apply Matrix.ext; change ∀ i j, raw31854step1 i j = -(raw31854step0 i j); unfold raw31854step1 raw31854step0; decide +kernel
      have hl : raw31854step1Labels = raw31854step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31854step1 raw31854step1Labels = mixedMoment B raw31854step2 raw31854step2Labels := by
      have ha : raw31854step2 = raw31854step1 := by apply Matrix.ext; unfold raw31854step2 raw31854step1; decide +kernel
      have hl : raw31854step1Labels = labelEmbedding1 ∘ raw31854step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31854step1 raw31854step1Labels raw31854step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1906 node1906Labels := by rfl

def raw31855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31855Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw31855step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31855step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31855step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31855step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31855 raw31855Labels = mixedMoment B node1909 node1909Labels := by
  calc
    mixedMoment B raw31855 raw31855Labels = mixedMoment B raw31855step0 raw31855step0Labels := by
      have ha : raw31855step0 = (fun i j => raw31855 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31855step0 raw31855; decide +kernel
      have hl : raw31855step0Labels = raw31855Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31855 raw31855Labels permutation159 permutation7
    mixedMoment B raw31855step0 raw31855step0Labels = mixedMoment B raw31855step1 raw31855step1Labels := by
      have ha : raw31855step1 = -raw31855step0 := by apply Matrix.ext; change ∀ i j, raw31855step1 i j = -(raw31855step0 i j); unfold raw31855step1 raw31855step0; decide +kernel
      have hl : raw31855step1Labels = raw31855step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31855step1 raw31855step1Labels = mixedMoment B raw31855step2 raw31855step2Labels := by
      have ha : raw31855step2 = raw31855step1 := by apply Matrix.ext; unfold raw31855step2 raw31855step1; decide +kernel
      have hl : raw31855step1Labels = labelEmbedding1 ∘ raw31855step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31855step1 raw31855step1Labels raw31855step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1909 node1909Labels := by rfl

def raw31856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw31856Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw31856step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31856step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31856step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31856step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31856 raw31856Labels = mixedMoment B node1908 node1908Labels := by
  calc
    mixedMoment B raw31856 raw31856Labels = mixedMoment B raw31856step0 raw31856step0Labels := by
      have ha : raw31856step0 = (fun i j => raw31856 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31856step0 raw31856; decide +kernel
      have hl : raw31856step0Labels = raw31856Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31856 raw31856Labels permutation159 permutation7
    mixedMoment B raw31856step0 raw31856step0Labels = mixedMoment B raw31856step1 raw31856step1Labels := by
      have ha : raw31856step1 = -raw31856step0 := by apply Matrix.ext; change ∀ i j, raw31856step1 i j = -(raw31856step0 i j); unfold raw31856step1 raw31856step0; decide +kernel
      have hl : raw31856step1Labels = raw31856step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31856step1 raw31856step1Labels = mixedMoment B raw31856step2 raw31856step2Labels := by
      have ha : raw31856step2 = raw31856step1 := by apply Matrix.ext; unfold raw31856step2 raw31856step1; decide +kernel
      have hl : raw31856step1Labels = labelEmbedding1 ∘ raw31856step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31856step1 raw31856step1Labels raw31856step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1908 node1908Labels := by rfl

def raw31857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31857Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![3, -1, -2], ![2, -1, -1]]
def raw31857step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw31857step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw31857step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31857step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw31857step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31857 raw31857Labels = mixedMoment B node1569 node1569Labels := by
  calc
    mixedMoment B raw31857 raw31857Labels = mixedMoment B raw31857step0 raw31857step0Labels := by
      have hz : ∀ j, raw31857 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31857step0 = (fun i j => raw31857 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31857step0 raw31857; decide +kernel
      have hl : raw31857step0Labels = raw31857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31857 raw31857Labels permutation434 hz
    mixedMoment B raw31857step0 raw31857step0Labels = mixedMoment B raw31857step1 raw31857step1Labels := by
      have ha : raw31857step1 = (fun i j => raw31857step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31857step1 raw31857step0; decide +kernel
      have hl : raw31857step1Labels = raw31857step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31857step0 raw31857step0Labels permutation33 permutation7
    mixedMoment B raw31857step1 raw31857step1Labels = mixedMoment B raw31857step2 raw31857step2Labels := by
      have ha : raw31857step2 = -raw31857step1 := by apply Matrix.ext; change ∀ i j, raw31857step2 i j = -(raw31857step1 i j); unfold raw31857step2 raw31857step1; decide +kernel
      have hl : raw31857step2Labels = raw31857step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31857step2 raw31857step2Labels = mixedMoment B raw31857step3 raw31857step3Labels := by
      have ha : raw31857step3 = raw31857step2 := by apply Matrix.ext; unfold raw31857step3 raw31857step2; decide +kernel
      have hl : raw31857step2Labels = labelEmbedding1 ∘ raw31857step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31857step2 raw31857step2Labels raw31857step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1569 node1569Labels := by rfl

def raw31858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31858Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![3, -1, -2], ![2, -1, -1]]
def raw31858step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw31858step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw31858step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31858step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw31858step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31858 raw31858Labels = mixedMoment B node1850 node1850Labels := by
  calc
    mixedMoment B raw31858 raw31858Labels = mixedMoment B raw31858step0 raw31858step0Labels := by
      have hz : ∀ j, raw31858 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31858step0 = (fun i j => raw31858 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31858step0 raw31858; decide +kernel
      have hl : raw31858step0Labels = raw31858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31858 raw31858Labels permutation434 hz
    mixedMoment B raw31858step0 raw31858step0Labels = mixedMoment B raw31858step1 raw31858step1Labels := by
      have ha : raw31858step1 = (fun i j => raw31858step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31858step1 raw31858step0; decide +kernel
      have hl : raw31858step1Labels = raw31858step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31858step0 raw31858step0Labels permutation33 permutation7
    mixedMoment B raw31858step1 raw31858step1Labels = mixedMoment B raw31858step2 raw31858step2Labels := by
      have ha : raw31858step2 = -raw31858step1 := by apply Matrix.ext; change ∀ i j, raw31858step2 i j = -(raw31858step1 i j); unfold raw31858step2 raw31858step1; decide +kernel
      have hl : raw31858step2Labels = raw31858step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31858step2 raw31858step2Labels = mixedMoment B raw31858step3 raw31858step3Labels := by
      have ha : raw31858step3 = raw31858step2 := by apply Matrix.ext; unfold raw31858step3 raw31858step2; decide +kernel
      have hl : raw31858step2Labels = labelEmbedding1 ∘ raw31858step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31858step2 raw31858step2Labels raw31858step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1850 node1850Labels := by rfl

def raw31859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31859Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![3, -1, -2], ![2, -1, -1]]
def raw31859step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw31859step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31859step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw31859step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31859step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw31859step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31859 raw31859Labels = mixedMoment B node1938 node1938Labels := by
  calc
    mixedMoment B raw31859 raw31859Labels = mixedMoment B raw31859step0 raw31859step0Labels := by
      have hz : ∀ j, raw31859 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31859step0 = (fun i j => raw31859 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31859step0 raw31859; decide +kernel
      have hl : raw31859step0Labels = raw31859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31859 raw31859Labels permutation434 hz
    mixedMoment B raw31859step0 raw31859step0Labels = mixedMoment B raw31859step1 raw31859step1Labels := by
      have ha : raw31859step1 = (fun i j => raw31859step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31859step1 raw31859step0; decide +kernel
      have hl : raw31859step1Labels = raw31859step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31859step0 raw31859step0Labels permutation33 permutation7
    mixedMoment B raw31859step1 raw31859step1Labels = mixedMoment B raw31859step2 raw31859step2Labels := by
      have ha : raw31859step2 = -raw31859step1 := by apply Matrix.ext; change ∀ i j, raw31859step2 i j = -(raw31859step1 i j); unfold raw31859step2 raw31859step1; decide +kernel
      have hl : raw31859step2Labels = raw31859step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31859step2 raw31859step2Labels = mixedMoment B raw31859step3 raw31859step3Labels := by
      have ha : raw31859step3 = raw31859step2 := by apply Matrix.ext; unfold raw31859step3 raw31859step2; decide +kernel
      have hl : raw31859step2Labels = labelEmbedding1 ∘ raw31859step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31859step2 raw31859step2Labels raw31859step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1938 node1938Labels := by rfl

def raw31860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw31860Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw31860step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31860step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw31860step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31860step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw31860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31860 raw31860Labels = mixedMoment B node1888 node1888Labels := by
  calc
    mixedMoment B raw31860 raw31860Labels = mixedMoment B raw31860step0 raw31860step0Labels := by
      have ha : raw31860step0 = (fun i j => raw31860 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31860step0 raw31860; decide +kernel
      have hl : raw31860step0Labels = raw31860Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31860 raw31860Labels permutation159 permutation7
    mixedMoment B raw31860step0 raw31860step0Labels = mixedMoment B raw31860step1 raw31860step1Labels := by
      have ha : raw31860step1 = -raw31860step0 := by apply Matrix.ext; change ∀ i j, raw31860step1 i j = -(raw31860step0 i j); unfold raw31860step1 raw31860step0; decide +kernel
      have hl : raw31860step1Labels = raw31860step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31860step1 raw31860step1Labels = mixedMoment B raw31860step2 raw31860step2Labels := by
      have ha : raw31860step2 = raw31860step1 := by apply Matrix.ext; unfold raw31860step2 raw31860step1; decide +kernel
      have hl : raw31860step1Labels = labelEmbedding1 ∘ raw31860step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31860step1 raw31860step1Labels raw31860step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1888 node1888Labels := by rfl

def raw31861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw31861Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![3, -1, -2], ![1, 0, -1]]
def raw31861step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw31861step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw31861step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31861step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw31861step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31861 raw31861Labels = mixedMoment B node1944 node1944Labels := by
  calc
    mixedMoment B raw31861 raw31861Labels = mixedMoment B raw31861step0 raw31861step0Labels := by
      have hz : ∀ j, raw31861 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31861step0 = (fun i j => raw31861 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31861step0 raw31861; decide +kernel
      have hl : raw31861step0Labels = raw31861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31861 raw31861Labels permutation434 hz
    mixedMoment B raw31861step0 raw31861step0Labels = mixedMoment B raw31861step1 raw31861step1Labels := by
      have ha : raw31861step1 = (fun i j => raw31861step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31861step1 raw31861step0; decide +kernel
      have hl : raw31861step1Labels = raw31861step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31861step0 raw31861step0Labels permutation33 permutation7
    mixedMoment B raw31861step1 raw31861step1Labels = mixedMoment B raw31861step2 raw31861step2Labels := by
      have ha : raw31861step2 = -raw31861step1 := by apply Matrix.ext; change ∀ i j, raw31861step2 i j = -(raw31861step1 i j); unfold raw31861step2 raw31861step1; decide +kernel
      have hl : raw31861step2Labels = raw31861step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31861step2 raw31861step2Labels = mixedMoment B raw31861step3 raw31861step3Labels := by
      have ha : raw31861step3 = raw31861step2 := by apply Matrix.ext; unfold raw31861step3 raw31861step2; decide +kernel
      have hl : raw31861step2Labels = labelEmbedding1 ∘ raw31861step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31861step2 raw31861step2Labels raw31861step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1944 node1944Labels := by rfl

def raw31862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31862Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31862step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw31862step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw31862step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31862step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw31862step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31862 raw31862Labels = mixedMoment B node1570 node1570Labels := by
  calc
    mixedMoment B raw31862 raw31862Labels = mixedMoment B raw31862step0 raw31862step0Labels := by
      have hz : ∀ j, raw31862 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31862step0 = (fun i j => raw31862 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31862step0 raw31862; decide +kernel
      have hl : raw31862step0Labels = raw31862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31862 raw31862Labels permutation434 hz
    mixedMoment B raw31862step0 raw31862step0Labels = mixedMoment B raw31862step1 raw31862step1Labels := by
      have ha : raw31862step1 = (fun i j => raw31862step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31862step1 raw31862step0; decide +kernel
      have hl : raw31862step1Labels = raw31862step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31862step0 raw31862step0Labels permutation33 permutation7
    mixedMoment B raw31862step1 raw31862step1Labels = mixedMoment B raw31862step2 raw31862step2Labels := by
      have ha : raw31862step2 = -raw31862step1 := by apply Matrix.ext; change ∀ i j, raw31862step2 i j = -(raw31862step1 i j); unfold raw31862step2 raw31862step1; decide +kernel
      have hl : raw31862step2Labels = raw31862step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31862step2 raw31862step2Labels = mixedMoment B raw31862step3 raw31862step3Labels := by
      have ha : raw31862step3 = raw31862step2 := by apply Matrix.ext; unfold raw31862step3 raw31862step2; decide +kernel
      have hl : raw31862step2Labels = labelEmbedding1 ∘ raw31862step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31862step2 raw31862step2Labels raw31862step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1570 node1570Labels := by rfl

def raw31863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31863Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31863step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw31863step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw31863step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31863step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw31863step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31863 raw31863Labels = mixedMoment B node1851 node1851Labels := by
  calc
    mixedMoment B raw31863 raw31863Labels = mixedMoment B raw31863step0 raw31863step0Labels := by
      have hz : ∀ j, raw31863 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31863step0 = (fun i j => raw31863 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31863step0 raw31863; decide +kernel
      have hl : raw31863step0Labels = raw31863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31863 raw31863Labels permutation434 hz
    mixedMoment B raw31863step0 raw31863step0Labels = mixedMoment B raw31863step1 raw31863step1Labels := by
      have ha : raw31863step1 = (fun i j => raw31863step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31863step1 raw31863step0; decide +kernel
      have hl : raw31863step1Labels = raw31863step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31863step0 raw31863step0Labels permutation33 permutation7
    mixedMoment B raw31863step1 raw31863step1Labels = mixedMoment B raw31863step2 raw31863step2Labels := by
      have ha : raw31863step2 = -raw31863step1 := by apply Matrix.ext; change ∀ i j, raw31863step2 i j = -(raw31863step1 i j); unfold raw31863step2 raw31863step1; decide +kernel
      have hl : raw31863step2Labels = raw31863step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31863step2 raw31863step2Labels = mixedMoment B raw31863step3 raw31863step3Labels := by
      have ha : raw31863step3 = raw31863step2 := by apply Matrix.ext; unfold raw31863step3 raw31863step2; decide +kernel
      have hl : raw31863step2Labels = labelEmbedding1 ∘ raw31863step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31863step2 raw31863step2Labels raw31863step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1851 node1851Labels := by rfl

def raw31864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31864Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31864step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 2, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw31864step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw31864step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31864step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw31864step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31864 raw31864Labels = mixedMoment B node1939 node1939Labels := by
  calc
    mixedMoment B raw31864 raw31864Labels = mixedMoment B raw31864step0 raw31864step0Labels := by
      have hz : ∀ j, raw31864 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31864step0 = (fun i j => raw31864 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31864step0 raw31864; decide +kernel
      have hl : raw31864step0Labels = raw31864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31864 raw31864Labels permutation434 hz
    mixedMoment B raw31864step0 raw31864step0Labels = mixedMoment B raw31864step1 raw31864step1Labels := by
      have ha : raw31864step1 = (fun i j => raw31864step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31864step1 raw31864step0; decide +kernel
      have hl : raw31864step1Labels = raw31864step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31864step0 raw31864step0Labels permutation33 permutation7
    mixedMoment B raw31864step1 raw31864step1Labels = mixedMoment B raw31864step2 raw31864step2Labels := by
      have ha : raw31864step2 = -raw31864step1 := by apply Matrix.ext; change ∀ i j, raw31864step2 i j = -(raw31864step1 i j); unfold raw31864step2 raw31864step1; decide +kernel
      have hl : raw31864step2Labels = raw31864step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31864step2 raw31864step2Labels = mixedMoment B raw31864step3 raw31864step3Labels := by
      have ha : raw31864step3 = raw31864step2 := by apply Matrix.ext; unfold raw31864step3 raw31864step2; decide +kernel
      have hl : raw31864step2Labels = labelEmbedding1 ∘ raw31864step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31864step2 raw31864step2Labels raw31864step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1939 node1939Labels := by rfl

def raw31865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31865Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw31865step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw31865step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31865step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw31865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31865 raw31865Labels = mixedMoment B node1889 node1889Labels := by
  calc
    mixedMoment B raw31865 raw31865Labels = mixedMoment B raw31865step0 raw31865step0Labels := by
      have ha : raw31865step0 = (fun i j => raw31865 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31865step0 raw31865; decide +kernel
      have hl : raw31865step0Labels = raw31865Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31865 raw31865Labels permutation159 permutation7
    mixedMoment B raw31865step0 raw31865step0Labels = mixedMoment B raw31865step1 raw31865step1Labels := by
      have ha : raw31865step1 = -raw31865step0 := by apply Matrix.ext; change ∀ i j, raw31865step1 i j = -(raw31865step0 i j); unfold raw31865step1 raw31865step0; decide +kernel
      have hl : raw31865step1Labels = raw31865step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31865step1 raw31865step1Labels = mixedMoment B raw31865step2 raw31865step2Labels := by
      have ha : raw31865step2 = raw31865step1 := by apply Matrix.ext; unfold raw31865step2 raw31865step1; decide +kernel
      have hl : raw31865step1Labels = labelEmbedding1 ∘ raw31865step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31865step1 raw31865step1Labels raw31865step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1889 node1889Labels := by rfl

def raw31866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw31866Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw31866step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw31866step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw31866step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31866step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw31866step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31866 raw31866Labels = mixedMoment B node1946 node1946Labels := by
  calc
    mixedMoment B raw31866 raw31866Labels = mixedMoment B raw31866step0 raw31866step0Labels := by
      have hz : ∀ j, raw31866 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31866step0 = (fun i j => raw31866 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31866step0 raw31866; decide +kernel
      have hl : raw31866step0Labels = raw31866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31866 raw31866Labels permutation434 hz
    mixedMoment B raw31866step0 raw31866step0Labels = mixedMoment B raw31866step1 raw31866step1Labels := by
      have ha : raw31866step1 = (fun i j => raw31866step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31866step1 raw31866step0; decide +kernel
      have hl : raw31866step1Labels = raw31866step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31866step0 raw31866step0Labels permutation33 permutation7
    mixedMoment B raw31866step1 raw31866step1Labels = mixedMoment B raw31866step2 raw31866step2Labels := by
      have ha : raw31866step2 = -raw31866step1 := by apply Matrix.ext; change ∀ i j, raw31866step2 i j = -(raw31866step1 i j); unfold raw31866step2 raw31866step1; decide +kernel
      have hl : raw31866step2Labels = raw31866step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31866step2 raw31866step2Labels = mixedMoment B raw31866step3 raw31866step3Labels := by
      have ha : raw31866step3 = raw31866step2 := by apply Matrix.ext; unfold raw31866step3 raw31866step2; decide +kernel
      have hl : raw31866step2Labels = labelEmbedding1 ∘ raw31866step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31866step2 raw31866step2Labels raw31866step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1946 node1946Labels := by rfl

def raw31867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![2, -2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw31867step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31867step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31867step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31867step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31867 raw31867Labels = mixedMoment B node4313 node4313Labels := by
  calc
    mixedMoment B raw31867 raw31867Labels = mixedMoment B raw31867step0 raw31867step0Labels := by
      have hz : ∀ j, raw31867 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31867step0 = (fun i j => raw31867 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31867step0 raw31867; decide +kernel
      have hl : raw31867step0Labels = raw31867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31867 raw31867Labels permutation434 hz
    mixedMoment B raw31867step0 raw31867step0Labels = mixedMoment B raw31867step1 raw31867step1Labels := by
      have ha : raw31867step1 = (fun i j => raw31867step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31867step1 raw31867step0; decide +kernel
      have hl : raw31867step1Labels = raw31867step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31867step0 raw31867step0Labels permutation36 permutation4
    mixedMoment B raw31867step1 raw31867step1Labels = mixedMoment B raw31867step2 raw31867step2Labels := by
      have ha : raw31867step2 = -raw31867step1 := by apply Matrix.ext; change ∀ i j, raw31867step2 i j = -(raw31867step1 i j); unfold raw31867step2 raw31867step1; decide +kernel
      have hl : raw31867step2Labels = raw31867step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31867step2 raw31867step2Labels = mixedMoment B raw31867step3 raw31867step3Labels := by
      have ha : raw31867step3 = raw31867step2 := by apply Matrix.ext; unfold raw31867step3 raw31867step2; decide +kernel
      have hl : raw31867step2Labels = labelEmbedding7 ∘ raw31867step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31867step2 raw31867step2Labels raw31867step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4313 node4313Labels := by rfl

def raw31868 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![2, -2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31868step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw31868step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31868step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31868step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31868step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31868step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31868 raw31868Labels = mixedMoment B node4653 node4653Labels := by
  calc
    mixedMoment B raw31868 raw31868Labels = mixedMoment B raw31868step0 raw31868step0Labels := by
      have hz : ∀ j, raw31868 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31868step0 = (fun i j => raw31868 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31868step0 raw31868; decide +kernel
      have hl : raw31868step0Labels = raw31868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31868 raw31868Labels permutation434 hz
    mixedMoment B raw31868step0 raw31868step0Labels = mixedMoment B raw31868step1 raw31868step1Labels := by
      have ha : raw31868step1 = (fun i j => raw31868step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31868step1 raw31868step0; decide +kernel
      have hl : raw31868step1Labels = raw31868step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31868step0 raw31868step0Labels permutation36 permutation4
    mixedMoment B raw31868step1 raw31868step1Labels = mixedMoment B raw31868step2 raw31868step2Labels := by
      have ha : raw31868step2 = -raw31868step1 := by apply Matrix.ext; change ∀ i j, raw31868step2 i j = -(raw31868step1 i j); unfold raw31868step2 raw31868step1; decide +kernel
      have hl : raw31868step2Labels = raw31868step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31868step2 raw31868step2Labels = mixedMoment B raw31868step3 raw31868step3Labels := by
      have ha : raw31868step3 = raw31868step2 := by apply Matrix.ext; unfold raw31868step3 raw31868step2; decide +kernel
      have hl : raw31868step2Labels = labelEmbedding7 ∘ raw31868step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31868step2 raw31868step2Labels raw31868step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4653 node4653Labels := by rfl

def raw31869 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw31869step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31869step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31869step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31869step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31869step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31869 raw31869Labels = mixedMoment B node4716 node4716Labels := by
  calc
    mixedMoment B raw31869 raw31869Labels = mixedMoment B raw31869step0 raw31869step0Labels := by
      have ha : raw31869step0 = (fun i j => raw31869 (permutation162 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31869step0 raw31869; decide +kernel
      have hl : raw31869step0Labels = raw31869Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31869 raw31869Labels permutation162 permutation4
    mixedMoment B raw31869step0 raw31869step0Labels = mixedMoment B raw31869step1 raw31869step1Labels := by
      have ha : raw31869step1 = -raw31869step0 := by apply Matrix.ext; change ∀ i j, raw31869step1 i j = -(raw31869step0 i j); unfold raw31869step1 raw31869step0; decide +kernel
      have hl : raw31869step1Labels = raw31869step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31869step1 raw31869step1Labels = mixedMoment B raw31869step2 raw31869step2Labels := by
      have ha : raw31869step2 = raw31869step1 := by apply Matrix.ext; unfold raw31869step2 raw31869step1; decide +kernel
      have hl : raw31869step1Labels = labelEmbedding7 ∘ raw31869step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31869step1 raw31869step1Labels raw31869step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4716 node4716Labels := by rfl

def raw31870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31870step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31870step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31870step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31870step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31870 raw31870Labels = mixedMoment B node4298 node4298Labels := by
  calc
    mixedMoment B raw31870 raw31870Labels = mixedMoment B raw31870step0 raw31870step0Labels := by
      have ha : raw31870step0 = (fun i j => raw31870 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31870step0 raw31870; decide +kernel
      have hl : raw31870step0Labels = raw31870Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31870 raw31870Labels permutation153 permutation4
    mixedMoment B raw31870step0 raw31870step0Labels = mixedMoment B raw31870step1 raw31870step1Labels := by
      have ha : raw31870step1 = -raw31870step0 := by apply Matrix.ext; change ∀ i j, raw31870step1 i j = -(raw31870step0 i j); unfold raw31870step1 raw31870step0; decide +kernel
      have hl : raw31870step1Labels = raw31870step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31870step1 raw31870step1Labels = mixedMoment B raw31870step2 raw31870step2Labels := by
      have ha : raw31870step2 = raw31870step1 := by apply Matrix.ext; unfold raw31870step2 raw31870step1; decide +kernel
      have hl : raw31870step1Labels = labelEmbedding7 ∘ raw31870step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31870step1 raw31870step1Labels raw31870step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4298 node4298Labels := by rfl

def raw31871 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31871step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31871step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31871step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31871step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31871 raw31871Labels = mixedMoment B node4640 node4640Labels := by
  calc
    mixedMoment B raw31871 raw31871Labels = mixedMoment B raw31871step0 raw31871step0Labels := by
      have ha : raw31871step0 = (fun i j => raw31871 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31871step0 raw31871; decide +kernel
      have hl : raw31871step0Labels = raw31871Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31871 raw31871Labels permutation153 permutation4
    mixedMoment B raw31871step0 raw31871step0Labels = mixedMoment B raw31871step1 raw31871step1Labels := by
      have ha : raw31871step1 = -raw31871step0 := by apply Matrix.ext; change ∀ i j, raw31871step1 i j = -(raw31871step0 i j); unfold raw31871step1 raw31871step0; decide +kernel
      have hl : raw31871step1Labels = raw31871step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31871step1 raw31871step1Labels = mixedMoment B raw31871step2 raw31871step2Labels := by
      have ha : raw31871step2 = raw31871step1 := by apply Matrix.ext; unfold raw31871step2 raw31871step1; decide +kernel
      have hl : raw31871step1Labels = labelEmbedding7 ∘ raw31871step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31871step1 raw31871step1Labels raw31871step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4640 node4640Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
