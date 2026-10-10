import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25216Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25216step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25216step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25216step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25216step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25216step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25216 raw25216Labels = mixedMoment B node1734 node1734Labels := by
  calc
    mixedMoment B raw25216 raw25216Labels = mixedMoment B raw25216step0 raw25216step0Labels := by
      have hz : ∀ j, raw25216 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25216step0 = (fun i j => raw25216 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25216step0 raw25216; decide +kernel
      have hl : raw25216step0Labels = raw25216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25216 raw25216Labels permutation346 hz
    mixedMoment B raw25216step0 raw25216step0Labels = mixedMoment B raw25216step1 raw25216step1Labels := by
      have ha : raw25216step1 = (fun i j => raw25216step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25216step1 raw25216step0; decide +kernel
      have hl : raw25216step1Labels = raw25216step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25216step0 raw25216step0Labels permutation44 permutation7
    mixedMoment B raw25216step1 raw25216step1Labels = mixedMoment B raw25216step2 raw25216step2Labels := by
      have ha : raw25216step2 = -raw25216step1 := by apply Matrix.ext; change ∀ i j, raw25216step2 i j = -(raw25216step1 i j); unfold raw25216step2 raw25216step1; decide +kernel
      have hl : raw25216step2Labels = raw25216step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25216step2 raw25216step2Labels = mixedMoment B raw25216step3 raw25216step3Labels := by
      have ha : raw25216step3 = raw25216step2 := by apply Matrix.ext; unfold raw25216step3 raw25216step2; decide +kernel
      have hl : raw25216step2Labels = labelEmbedding1 ∘ raw25216step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25216step2 raw25216step2Labels raw25216step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1734 node1734Labels := by rfl

def raw25217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25217Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25217step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25217step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25217step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25217step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25217step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25217 raw25217Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw25217 raw25217Labels = mixedMoment B raw25217step0 raw25217step0Labels := by
      have ha : raw25217step0 = (fun i j => raw25217 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25217step0 raw25217; decide +kernel
      have hl : raw25217step0Labels = raw25217Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25217 raw25217Labels permutation188 permutation7
    mixedMoment B raw25217step0 raw25217step0Labels = mixedMoment B raw25217step1 raw25217step1Labels := by
      have ha : raw25217step1 = -raw25217step0 := by apply Matrix.ext; change ∀ i j, raw25217step1 i j = -(raw25217step0 i j); unfold raw25217step1 raw25217step0; decide +kernel
      have hl : raw25217step1Labels = raw25217step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25217step1 raw25217step1Labels = mixedMoment B raw25217step2 raw25217step2Labels := by
      have ha : raw25217step2 = raw25217step1 := by apply Matrix.ext; unfold raw25217step2 raw25217step1; decide +kernel
      have hl : raw25217step1Labels = labelEmbedding1 ∘ raw25217step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25217step1 raw25217step1Labels raw25217step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1678 node1678Labels := by rfl

def raw25218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25218Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25218step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw25218step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25218step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25218step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25218step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25218 raw25218Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw25218 raw25218Labels = mixedMoment B raw25218step0 raw25218step0Labels := by
      have hz : ∀ j, raw25218 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25218step0 = (fun i j => raw25218 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25218step0 raw25218; decide +kernel
      have hl : raw25218step0Labels = raw25218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25218 raw25218Labels permutation346 hz
    mixedMoment B raw25218step0 raw25218step0Labels = mixedMoment B raw25218step1 raw25218step1Labels := by
      have ha : raw25218step1 = (fun i j => raw25218step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25218step1 raw25218step0; decide +kernel
      have hl : raw25218step1Labels = raw25218step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25218step0 raw25218step0Labels permutation44 permutation7
    mixedMoment B raw25218step1 raw25218step1Labels = mixedMoment B raw25218step2 raw25218step2Labels := by
      have ha : raw25218step2 = -raw25218step1 := by apply Matrix.ext; change ∀ i j, raw25218step2 i j = -(raw25218step1 i j); unfold raw25218step2 raw25218step1; decide +kernel
      have hl : raw25218step2Labels = raw25218step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25218step2 raw25218step2Labels = mixedMoment B raw25218step3 raw25218step3Labels := by
      have ha : raw25218step3 = raw25218step2 := by apply Matrix.ext; unfold raw25218step3 raw25218step2; decide +kernel
      have hl : raw25218step2Labels = labelEmbedding1 ∘ raw25218step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25218step2 raw25218step2Labels raw25218step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1736 node1736Labels := by rfl

def raw25219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw25219Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw25219step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25219step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25219step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25219step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25219step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25219 raw25219Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw25219 raw25219Labels = mixedMoment B raw25219step0 raw25219step0Labels := by
      have hz : ∀ j, raw25219 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25219step0 = (fun i j => raw25219 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25219step0 raw25219; decide +kernel
      have hl : raw25219step0Labels = raw25219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25219 raw25219Labels permutation346 hz
    mixedMoment B raw25219step0 raw25219step0Labels = mixedMoment B raw25219step1 raw25219step1Labels := by
      have ha : raw25219step1 = (fun i j => raw25219step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25219step1 raw25219step0; decide +kernel
      have hl : raw25219step1Labels = raw25219step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25219step0 raw25219step0Labels permutation44 permutation7
    mixedMoment B raw25219step1 raw25219step1Labels = mixedMoment B raw25219step2 raw25219step2Labels := by
      have ha : raw25219step2 = -raw25219step1 := by apply Matrix.ext; change ∀ i j, raw25219step2 i j = -(raw25219step1 i j); unfold raw25219step2 raw25219step1; decide +kernel
      have hl : raw25219step2Labels = raw25219step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25219step2 raw25219step2Labels = mixedMoment B raw25219step3 raw25219step3Labels := by
      have ha : raw25219step3 = raw25219step2 := by apply Matrix.ext; unfold raw25219step3 raw25219step2; decide +kernel
      have hl : raw25219step2Labels = labelEmbedding1 ∘ raw25219step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25219step2 raw25219step2Labels raw25219step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

def raw25220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25220Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25220step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw25220step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw25220step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25220step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw25220step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25220 raw25220Labels = mixedMoment B node1514 node1514Labels := by
  calc
    mixedMoment B raw25220 raw25220Labels = mixedMoment B raw25220step0 raw25220step0Labels := by
      have hz : ∀ j, raw25220 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25220step0 = (fun i j => raw25220 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25220step0 raw25220; decide +kernel
      have hl : raw25220step0Labels = raw25220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25220 raw25220Labels permutation346 hz
    mixedMoment B raw25220step0 raw25220step0Labels = mixedMoment B raw25220step1 raw25220step1Labels := by
      have ha : raw25220step1 = (fun i j => raw25220step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25220step1 raw25220step0; decide +kernel
      have hl : raw25220step1Labels = raw25220step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25220step0 raw25220step0Labels permutation44 permutation7
    mixedMoment B raw25220step1 raw25220step1Labels = mixedMoment B raw25220step2 raw25220step2Labels := by
      have ha : raw25220step2 = -raw25220step1 := by apply Matrix.ext; change ∀ i j, raw25220step2 i j = -(raw25220step1 i j); unfold raw25220step2 raw25220step1; decide +kernel
      have hl : raw25220step2Labels = raw25220step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25220step2 raw25220step2Labels = mixedMoment B raw25220step3 raw25220step3Labels := by
      have ha : raw25220step3 = raw25220step2 := by apply Matrix.ext; unfold raw25220step3 raw25220step2; decide +kernel
      have hl : raw25220step2Labels = labelEmbedding1 ∘ raw25220step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25220step2 raw25220step2Labels raw25220step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1514 node1514Labels := by rfl

def raw25221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25221Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25221step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw25221step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25221step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw25221step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25221step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw25221step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25221 raw25221Labels = mixedMoment B node1720 node1720Labels := by
  calc
    mixedMoment B raw25221 raw25221Labels = mixedMoment B raw25221step0 raw25221step0Labels := by
      have hz : ∀ j, raw25221 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25221step0 = (fun i j => raw25221 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25221step0 raw25221; decide +kernel
      have hl : raw25221step0Labels = raw25221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25221 raw25221Labels permutation346 hz
    mixedMoment B raw25221step0 raw25221step0Labels = mixedMoment B raw25221step1 raw25221step1Labels := by
      have ha : raw25221step1 = (fun i j => raw25221step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25221step1 raw25221step0; decide +kernel
      have hl : raw25221step1Labels = raw25221step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25221step0 raw25221step0Labels permutation44 permutation7
    mixedMoment B raw25221step1 raw25221step1Labels = mixedMoment B raw25221step2 raw25221step2Labels := by
      have ha : raw25221step2 = -raw25221step1 := by apply Matrix.ext; change ∀ i j, raw25221step2 i j = -(raw25221step1 i j); unfold raw25221step2 raw25221step1; decide +kernel
      have hl : raw25221step2Labels = raw25221step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25221step2 raw25221step2Labels = mixedMoment B raw25221step3 raw25221step3Labels := by
      have ha : raw25221step3 = raw25221step2 := by apply Matrix.ext; unfold raw25221step3 raw25221step2; decide +kernel
      have hl : raw25221step2Labels = labelEmbedding1 ∘ raw25221step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25221step2 raw25221step2Labels raw25221step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1720 node1720Labels := by rfl

def raw25222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25222Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw25222step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25222step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw25222step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25222step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw25222step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25222 raw25222Labels = mixedMoment B node1670 node1670Labels := by
  calc
    mixedMoment B raw25222 raw25222Labels = mixedMoment B raw25222step0 raw25222step0Labels := by
      have ha : raw25222step0 = (fun i j => raw25222 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25222step0 raw25222; decide +kernel
      have hl : raw25222step0Labels = raw25222Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25222 raw25222Labels permutation188 permutation7
    mixedMoment B raw25222step0 raw25222step0Labels = mixedMoment B raw25222step1 raw25222step1Labels := by
      have ha : raw25222step1 = -raw25222step0 := by apply Matrix.ext; change ∀ i j, raw25222step1 i j = -(raw25222step0 i j); unfold raw25222step1 raw25222step0; decide +kernel
      have hl : raw25222step1Labels = raw25222step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25222step1 raw25222step1Labels = mixedMoment B raw25222step2 raw25222step2Labels := by
      have ha : raw25222step2 = raw25222step1 := by apply Matrix.ext; unfold raw25222step2 raw25222step1; decide +kernel
      have hl : raw25222step1Labels = labelEmbedding1 ∘ raw25222step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25222step1 raw25222step1Labels raw25222step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1670 node1670Labels := by rfl

def raw25223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25223Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25223step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw25223step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25223step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25223step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25223step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25223 raw25223Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw25223 raw25223Labels = mixedMoment B raw25223step0 raw25223step0Labels := by
      have hz : ∀ j, raw25223 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25223step0 = (fun i j => raw25223 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25223step0 raw25223; decide +kernel
      have hl : raw25223step0Labels = raw25223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25223 raw25223Labels permutation346 hz
    mixedMoment B raw25223step0 raw25223step0Labels = mixedMoment B raw25223step1 raw25223step1Labels := by
      have ha : raw25223step1 = (fun i j => raw25223step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25223step1 raw25223step0; decide +kernel
      have hl : raw25223step1Labels = raw25223step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25223step0 raw25223step0Labels permutation44 permutation7
    mixedMoment B raw25223step1 raw25223step1Labels = mixedMoment B raw25223step2 raw25223step2Labels := by
      have ha : raw25223step2 = -raw25223step1 := by apply Matrix.ext; change ∀ i j, raw25223step2 i j = -(raw25223step1 i j); unfold raw25223step2 raw25223step1; decide +kernel
      have hl : raw25223step2Labels = raw25223step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25223step2 raw25223step2Labels = mixedMoment B raw25223step3 raw25223step3Labels := by
      have ha : raw25223step3 = raw25223step2 := by apply Matrix.ext; unfold raw25223step3 raw25223step2; decide +kernel
      have hl : raw25223step2Labels = labelEmbedding1 ∘ raw25223step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25223step2 raw25223step2Labels raw25223step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1723 node1723Labels := by rfl

def raw25224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw25224Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25224step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25224step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25224step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw25224step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25224step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw25224step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25224step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw25224step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25224 raw25224Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw25224 raw25224Labels = mixedMoment B raw25224step0 raw25224step0Labels := by
      have hz : ∀ j, raw25224 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25224step0 = (fun i j => raw25224 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25224step0 raw25224; decide +kernel
      have hl : raw25224step0Labels = raw25224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25224 raw25224Labels permutation520 hz
    mixedMoment B raw25224step0 raw25224step0Labels = mixedMoment B raw25224step1 raw25224step1Labels := by
      have hz : ∀ j, raw25224step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25224step1 = (fun i j => raw25224step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25224step1 raw25224step0; decide +kernel
      have hl : raw25224step1Labels = raw25224step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25224step0 raw25224step0Labels permutation80 hz
    mixedMoment B raw25224step1 raw25224step1Labels = mixedMoment B raw25224step2 raw25224step2Labels := by
      have ha : raw25224step2 = (fun i j => raw25224step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25224step2 raw25224step1; decide +kernel
      have hl : raw25224step2Labels = raw25224step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25224step1 raw25224step1Labels permutation8 permutation7
    mixedMoment B raw25224step2 raw25224step2Labels = mixedMoment B raw25224step3 raw25224step3Labels := by
      have ha : raw25224step3 = -raw25224step2 := by apply Matrix.ext; change ∀ i j, raw25224step3 i j = -(raw25224step2 i j); unfold raw25224step3 raw25224step2; decide +kernel
      have hl : raw25224step3Labels = raw25224step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25224step3 raw25224step3Labels = mixedMoment B raw25224step4 raw25224step4Labels := by
      have ha : raw25224step4 = raw25224step3 := by apply Matrix.ext; unfold raw25224step4 raw25224step3; decide +kernel
      have hl : raw25224step3Labels = labelEmbedding1 ∘ raw25224step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25224step3 raw25224step3Labels raw25224step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

def raw25225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25225step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25225 raw25225Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw25225 raw25225Labels = mixedMoment B raw25225step0 raw25225step0Labels := by
      have hz : ∀ j, raw25225 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25225step0 = (fun i j => raw25225 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25225step0 raw25225; decide +kernel
      have hl : raw25225step0Labels = raw25225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25225 raw25225Labels permutation346 hz
    mixedMoment B raw25225step0 raw25225step0Labels = mixedMoment B raw25225step1 raw25225step1Labels := by
      have ha : raw25225step1 = (fun i j => raw25225step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25225step1 raw25225step0; decide +kernel
      have hl : raw25225step1Labels = raw25225step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25225step0 raw25225step0Labels permutation34 permutation2
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw25226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25226step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25226 raw25226Labels = mixedMoment B node603 node603Labels := by
  calc
    mixedMoment B raw25226 raw25226Labels = mixedMoment B raw25226step0 raw25226step0Labels := by
      have hz : ∀ j, raw25226 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25226step0 = (fun i j => raw25226 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25226step0 raw25226; decide +kernel
      have hl : raw25226step0Labels = raw25226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25226 raw25226Labels permutation346 hz
    mixedMoment B raw25226step0 raw25226step0Labels = mixedMoment B raw25226step1 raw25226step1Labels := by
      have ha : raw25226step1 = (fun i j => raw25226step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25226step1 raw25226step0; decide +kernel
      have hl : raw25226step1Labels = raw25226step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25226step0 raw25226step0Labels permutation44 permutation2
    _ = mixedMoment B node603 node603Labels := by rfl

def raw25227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25227 raw25227Labels = mixedMoment B node578 node578Labels := by
  calc
    mixedMoment B raw25227 raw25227Labels = mixedMoment B raw25227step0 raw25227step0Labels := by
      have ha : raw25227step0 = (fun i j => raw25227 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25227step0 raw25227; decide +kernel
      have hl : raw25227step0Labels = raw25227Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25227 raw25227Labels permutation154 permutation2
    _ = mixedMoment B node578 node578Labels := by rfl

def raw25228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25228step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25228 raw25228Labels = mixedMoment B node583 node583Labels := by
  calc
    mixedMoment B raw25228 raw25228Labels = mixedMoment B raw25228step0 raw25228step0Labels := by
      have hz : ∀ j, raw25228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25228step0 = (fun i j => raw25228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25228step0 raw25228; decide +kernel
      have hl : raw25228step0Labels = raw25228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25228 raw25228Labels permutation346 hz
    mixedMoment B raw25228step0 raw25228step0Labels = mixedMoment B raw25228step1 raw25228step1Labels := by
      have ha : raw25228step1 = (fun i j => raw25228step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25228step1 raw25228step0; decide +kernel
      have hl : raw25228step1Labels = raw25228step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25228step0 raw25228step0Labels permutation34 permutation2
    _ = mixedMoment B node583 node583Labels := by rfl

def raw25229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25229step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25229 raw25229Labels = mixedMoment B node586 node586Labels := by
  calc
    mixedMoment B raw25229 raw25229Labels = mixedMoment B raw25229step0 raw25229step0Labels := by
      have hz : ∀ j, raw25229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25229step0 = (fun i j => raw25229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25229step0 raw25229; decide +kernel
      have hl : raw25229step0Labels = raw25229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25229 raw25229Labels permutation346 hz
    _ = mixedMoment B node586 node586Labels := by rfl

def raw25230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25230step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25230 raw25230Labels = mixedMoment B node581 node581Labels := by
  calc
    mixedMoment B raw25230 raw25230Labels = mixedMoment B raw25230step0 raw25230step0Labels := by
      have hz : ∀ j, raw25230 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25230step0 = (fun i j => raw25230 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25230step0 raw25230; decide +kernel
      have hl : raw25230step0Labels = raw25230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25230 raw25230Labels permutation346 hz
    mixedMoment B raw25230step0 raw25230step0Labels = mixedMoment B raw25230step1 raw25230step1Labels := by
      have ha : raw25230step1 = (fun i j => raw25230step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25230step1 raw25230step0; decide +kernel
      have hl : raw25230step1Labels = raw25230step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25230step0 raw25230step0Labels permutation34 permutation2
    _ = mixedMoment B node581 node581Labels := by rfl

def raw25231 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![0, 0], ![1, -1]]
def raw25231Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25231step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]
def raw25231step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25231step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw25231step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical25231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25231 raw25231Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw25231 raw25231Labels = mixedMoment B raw25231step0 raw25231step0Labels := by
      have hz : ∀ j, raw25231 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25231step0 = (fun i j => raw25231 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25231step0 raw25231; decide +kernel
      have hl : raw25231step0Labels = raw25231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25231 raw25231Labels permutation520 hz
    mixedMoment B raw25231step0 raw25231step0Labels = mixedMoment B raw25231step1 raw25231step1Labels := by
      have hz : ∀ j, raw25231step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25231step1 = (fun i j => raw25231step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25231step1 raw25231step0; decide +kernel
      have hl : raw25231step1Labels = raw25231step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25231step0 raw25231step0Labels permutation80 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw25232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25232Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25232step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25232 raw25232Labels = mixedMoment B node922 node922Labels := by
  calc
    mixedMoment B raw25232 raw25232Labels = mixedMoment B raw25232step0 raw25232step0Labels := by
      have ha : raw25232step0 = (fun i j => raw25232 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25232step0 raw25232; decide +kernel
      have hl : raw25232step0Labels = raw25232Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25232 raw25232Labels permutation188 permutation2
    _ = mixedMoment B node922 node922Labels := by rfl

def raw25233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25233Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25233step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25233step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25233 raw25233Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw25233 raw25233Labels = mixedMoment B raw25233step0 raw25233step0Labels := by
      have hz : ∀ j, raw25233 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25233step0 = (fun i j => raw25233 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25233step0 raw25233; decide +kernel
      have hl : raw25233step0Labels = raw25233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25233 raw25233Labels permutation346 hz
    mixedMoment B raw25233step0 raw25233step0Labels = mixedMoment B raw25233step1 raw25233step1Labels := by
      have ha : raw25233step1 = (fun i j => raw25233step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25233step1 raw25233step0; decide +kernel
      have hl : raw25233step1Labels = raw25233step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25233step0 raw25233step0Labels permutation40 permutation2
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw25234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25234Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25234step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25234step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25234 raw25234Labels = mixedMoment B node1086 node1086Labels := by
  calc
    mixedMoment B raw25234 raw25234Labels = mixedMoment B raw25234step0 raw25234step0Labels := by
      have hz : ∀ j, raw25234 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25234step0 = (fun i j => raw25234 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25234step0 raw25234; decide +kernel
      have hl : raw25234step0Labels = raw25234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25234 raw25234Labels permutation520 hz
    mixedMoment B raw25234step0 raw25234step0Labels = mixedMoment B raw25234step1 raw25234step1Labels := by
      have hz : ∀ j, raw25234step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25234step1 = (fun i j => raw25234step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25234step1 raw25234step0; decide +kernel
      have hl : raw25234step1Labels = raw25234step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25234step0 raw25234step0Labels permutation80 hz
    _ = mixedMoment B node1086 node1086Labels := by rfl

def raw25235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25235Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25235step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25235step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25235 raw25235Labels = mixedMoment B node1081 node1081Labels := by
  calc
    mixedMoment B raw25235 raw25235Labels = mixedMoment B raw25235step0 raw25235step0Labels := by
      have hz : ∀ j, raw25235 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25235step0 = (fun i j => raw25235 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25235step0 raw25235; decide +kernel
      have hl : raw25235step0Labels = raw25235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25235 raw25235Labels permutation346 hz
    mixedMoment B raw25235step0 raw25235step0Labels = mixedMoment B raw25235step1 raw25235step1Labels := by
      have ha : raw25235step1 = (fun i j => raw25235step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25235step1 raw25235step0; decide +kernel
      have hl : raw25235step1Labels = raw25235step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25235step0 raw25235step0Labels permutation44 permutation2
    _ = mixedMoment B node1081 node1081Labels := by rfl

def raw25236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25236Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25236step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25236step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25236 raw25236Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw25236 raw25236Labels = mixedMoment B raw25236step0 raw25236step0Labels := by
      have hz : ∀ j, raw25236 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25236step0 = (fun i j => raw25236 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25236step0 raw25236; decide +kernel
      have hl : raw25236step0Labels = raw25236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25236 raw25236Labels permutation346 hz
    mixedMoment B raw25236step0 raw25236step0Labels = mixedMoment B raw25236step1 raw25236step1Labels := by
      have ha : raw25236step1 = (fun i j => raw25236step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25236step1 raw25236step0; decide +kernel
      have hl : raw25236step1Labels = raw25236step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25236step0 raw25236step0Labels permutation34 permutation2
    _ = mixedMoment B node2107 node2107Labels := by rfl

def raw25237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25237Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25237step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25237 raw25237Labels = mixedMoment B node942 node942Labels := by
  calc
    mixedMoment B raw25237 raw25237Labels = mixedMoment B raw25237step0 raw25237step0Labels := by
      have ha : raw25237step0 = (fun i j => raw25237 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25237step0 raw25237; decide +kernel
      have hl : raw25237step0Labels = raw25237Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25237 raw25237Labels permutation154 permutation2
    _ = mixedMoment B node942 node942Labels := by rfl

def raw25238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25238Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25238step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25238 raw25238Labels = mixedMoment B node947 node947Labels := by
  calc
    mixedMoment B raw25238 raw25238Labels = mixedMoment B raw25238step0 raw25238step0Labels := by
      have hz : ∀ j, raw25238 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25238step0 = (fun i j => raw25238 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25238step0 raw25238; decide +kernel
      have hl : raw25238step0Labels = raw25238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25238 raw25238Labels permutation346 hz
    mixedMoment B raw25238step0 raw25238step0Labels = mixedMoment B raw25238step1 raw25238step1Labels := by
      have ha : raw25238step1 = (fun i j => raw25238step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25238step1 raw25238step0; decide +kernel
      have hl : raw25238step1Labels = raw25238step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25238step0 raw25238step0Labels permutation34 permutation2
    _ = mixedMoment B node947 node947Labels := by rfl

def raw25239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25239Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25239step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25239 raw25239Labels = mixedMoment B node950 node950Labels := by
  calc
    mixedMoment B raw25239 raw25239Labels = mixedMoment B raw25239step0 raw25239step0Labels := by
      have hz : ∀ j, raw25239 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25239step0 = (fun i j => raw25239 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25239step0 raw25239; decide +kernel
      have hl : raw25239step0Labels = raw25239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25239 raw25239Labels permutation346 hz
    _ = mixedMoment B node950 node950Labels := by rfl

def raw25240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25240Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25240step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25240 raw25240Labels = mixedMoment B node945 node945Labels := by
  calc
    mixedMoment B raw25240 raw25240Labels = mixedMoment B raw25240step0 raw25240step0Labels := by
      have hz : ∀ j, raw25240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25240step0 = (fun i j => raw25240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25240step0 raw25240; decide +kernel
      have hl : raw25240step0Labels = raw25240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25240 raw25240Labels permutation346 hz
    mixedMoment B raw25240step0 raw25240step0Labels = mixedMoment B raw25240step1 raw25240step1Labels := by
      have ha : raw25240step1 = (fun i j => raw25240step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25240step1 raw25240step0; decide +kernel
      have hl : raw25240step1Labels = raw25240step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25240step0 raw25240step0Labels permutation34 permutation2
    _ = mixedMoment B node945 node945Labels := by rfl

def raw25241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25241step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25241step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25241 raw25241Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw25241 raw25241Labels = mixedMoment B raw25241step0 raw25241step0Labels := by
      have ha : raw25241step0 = (fun i j => raw25241 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25241step0 raw25241; decide +kernel
      have hl : raw25241step0Labels = raw25241Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25241 raw25241Labels permutation178 permutation3
    mixedMoment B raw25241step0 raw25241step0Labels = mixedMoment B raw25241step1 raw25241step1Labels := by
      have ha : raw25241step1 = raw25241step0 := by apply Matrix.ext; unfold raw25241step1 raw25241step0; decide +kernel
      have hl : raw25241step0Labels = labelEmbedding6 ∘ raw25241step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25241step0 raw25241step0Labels raw25241step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw25242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25242step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25242step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25242step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25242 raw25242Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw25242 raw25242Labels = mixedMoment B raw25242step0 raw25242step0Labels := by
      have hz : ∀ j, raw25242 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25242step0 = (fun i j => raw25242 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25242step0 raw25242; decide +kernel
      have hl : raw25242step0Labels = raw25242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25242 raw25242Labels permutation346 hz
    mixedMoment B raw25242step0 raw25242step0Labels = mixedMoment B raw25242step1 raw25242step1Labels := by
      have ha : raw25242step1 = (fun i j => raw25242step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25242step1 raw25242step0; decide +kernel
      have hl : raw25242step1Labels = raw25242step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25242step0 raw25242step0Labels permutation35 permutation3
    mixedMoment B raw25242step1 raw25242step1Labels = mixedMoment B raw25242step2 raw25242step2Labels := by
      have ha : raw25242step2 = raw25242step1 := by apply Matrix.ext; unfold raw25242step2 raw25242step1; decide +kernel
      have hl : raw25242step1Labels = labelEmbedding6 ∘ raw25242step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25242step1 raw25242step1Labels raw25242step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw25243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25243step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25243step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25243 raw25243Labels = mixedMoment B node4119 node4119Labels := by
  calc
    mixedMoment B raw25243 raw25243Labels = mixedMoment B raw25243step0 raw25243step0Labels := by
      have hz : ∀ j, raw25243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25243step0 = (fun i j => raw25243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25243step0 raw25243; decide +kernel
      have hl : raw25243step0Labels = raw25243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25243 raw25243Labels permutation346 hz
    mixedMoment B raw25243step0 raw25243step0Labels = mixedMoment B raw25243step1 raw25243step1Labels := by
      have ha : raw25243step1 = (fun i j => raw25243step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25243step1 raw25243step0; decide +kernel
      have hl : raw25243step1Labels = raw25243step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25243step0 raw25243step0Labels permutation46 permutation3
    mixedMoment B raw25243step1 raw25243step1Labels = mixedMoment B raw25243step2 raw25243step2Labels := by
      have ha : raw25243step2 = raw25243step1 := by apply Matrix.ext; unfold raw25243step2 raw25243step1; decide +kernel
      have hl : raw25243step1Labels = labelEmbedding6 ∘ raw25243step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25243step1 raw25243step1Labels raw25243step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4119 node4119Labels := by rfl

def raw25244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25244step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25244step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25244 raw25244Labels = mixedMoment B node4301 node4301Labels := by
  calc
    mixedMoment B raw25244 raw25244Labels = mixedMoment B raw25244step0 raw25244step0Labels := by
      have ha : raw25244step0 = (fun i j => raw25244 (permutation190 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25244step0 raw25244; decide +kernel
      have hl : raw25244step0Labels = raw25244Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25244 raw25244Labels permutation190 permutation3
    mixedMoment B raw25244step0 raw25244step0Labels = mixedMoment B raw25244step1 raw25244step1Labels := by
      have ha : raw25244step1 = raw25244step0 := by apply Matrix.ext; unfold raw25244step1 raw25244step0; decide +kernel
      have hl : raw25244step0Labels = labelEmbedding6 ∘ raw25244step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25244step0 raw25244step0Labels raw25244step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4301 node4301Labels := by rfl

def raw25245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25245step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25245step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25245step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25245 raw25245Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw25245 raw25245Labels = mixedMoment B raw25245step0 raw25245step0Labels := by
      have hz : ∀ j, raw25245 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25245step0 = (fun i j => raw25245 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25245step0 raw25245; decide +kernel
      have hl : raw25245step0Labels = raw25245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25245 raw25245Labels permutation346 hz
    mixedMoment B raw25245step0 raw25245step0Labels = mixedMoment B raw25245step1 raw25245step1Labels := by
      have ha : raw25245step1 = (fun i j => raw25245step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25245step1 raw25245step0; decide +kernel
      have hl : raw25245step1Labels = raw25245step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25245step0 raw25245step0Labels permutation46 permutation3
    mixedMoment B raw25245step1 raw25245step1Labels = mixedMoment B raw25245step2 raw25245step2Labels := by
      have ha : raw25245step2 = raw25245step1 := by apply Matrix.ext; unfold raw25245step2 raw25245step1; decide +kernel
      have hl : raw25245step1Labels = labelEmbedding6 ∘ raw25245step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25245step1 raw25245step1Labels raw25245step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

def raw25246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25246step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25246step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25246step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25246 raw25246Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw25246 raw25246Labels = mixedMoment B raw25246step0 raw25246step0Labels := by
      have hz : ∀ j, raw25246 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25246step0 = (fun i j => raw25246 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25246step0 raw25246; decide +kernel
      have hl : raw25246step0Labels = raw25246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25246 raw25246Labels permutation346 hz
    mixedMoment B raw25246step0 raw25246step0Labels = mixedMoment B raw25246step1 raw25246step1Labels := by
      have ha : raw25246step1 = (fun i j => raw25246step0 (permutation49 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25246step1 raw25246step0; decide +kernel
      have hl : raw25246step1Labels = raw25246step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25246step0 raw25246step0Labels permutation49 permutation3
    mixedMoment B raw25246step1 raw25246step1Labels = mixedMoment B raw25246step2 raw25246step2Labels := by
      have ha : raw25246step2 = raw25246step1 := by apply Matrix.ext; unfold raw25246step2 raw25246step1; decide +kernel
      have hl : raw25246step1Labels = labelEmbedding6 ∘ raw25246step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25246step1 raw25246step1Labels raw25246step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw25247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25247step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25247 raw25247Labels = mixedMoment B node4100 node4100Labels := by
  calc
    mixedMoment B raw25247 raw25247Labels = mixedMoment B raw25247step0 raw25247step0Labels := by
      have ha : raw25247step0 = (fun i j => raw25247 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25247step0 raw25247; decide +kernel
      have hl : raw25247step0Labels = raw25247Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25247 raw25247Labels permutation164 permutation3
    mixedMoment B raw25247step0 raw25247step0Labels = mixedMoment B raw25247step1 raw25247step1Labels := by
      have ha : raw25247step1 = raw25247step0 := by apply Matrix.ext; unfold raw25247step1 raw25247step0; decide +kernel
      have hl : raw25247step0Labels = labelEmbedding6 ∘ raw25247step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25247step0 raw25247step0Labels raw25247step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4100 node4100Labels := by rfl

def raw25248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25248step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25248step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25248 raw25248Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw25248 raw25248Labels = mixedMoment B raw25248step0 raw25248step0Labels := by
      have ha : raw25248step0 = (fun i j => raw25248 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25248step0 raw25248; decide +kernel
      have hl : raw25248step0Labels = raw25248Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25248 raw25248Labels permutation164 permutation3
    mixedMoment B raw25248step0 raw25248step0Labels = mixedMoment B raw25248step1 raw25248step1Labels := by
      have ha : raw25248step1 = raw25248step0 := by apply Matrix.ext; unfold raw25248step1 raw25248step0; decide +kernel
      have hl : raw25248step0Labels = labelEmbedding6 ∘ raw25248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25248step0 raw25248step0Labels raw25248step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4344 node4344Labels := by rfl

def raw25249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25249step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25249 raw25249Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw25249 raw25249Labels = mixedMoment B raw25249step0 raw25249step0Labels := by
      have ha : raw25249step0 = (fun i j => raw25249 (permutation224 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25249step0 raw25249; decide +kernel
      have hl : raw25249step0Labels = raw25249Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25249 raw25249Labels permutation224 permutation3
    mixedMoment B raw25249step0 raw25249step0Labels = mixedMoment B raw25249step1 raw25249step1Labels := by
      have ha : raw25249step1 = raw25249step0 := by apply Matrix.ext; unfold raw25249step1 raw25249step0; decide +kernel
      have hl : raw25249step0Labels = labelEmbedding6 ∘ raw25249step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25249step0 raw25249step0Labels raw25249step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4399 node4399Labels := by rfl

def raw25250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25250step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25250step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25250 raw25250Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw25250 raw25250Labels = mixedMoment B raw25250step0 raw25250step0Labels := by
      have ha : raw25250step0 = (fun i j => raw25250 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25250step0 raw25250; decide +kernel
      have hl : raw25250step0Labels = raw25250Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25250 raw25250Labels permutation168 permutation3
    mixedMoment B raw25250step0 raw25250step0Labels = mixedMoment B raw25250step1 raw25250step1Labels := by
      have ha : raw25250step1 = raw25250step0 := by apply Matrix.ext; unfold raw25250step1 raw25250step0; decide +kernel
      have hl : raw25250step0Labels = labelEmbedding6 ∘ raw25250step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25250step0 raw25250step0Labels raw25250step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw25251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25251step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25251step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25251step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25251 raw25251Labels = mixedMoment B node4102 node4102Labels := by
  calc
    mixedMoment B raw25251 raw25251Labels = mixedMoment B raw25251step0 raw25251step0Labels := by
      have hz : ∀ j, raw25251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25251step0 = (fun i j => raw25251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25251step0 raw25251; decide +kernel
      have hl : raw25251step0Labels = raw25251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25251 raw25251Labels permutation346 hz
    mixedMoment B raw25251step0 raw25251step0Labels = mixedMoment B raw25251step1 raw25251step1Labels := by
      have ha : raw25251step1 = (fun i j => raw25251step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25251step1 raw25251step0; decide +kernel
      have hl : raw25251step1Labels = raw25251step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25251step0 raw25251step0Labels permutation35 permutation3
    mixedMoment B raw25251step1 raw25251step1Labels = mixedMoment B raw25251step2 raw25251step2Labels := by
      have ha : raw25251step2 = raw25251step1 := by apply Matrix.ext; unfold raw25251step2 raw25251step1; decide +kernel
      have hl : raw25251step1Labels = labelEmbedding6 ∘ raw25251step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25251step1 raw25251step1Labels raw25251step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4102 node4102Labels := by rfl

def raw25252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25252step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25252 raw25252Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw25252 raw25252Labels = mixedMoment B raw25252step0 raw25252step0Labels := by
      have hz : ∀ j, raw25252 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25252step0 = (fun i j => raw25252 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25252step0 raw25252; decide +kernel
      have hl : raw25252step0Labels = raw25252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25252 raw25252Labels permutation346 hz
    mixedMoment B raw25252step0 raw25252step0Labels = mixedMoment B raw25252step1 raw25252step1Labels := by
      have ha : raw25252step1 = (fun i j => raw25252step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25252step1 raw25252step0; decide +kernel
      have hl : raw25252step1Labels = raw25252step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25252step0 raw25252step0Labels permutation35 permutation3
    mixedMoment B raw25252step1 raw25252step1Labels = mixedMoment B raw25252step2 raw25252step2Labels := by
      have ha : raw25252step2 = raw25252step1 := by apply Matrix.ext; unfold raw25252step2 raw25252step1; decide +kernel
      have hl : raw25252step1Labels = labelEmbedding6 ∘ raw25252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25252step1 raw25252step1Labels raw25252step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4349 node4349Labels := by rfl

def raw25253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25253step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25253step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25253 raw25253Labels = mixedMoment B node4288 node4288Labels := by
  calc
    mixedMoment B raw25253 raw25253Labels = mixedMoment B raw25253step0 raw25253step0Labels := by
      have ha : raw25253step0 = (fun i j => raw25253 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25253step0 raw25253; decide +kernel
      have hl : raw25253step0Labels = raw25253Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25253 raw25253Labels permutation179 permutation3
    mixedMoment B raw25253step0 raw25253step0Labels = mixedMoment B raw25253step1 raw25253step1Labels := by
      have ha : raw25253step1 = raw25253step0 := by apply Matrix.ext; unfold raw25253step1 raw25253step0; decide +kernel
      have hl : raw25253step0Labels = labelEmbedding6 ∘ raw25253step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25253step0 raw25253step0Labels raw25253step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4288 node4288Labels := by rfl

def raw25254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25254step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25254step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25254 raw25254Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw25254 raw25254Labels = mixedMoment B raw25254step0 raw25254step0Labels := by
      have hz : ∀ j, raw25254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25254step0 = (fun i j => raw25254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25254step0 raw25254; decide +kernel
      have hl : raw25254step0Labels = raw25254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25254 raw25254Labels permutation346 hz
    mixedMoment B raw25254step0 raw25254step0Labels = mixedMoment B raw25254step1 raw25254step1Labels := by
      have ha : raw25254step1 = (fun i j => raw25254step0 (permutation45 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25254step1 raw25254step0; decide +kernel
      have hl : raw25254step1Labels = raw25254step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25254step0 raw25254step0Labels permutation45 permutation3
    mixedMoment B raw25254step1 raw25254step1Labels = mixedMoment B raw25254step2 raw25254step2Labels := by
      have ha : raw25254step2 = raw25254step1 := by apply Matrix.ext; unfold raw25254step2 raw25254step1; decide +kernel
      have hl : raw25254step1Labels = labelEmbedding6 ∘ raw25254step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25254step1 raw25254step1Labels raw25254step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

def raw25255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25255step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25255 raw25255Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw25255 raw25255Labels = mixedMoment B raw25255step0 raw25255step0Labels := by
      have hz : ∀ j, raw25255 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25255step0 = (fun i j => raw25255 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25255step0 raw25255; decide +kernel
      have hl : raw25255step0Labels = raw25255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25255 raw25255Labels permutation346 hz
    mixedMoment B raw25255step0 raw25255step0Labels = mixedMoment B raw25255step1 raw25255step1Labels := by
      have ha : raw25255step1 = (fun i j => raw25255step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25255step1 raw25255step0; decide +kernel
      have hl : raw25255step1Labels = raw25255step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25255step0 raw25255step0Labels permutation35 permutation3
    mixedMoment B raw25255step1 raw25255step1Labels = mixedMoment B raw25255step2 raw25255step2Labels := by
      have ha : raw25255step2 = raw25255step1 := by apply Matrix.ext; unfold raw25255step2 raw25255step1; decide +kernel
      have hl : raw25255step1Labels = labelEmbedding6 ∘ raw25255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25255step1 raw25255step1Labels raw25255step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

def raw25256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25256step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25256 raw25256Labels = mixedMoment B node2595 node2595Labels := by
  calc
    mixedMoment B raw25256 raw25256Labels = mixedMoment B raw25256step0 raw25256step0Labels := by
      have hz : ∀ j, raw25256 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25256step0 = (fun i j => raw25256 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25256step0 raw25256; decide +kernel
      have hl : raw25256step0Labels = raw25256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25256 raw25256Labels permutation346 hz
    mixedMoment B raw25256step0 raw25256step0Labels = mixedMoment B raw25256step1 raw25256step1Labels := by
      have ha : raw25256step1 = (fun i j => raw25256step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25256step1 raw25256step0; decide +kernel
      have hl : raw25256step1Labels = raw25256step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25256step0 raw25256step0Labels permutation34 permutation3
    _ = mixedMoment B node2595 node2595Labels := by rfl

def raw25257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25257Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25257 raw25257Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw25257 raw25257Labels = mixedMoment B raw25257step0 raw25257step0Labels := by
      have ha : raw25257step0 = (fun i j => raw25257 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25257step0 raw25257; decide +kernel
      have hl : raw25257step0Labels = raw25257Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25257 raw25257Labels permutation178 permutation3
    _ = mixedMoment B node2480 node2480Labels := by rfl

def raw25258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25258 raw25258Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw25258 raw25258Labels = mixedMoment B raw25258step0 raw25258step0Labels := by
      have hz : ∀ j, raw25258 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25258step0 = (fun i j => raw25258 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25258step0 raw25258; decide +kernel
      have hl : raw25258step0Labels = raw25258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25258 raw25258Labels permutation346 hz
    mixedMoment B raw25258step0 raw25258step0Labels = mixedMoment B raw25258step1 raw25258step1Labels := by
      have ha : raw25258step1 = (fun i j => raw25258step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25258step1 raw25258step0; decide +kernel
      have hl : raw25258step1Labels = raw25258step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25258step0 raw25258step0Labels permutation35 permutation3
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw25259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25259Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25259step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25259step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25259 raw25259Labels = mixedMoment B node554 node554Labels := by
  calc
    mixedMoment B raw25259 raw25259Labels = mixedMoment B raw25259step0 raw25259step0Labels := by
      have hz : ∀ j, raw25259 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25259step0 = (fun i j => raw25259 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25259step0 raw25259; decide +kernel
      have hl : raw25259step0Labels = raw25259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25259 raw25259Labels permutation346 hz
    mixedMoment B raw25259step0 raw25259step0Labels = mixedMoment B raw25259step1 raw25259step1Labels := by
      have ha : raw25259step1 = (fun i j => raw25259step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25259step1 raw25259step0; decide +kernel
      have hl : raw25259step1Labels = raw25259step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25259step0 raw25259step0Labels permutation46 permutation3
    _ = mixedMoment B node554 node554Labels := by rfl

def raw25260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25260Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25260step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25260 raw25260Labels = mixedMoment B node879 node879Labels := by
  calc
    mixedMoment B raw25260 raw25260Labels = mixedMoment B raw25260step0 raw25260step0Labels := by
      have ha : raw25260step0 = (fun i j => raw25260 (permutation190 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25260step0 raw25260; decide +kernel
      have hl : raw25260step0Labels = raw25260Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25260 raw25260Labels permutation190 permutation3
    _ = mixedMoment B node879 node879Labels := by rfl

def raw25261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25261step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25261step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25261 raw25261Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw25261 raw25261Labels = mixedMoment B raw25261step0 raw25261step0Labels := by
      have hz : ∀ j, raw25261 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25261step0 = (fun i j => raw25261 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25261step0 raw25261; decide +kernel
      have hl : raw25261step0Labels = raw25261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25261 raw25261Labels permutation346 hz
    mixedMoment B raw25261step0 raw25261step0Labels = mixedMoment B raw25261step1 raw25261step1Labels := by
      have ha : raw25261step1 = (fun i j => raw25261step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25261step1 raw25261step0; decide +kernel
      have hl : raw25261step1Labels = raw25261step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25261step0 raw25261step0Labels permutation46 permutation3
    _ = mixedMoment B node1005 node1005Labels := by rfl

def raw25262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25262step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25262step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25262 raw25262Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw25262 raw25262Labels = mixedMoment B raw25262step0 raw25262step0Labels := by
      have hz : ∀ j, raw25262 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25262step0 = (fun i j => raw25262 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25262step0 raw25262; decide +kernel
      have hl : raw25262step0Labels = raw25262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25262 raw25262Labels permutation346 hz
    mixedMoment B raw25262step0 raw25262step0Labels = mixedMoment B raw25262step1 raw25262step1Labels := by
      have ha : raw25262step1 = (fun i j => raw25262step0 (permutation49 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25262step1 raw25262step0; decide +kernel
      have hl : raw25262step1Labels = raw25262step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25262step0 raw25262step0Labels permutation49 permutation3
    _ = mixedMoment B node1079 node1079Labels := by rfl

def raw25263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25263step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25263 raw25263Labels = mixedMoment B node537 node537Labels := by
  calc
    mixedMoment B raw25263 raw25263Labels = mixedMoment B raw25263step0 raw25263step0Labels := by
      have ha : raw25263step0 = (fun i j => raw25263 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25263step0 raw25263; decide +kernel
      have hl : raw25263step0Labels = raw25263Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25263 raw25263Labels permutation164 permutation3
    _ = mixedMoment B node537 node537Labels := by rfl

def raw25264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25264step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25264 raw25264Labels = mixedMoment B node922 node922Labels := by
  calc
    mixedMoment B raw25264 raw25264Labels = mixedMoment B raw25264step0 raw25264step0Labels := by
      have ha : raw25264step0 = (fun i j => raw25264 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25264step0 raw25264; decide +kernel
      have hl : raw25264step0Labels = raw25264Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25264 raw25264Labels permutation164 permutation3
    _ = mixedMoment B node922 node922Labels := by rfl

def raw25265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25265Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25265step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25265 raw25265Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw25265 raw25265Labels = mixedMoment B raw25265step0 raw25265step0Labels := by
      have ha : raw25265step0 = (fun i j => raw25265 (permutation224 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25265step0 raw25265; decide +kernel
      have hl : raw25265step0Labels = raw25265Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25265 raw25265Labels permutation224 permutation3
    _ = mixedMoment B node980 node980Labels := by rfl

def raw25266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25266Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25266step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25266 raw25266Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw25266 raw25266Labels = mixedMoment B raw25266step0 raw25266step0Labels := by
      have ha : raw25266step0 = (fun i j => raw25266 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25266step0 raw25266; decide +kernel
      have hl : raw25266step0Labels = raw25266Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25266 raw25266Labels permutation168 permutation3
    _ = mixedMoment B node1039 node1039Labels := by rfl

def raw25267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25267Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25267step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25267step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25267 raw25267Labels = mixedMoment B node539 node539Labels := by
  calc
    mixedMoment B raw25267 raw25267Labels = mixedMoment B raw25267step0 raw25267step0Labels := by
      have hz : ∀ j, raw25267 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25267step0 = (fun i j => raw25267 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25267step0 raw25267; decide +kernel
      have hl : raw25267step0Labels = raw25267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25267 raw25267Labels permutation346 hz
    mixedMoment B raw25267step0 raw25267step0Labels = mixedMoment B raw25267step1 raw25267step1Labels := by
      have ha : raw25267step1 = (fun i j => raw25267step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25267step1 raw25267step0; decide +kernel
      have hl : raw25267step1Labels = raw25267step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25267step0 raw25267step0Labels permutation35 permutation3
    _ = mixedMoment B node539 node539Labels := by rfl

def raw25268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25268Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25268step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25268step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25268 raw25268Labels = mixedMoment B node927 node927Labels := by
  calc
    mixedMoment B raw25268 raw25268Labels = mixedMoment B raw25268step0 raw25268step0Labels := by
      have hz : ∀ j, raw25268 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25268step0 = (fun i j => raw25268 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25268step0 raw25268; decide +kernel
      have hl : raw25268step0Labels = raw25268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25268 raw25268Labels permutation346 hz
    mixedMoment B raw25268step0 raw25268step0Labels = mixedMoment B raw25268step1 raw25268step1Labels := by
      have ha : raw25268step1 = (fun i j => raw25268step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25268step1 raw25268step0; decide +kernel
      have hl : raw25268step1Labels = raw25268step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25268step0 raw25268step0Labels permutation35 permutation3
    _ = mixedMoment B node927 node927Labels := by rfl

def raw25269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25269Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25269 raw25269Labels = mixedMoment B node866 node866Labels := by
  calc
    mixedMoment B raw25269 raw25269Labels = mixedMoment B raw25269step0 raw25269step0Labels := by
      have ha : raw25269step0 = (fun i j => raw25269 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25269step0 raw25269; decide +kernel
      have hl : raw25269step0Labels = raw25269Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25269 raw25269Labels permutation179 permutation3
    _ = mixedMoment B node866 node866Labels := by rfl

def raw25270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25270Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw25270step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw25270step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25270 raw25270Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw25270 raw25270Labels = mixedMoment B raw25270step0 raw25270step0Labels := by
      have hz : ∀ j, raw25270 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25270step0 = (fun i j => raw25270 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25270step0 raw25270; decide +kernel
      have hl : raw25270step0Labels = raw25270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25270 raw25270Labels permutation346 hz
    mixedMoment B raw25270step0 raw25270step0Labels = mixedMoment B raw25270step1 raw25270step1Labels := by
      have ha : raw25270step1 = (fun i j => raw25270step0 (permutation45 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25270step1 raw25270step0; decide +kernel
      have hl : raw25270step1Labels = raw25270step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25270step0 raw25270step0Labels permutation45 permutation3
    _ = mixedMoment B node985 node985Labels := by rfl

def raw25271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25271Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25271step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25271 raw25271Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw25271 raw25271Labels = mixedMoment B raw25271step0 raw25271step0Labels := by
      have hz : ∀ j, raw25271 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25271step0 = (fun i j => raw25271 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25271step0 raw25271; decide +kernel
      have hl : raw25271step0Labels = raw25271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25271 raw25271Labels permutation346 hz
    mixedMoment B raw25271step0 raw25271step0Labels = mixedMoment B raw25271step1 raw25271step1Labels := by
      have ha : raw25271step1 = (fun i j => raw25271step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25271step1 raw25271step0; decide +kernel
      have hl : raw25271step1Labels = raw25271step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25271step0 raw25271step0Labels permutation35 permutation3
    _ = mixedMoment B node1040 node1040Labels := by rfl

def raw25272 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25272step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25272step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25272 raw25272Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw25272 raw25272Labels = mixedMoment B raw25272step0 raw25272step0Labels := by
      have hz : ∀ j, raw25272 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25272step0 = (fun i j => raw25272 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25272step0 raw25272; decide +kernel
      have hl : raw25272step0Labels = raw25272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25272 raw25272Labels permutation346 hz
    mixedMoment B raw25272step0 raw25272step0Labels = mixedMoment B raw25272step1 raw25272step1Labels := by
      have ha : raw25272step1 = (fun i j => raw25272step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25272step1 raw25272step0; decide +kernel
      have hl : raw25272step1Labels = raw25272step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25272step0 raw25272step0Labels permutation32 permutation7
    mixedMoment B raw25272step1 raw25272step1Labels = mixedMoment B raw25272step2 raw25272step2Labels := by
      have ha : raw25272step2 = raw25272step1 := by apply Matrix.ext; unfold raw25272step2 raw25272step1; decide +kernel
      have hl : raw25272step1Labels = labelEmbedding10 ∘ raw25272step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25272step1 raw25272step1Labels raw25272step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw25273 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw25273step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25273step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25273step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25273step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25273 raw25273Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw25273 raw25273Labels = mixedMoment B raw25273step0 raw25273step0Labels := by
      have hz : ∀ j, raw25273 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25273step0 = (fun i j => raw25273 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25273step0 raw25273; decide +kernel
      have hl : raw25273step0Labels = raw25273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25273 raw25273Labels permutation346 hz
    mixedMoment B raw25273step0 raw25273step0Labels = mixedMoment B raw25273step1 raw25273step1Labels := by
      have ha : raw25273step1 = (fun i j => raw25273step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25273step1 raw25273step0; decide +kernel
      have hl : raw25273step1Labels = raw25273step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25273step0 raw25273step0Labels permutation47 permutation4
    mixedMoment B raw25273step1 raw25273step1Labels = mixedMoment B raw25273step2 raw25273step2Labels := by
      have ha : raw25273step2 = -raw25273step1 := by apply Matrix.ext; change ∀ i j, raw25273step2 i j = -(raw25273step1 i j); unfold raw25273step2 raw25273step1; decide +kernel
      have hl : raw25273step2Labels = raw25273step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25273step2 raw25273step2Labels = mixedMoment B raw25273step3 raw25273step3Labels := by
      have ha : raw25273step3 = raw25273step2 := by apply Matrix.ext; unfold raw25273step3 raw25273step2; decide +kernel
      have hl : raw25273step2Labels = labelEmbedding7 ∘ raw25273step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25273step2 raw25273step2Labels raw25273step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

def raw25274 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25274step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25274 raw25274Labels = mixedMoment B node4407 node4407Labels := by
  calc
    mixedMoment B raw25274 raw25274Labels = mixedMoment B raw25274step0 raw25274step0Labels := by
      have ha : raw25274step0 = (fun i j => raw25274 (permutation178 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25274step0 raw25274; decide +kernel
      have hl : raw25274step0Labels = raw25274Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25274 raw25274Labels permutation178 permutation6
    mixedMoment B raw25274step0 raw25274step0Labels = mixedMoment B raw25274step1 raw25274step1Labels := by
      have ha : raw25274step1 = raw25274step0 := by apply Matrix.ext; unfold raw25274step1 raw25274step0; decide +kernel
      have hl : raw25274step0Labels = labelEmbedding9 ∘ raw25274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25274step0 raw25274step0Labels raw25274step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4407 node4407Labels := by rfl

def raw25275 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25275step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25275step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25275 raw25275Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw25275 raw25275Labels = mixedMoment B raw25275step0 raw25275step0Labels := by
      have hz : ∀ j, raw25275 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25275step0 = (fun i j => raw25275 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25275step0 raw25275; decide +kernel
      have hl : raw25275step0Labels = raw25275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25275 raw25275Labels permutation346 hz
    mixedMoment B raw25275step0 raw25275step0Labels = mixedMoment B raw25275step1 raw25275step1Labels := by
      have ha : raw25275step1 = (fun i j => raw25275step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25275step1 raw25275step0; decide +kernel
      have hl : raw25275step1Labels = raw25275step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25275step0 raw25275step0Labels permutation32 permutation6
    mixedMoment B raw25275step1 raw25275step1Labels = mixedMoment B raw25275step2 raw25275step2Labels := by
      have ha : raw25275step2 = raw25275step1 := by apply Matrix.ext; unfold raw25275step2 raw25275step1; decide +kernel
      have hl : raw25275step1Labels = labelEmbedding9 ∘ raw25275step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25275step1 raw25275step1Labels raw25275step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4474 node4474Labels := by rfl

def raw25276 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25276step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25276step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25276 raw25276Labels = mixedMoment B node4471 node4471Labels := by
  calc
    mixedMoment B raw25276 raw25276Labels = mixedMoment B raw25276step0 raw25276step0Labels := by
      have hz : ∀ j, raw25276 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25276step0 = (fun i j => raw25276 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25276step0 raw25276; decide +kernel
      have hl : raw25276step0Labels = raw25276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25276 raw25276Labels permutation346 hz
    mixedMoment B raw25276step0 raw25276step0Labels = mixedMoment B raw25276step1 raw25276step1Labels := by
      have ha : raw25276step1 = (fun i j => raw25276step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25276step1 raw25276step0; decide +kernel
      have hl : raw25276step1Labels = raw25276step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25276step0 raw25276step0Labels permutation34 permutation6
    mixedMoment B raw25276step1 raw25276step1Labels = mixedMoment B raw25276step2 raw25276step2Labels := by
      have ha : raw25276step2 = raw25276step1 := by apply Matrix.ext; unfold raw25276step2 raw25276step1; decide +kernel
      have hl : raw25276step1Labels = labelEmbedding9 ∘ raw25276step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25276step1 raw25276step1Labels raw25276step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4471 node4471Labels := by rfl

def raw25277 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25277step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25277step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25277 raw25277Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw25277 raw25277Labels = mixedMoment B raw25277step0 raw25277step0Labels := by
      have ha : raw25277step0 = (fun i j => raw25277 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25277step0 raw25277; decide +kernel
      have hl : raw25277step0Labels = raw25277Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25277 raw25277Labels permutation154 permutation6
    mixedMoment B raw25277step0 raw25277step0Labels = mixedMoment B raw25277step1 raw25277step1Labels := by
      have ha : raw25277step1 = raw25277step0 := by apply Matrix.ext; unfold raw25277step1 raw25277step0; decide +kernel
      have hl : raw25277step0Labels = labelEmbedding9 ∘ raw25277step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25277step0 raw25277step0Labels raw25277step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

def raw25278 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25278step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25278step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25278 raw25278Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25278 raw25278Labels = mixedMoment B raw25278step0 raw25278step0Labels := by
      have hz : ∀ j, raw25278 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25278step0 = (fun i j => raw25278 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25278step0 raw25278; decide +kernel
      have hl : raw25278step0Labels = raw25278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25278 raw25278Labels permutation265 hz
    mixedMoment B raw25278step0 raw25278step0Labels = mixedMoment B raw25278step1 raw25278step1Labels := by
      have ha : raw25278step1 = (fun i j => raw25278step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25278step1 raw25278step0; decide +kernel
      have hl : raw25278step1Labels = raw25278step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25278step0 raw25278step0Labels permutation34 permutation6
    mixedMoment B raw25278step1 raw25278step1Labels = mixedMoment B raw25278step2 raw25278step2Labels := by
      have ha : raw25278step2 = raw25278step1 := by apply Matrix.ext; unfold raw25278step2 raw25278step1; decide +kernel
      have hl : raw25278step1Labels = labelEmbedding9 ∘ raw25278step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25278step1 raw25278step1Labels raw25278step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw25279 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25279step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25279 raw25279Labels = mixedMoment B node4438 node4438Labels := by
  calc
    mixedMoment B raw25279 raw25279Labels = mixedMoment B raw25279step0 raw25279step0Labels := by
      have ha : raw25279step0 = (fun i j => raw25279 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25279step0 raw25279; decide +kernel
      have hl : raw25279step0Labels = raw25279Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25279 raw25279Labels permutation152 permutation6
    mixedMoment B raw25279step0 raw25279step0Labels = mixedMoment B raw25279step1 raw25279step1Labels := by
      have ha : raw25279step1 = raw25279step0 := by apply Matrix.ext; unfold raw25279step1 raw25279step0; decide +kernel
      have hl : raw25279step0Labels = labelEmbedding9 ∘ raw25279step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25279step0 raw25279step0Labels raw25279step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4438 node4438Labels := by rfl

def raw25280 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25280step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25280step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25280 raw25280Labels = mixedMoment B node4436 node4436Labels := by
  calc
    mixedMoment B raw25280 raw25280Labels = mixedMoment B raw25280step0 raw25280step0Labels := by
      have ha : raw25280step0 = (fun i j => raw25280 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25280step0 raw25280; decide +kernel
      have hl : raw25280step0Labels = raw25280Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25280 raw25280Labels permutation154 permutation6
    mixedMoment B raw25280step0 raw25280step0Labels = mixedMoment B raw25280step1 raw25280step1Labels := by
      have ha : raw25280step1 = raw25280step0 := by apply Matrix.ext; unfold raw25280step1 raw25280step0; decide +kernel
      have hl : raw25280step0Labels = labelEmbedding9 ∘ raw25280step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25280step0 raw25280step0Labels raw25280step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4436 node4436Labels := by rfl

def raw25281 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw25281step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25281step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25281step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25281step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25281step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25281 raw25281Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw25281 raw25281Labels = mixedMoment B raw25281step0 raw25281step0Labels := by
      have hz : ∀ j, raw25281 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25281step0 = (fun i j => raw25281 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25281step0 raw25281; decide +kernel
      have hl : raw25281step0Labels = raw25281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25281 raw25281Labels permutation346 hz
    mixedMoment B raw25281step0 raw25281step0Labels = mixedMoment B raw25281step1 raw25281step1Labels := by
      have ha : raw25281step1 = (fun i j => raw25281step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25281step1 raw25281step0; decide +kernel
      have hl : raw25281step1Labels = raw25281step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25281step0 raw25281step0Labels permutation45 permutation4
    mixedMoment B raw25281step1 raw25281step1Labels = mixedMoment B raw25281step2 raw25281step2Labels := by
      have ha : raw25281step2 = -raw25281step1 := by apply Matrix.ext; change ∀ i j, raw25281step2 i j = -(raw25281step1 i j); unfold raw25281step2 raw25281step1; decide +kernel
      have hl : raw25281step2Labels = raw25281step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25281step2 raw25281step2Labels = mixedMoment B raw25281step3 raw25281step3Labels := by
      have ha : raw25281step3 = raw25281step2 := by apply Matrix.ext; unfold raw25281step3 raw25281step2; decide +kernel
      have hl : raw25281step2Labels = labelEmbedding7 ∘ raw25281step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25281step2 raw25281step2Labels raw25281step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4265 node4265Labels := by rfl

def raw25282 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25282step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25282step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25282step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25282 raw25282Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw25282 raw25282Labels = mixedMoment B raw25282step0 raw25282step0Labels := by
      have hz : ∀ j, raw25282 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25282step0 = (fun i j => raw25282 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25282step0 raw25282; decide +kernel
      have hl : raw25282step0Labels = raw25282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25282 raw25282Labels permutation346 hz
    mixedMoment B raw25282step0 raw25282step0Labels = mixedMoment B raw25282step1 raw25282step1Labels := by
      have hz : ∀ j, raw25282step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25282step1 = (fun i j => raw25282step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25282step1 raw25282step0; decide +kernel
      have hl : raw25282step1Labels = raw25282step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25282step0 raw25282step0Labels permutation56 hz
    mixedMoment B raw25282step1 raw25282step1Labels = mixedMoment B raw25282step2 raw25282step2Labels := by
      have ha : raw25282step2 = (fun i j => raw25282step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25282step2 raw25282step1; decide +kernel
      have hl : raw25282step2Labels = raw25282step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25282step1 raw25282step1Labels permutation10 permutation6
    mixedMoment B raw25282step2 raw25282step2Labels = mixedMoment B raw25282step3 raw25282step3Labels := by
      have ha : raw25282step3 = raw25282step2 := by apply Matrix.ext; unfold raw25282step3 raw25282step2; decide +kernel
      have hl : raw25282step2Labels = labelEmbedding9 ∘ raw25282step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25282step2 raw25282step2Labels raw25282step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw25283 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25283step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25283step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25283 raw25283Labels = mixedMoment B node4397 node4397Labels := by
  calc
    mixedMoment B raw25283 raw25283Labels = mixedMoment B raw25283step0 raw25283step0Labels := by
      have ha : raw25283step0 = (fun i j => raw25283 (permutation178 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25283step0 raw25283; decide +kernel
      have hl : raw25283step0Labels = raw25283Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25283 raw25283Labels permutation178 permutation6
    mixedMoment B raw25283step0 raw25283step0Labels = mixedMoment B raw25283step1 raw25283step1Labels := by
      have ha : raw25283step1 = raw25283step0 := by apply Matrix.ext; unfold raw25283step1 raw25283step0; decide +kernel
      have hl : raw25283step0Labels = labelEmbedding9 ∘ raw25283step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25283step0 raw25283step0Labels raw25283step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4397 node4397Labels := by rfl

def raw25284 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25284step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25284step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25284step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25284 raw25284Labels = mixedMoment B node4453 node4453Labels := by
  calc
    mixedMoment B raw25284 raw25284Labels = mixedMoment B raw25284step0 raw25284step0Labels := by
      have hz : ∀ j, raw25284 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25284step0 = (fun i j => raw25284 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25284step0 raw25284; decide +kernel
      have hl : raw25284step0Labels = raw25284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25284 raw25284Labels permutation346 hz
    mixedMoment B raw25284step0 raw25284step0Labels = mixedMoment B raw25284step1 raw25284step1Labels := by
      have ha : raw25284step1 = (fun i j => raw25284step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25284step1 raw25284step0; decide +kernel
      have hl : raw25284step1Labels = raw25284step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25284step0 raw25284step0Labels permutation34 permutation6
    mixedMoment B raw25284step1 raw25284step1Labels = mixedMoment B raw25284step2 raw25284step2Labels := by
      have ha : raw25284step2 = raw25284step1 := by apply Matrix.ext; unfold raw25284step2 raw25284step1; decide +kernel
      have hl : raw25284step1Labels = labelEmbedding9 ∘ raw25284step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25284step1 raw25284step1Labels raw25284step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4453 node4453Labels := by rfl

def raw25285 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25285step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25285step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25285step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25285 raw25285Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw25285 raw25285Labels = mixedMoment B raw25285step0 raw25285step0Labels := by
      have hz : ∀ j, raw25285 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25285step0 = (fun i j => raw25285 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25285step0 raw25285; decide +kernel
      have hl : raw25285step0Labels = raw25285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25285 raw25285Labels permutation346 hz
    mixedMoment B raw25285step0 raw25285step0Labels = mixedMoment B raw25285step1 raw25285step1Labels := by
      have ha : raw25285step1 = (fun i j => raw25285step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25285step1 raw25285step0; decide +kernel
      have hl : raw25285step1Labels = raw25285step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25285step0 raw25285step0Labels permutation32 permutation6
    mixedMoment B raw25285step1 raw25285step1Labels = mixedMoment B raw25285step2 raw25285step2Labels := by
      have ha : raw25285step2 = raw25285step1 := by apply Matrix.ext; unfold raw25285step2 raw25285step1; decide +kernel
      have hl : raw25285step1Labels = labelEmbedding9 ∘ raw25285step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25285step1 raw25285step1Labels raw25285step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw25286 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw25286step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25286step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25286step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25286step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25286step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25286 raw25286Labels = mixedMoment B node4264 node4264Labels := by
  calc
    mixedMoment B raw25286 raw25286Labels = mixedMoment B raw25286step0 raw25286step0Labels := by
      have hz : ∀ j, raw25286 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25286step0 = (fun i j => raw25286 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25286step0 raw25286; decide +kernel
      have hl : raw25286step0Labels = raw25286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25286 raw25286Labels permutation346 hz
    mixedMoment B raw25286step0 raw25286step0Labels = mixedMoment B raw25286step1 raw25286step1Labels := by
      have ha : raw25286step1 = (fun i j => raw25286step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25286step1 raw25286step0; decide +kernel
      have hl : raw25286step1Labels = raw25286step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25286step0 raw25286step0Labels permutation44 permutation4
    mixedMoment B raw25286step1 raw25286step1Labels = mixedMoment B raw25286step2 raw25286step2Labels := by
      have ha : raw25286step2 = -raw25286step1 := by apply Matrix.ext; change ∀ i j, raw25286step2 i j = -(raw25286step1 i j); unfold raw25286step2 raw25286step1; decide +kernel
      have hl : raw25286step2Labels = raw25286step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25286step2 raw25286step2Labels = mixedMoment B raw25286step3 raw25286step3Labels := by
      have ha : raw25286step3 = raw25286step2 := by apply Matrix.ext; unfold raw25286step3 raw25286step2; decide +kernel
      have hl : raw25286step2Labels = labelEmbedding7 ∘ raw25286step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25286step2 raw25286step2Labels raw25286step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4264 node4264Labels := by rfl

def raw25287 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25287step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25287step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25287 raw25287Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw25287 raw25287Labels = mixedMoment B raw25287step0 raw25287step0Labels := by
      have hz : ∀ j, raw25287 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25287step0 = (fun i j => raw25287 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25287step0 raw25287; decide +kernel
      have hl : raw25287step0Labels = raw25287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25287 raw25287Labels permutation346 hz
    mixedMoment B raw25287step0 raw25287step0Labels = mixedMoment B raw25287step1 raw25287step1Labels := by
      have ha : raw25287step1 = (fun i j => raw25287step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25287step1 raw25287step0; decide +kernel
      have hl : raw25287step1Labels = raw25287step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25287step0 raw25287step0Labels permutation34 permutation6
    mixedMoment B raw25287step1 raw25287step1Labels = mixedMoment B raw25287step2 raw25287step2Labels := by
      have ha : raw25287step2 = raw25287step1 := by apply Matrix.ext; unfold raw25287step2 raw25287step1; decide +kernel
      have hl : raw25287step1Labels = labelEmbedding9 ∘ raw25287step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25287step1 raw25287step1Labels raw25287step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

def raw25288 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25288step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25288step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25288 raw25288Labels = mixedMoment B node1266 node1266Labels := by
  calc
    mixedMoment B raw25288 raw25288Labels = mixedMoment B raw25288step0 raw25288step0Labels := by
      have hz : ∀ j, raw25288 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25288step0 = (fun i j => raw25288 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25288step0 raw25288; decide +kernel
      have hl : raw25288step0Labels = raw25288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25288 raw25288Labels permutation346 hz
    mixedMoment B raw25288step0 raw25288step0Labels = mixedMoment B raw25288step1 raw25288step1Labels := by
      have ha : raw25288step1 = (fun i j => raw25288step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25288step1 raw25288step0; decide +kernel
      have hl : raw25288step1Labels = raw25288step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25288step0 raw25288step0Labels permutation32 permutation6
    _ = mixedMoment B node1266 node1266Labels := by rfl

def raw25289 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25289Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25289step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25289step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25289 raw25289Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw25289 raw25289Labels = mixedMoment B raw25289step0 raw25289step0Labels := by
      have hz : ∀ j, raw25289 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25289step0 = (fun i j => raw25289 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25289step0 raw25289; decide +kernel
      have hl : raw25289step0Labels = raw25289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25289 raw25289Labels permutation346 hz
    mixedMoment B raw25289step0 raw25289step0Labels = mixedMoment B raw25289step1 raw25289step1Labels := by
      have ha : raw25289step1 = (fun i j => raw25289step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25289step1 raw25289step0; decide +kernel
      have hl : raw25289step1Labels = raw25289step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25289step0 raw25289step0Labels permutation34 permutation6
    _ = mixedMoment B node1262 node1262Labels := by rfl

def raw25290 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25290Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25290step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25290step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25290 raw25290Labels = mixedMoment B node824 node824Labels := by
  calc
    mixedMoment B raw25290 raw25290Labels = mixedMoment B raw25290step0 raw25290step0Labels := by
      have hz : ∀ j, raw25290 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25290step0 = (fun i j => raw25290 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25290step0 raw25290; decide +kernel
      have hl : raw25290step0Labels = raw25290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25290 raw25290Labels permutation346 hz
    mixedMoment B raw25290step0 raw25290step0Labels = mixedMoment B raw25290step1 raw25290step1Labels := by
      have ha : raw25290step1 = (fun i j => raw25290step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25290step1 raw25290step0; decide +kernel
      have hl : raw25290step1Labels = raw25290step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25290step0 raw25290step0Labels permutation34 permutation6
    _ = mixedMoment B node824 node824Labels := by rfl

def raw25291 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25291Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25291step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25291 raw25291Labels = mixedMoment B node988 node988Labels := by
  calc
    mixedMoment B raw25291 raw25291Labels = mixedMoment B raw25291step0 raw25291step0Labels := by
      have ha : raw25291step0 = (fun i j => raw25291 (permutation178 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25291step0 raw25291; decide +kernel
      have hl : raw25291step0Labels = raw25291Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25291 raw25291Labels permutation178 permutation6
    _ = mixedMoment B node988 node988Labels := by rfl

def raw25292 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25292Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25292step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25292step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25292 raw25292Labels = mixedMoment B node1057 node1057Labels := by
  calc
    mixedMoment B raw25292 raw25292Labels = mixedMoment B raw25292step0 raw25292step0Labels := by
      have hz : ∀ j, raw25292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25292step0 = (fun i j => raw25292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25292step0 raw25292; decide +kernel
      have hl : raw25292step0Labels = raw25292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25292 raw25292Labels permutation346 hz
    mixedMoment B raw25292step0 raw25292step0Labels = mixedMoment B raw25292step1 raw25292step1Labels := by
      have ha : raw25292step1 = (fun i j => raw25292step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25292step1 raw25292step0; decide +kernel
      have hl : raw25292step1Labels = raw25292step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25292step0 raw25292step0Labels permutation32 permutation6
    _ = mixedMoment B node1057 node1057Labels := by rfl

def raw25293 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25293Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25293step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25293step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25293 raw25293Labels = mixedMoment B node1054 node1054Labels := by
  calc
    mixedMoment B raw25293 raw25293Labels = mixedMoment B raw25293step0 raw25293step0Labels := by
      have hz : ∀ j, raw25293 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25293step0 = (fun i j => raw25293 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25293step0 raw25293; decide +kernel
      have hl : raw25293step0Labels = raw25293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25293 raw25293Labels permutation346 hz
    mixedMoment B raw25293step0 raw25293step0Labels = mixedMoment B raw25293step1 raw25293step1Labels := by
      have ha : raw25293step1 = (fun i j => raw25293step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25293step1 raw25293step0; decide +kernel
      have hl : raw25293step1Labels = raw25293step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25293step0 raw25293step0Labels permutation34 permutation6
    _ = mixedMoment B node1054 node1054Labels := by rfl

def raw25294 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25294Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25294step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25294 raw25294Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw25294 raw25294Labels = mixedMoment B raw25294step0 raw25294step0Labels := by
      have ha : raw25294step0 = (fun i j => raw25294 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25294step0 raw25294; decide +kernel
      have hl : raw25294step0Labels = raw25294Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25294 raw25294Labels permutation154 permutation6
    _ = mixedMoment B node783 node783Labels := by rfl

def raw25295 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25295step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25295step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25295 raw25295Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw25295 raw25295Labels = mixedMoment B raw25295step0 raw25295step0Labels := by
      have hz : ∀ j, raw25295 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25295step0 = (fun i j => raw25295 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25295step0 raw25295; decide +kernel
      have hl : raw25295step0Labels = raw25295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25295 raw25295Labels permutation265 hz
    mixedMoment B raw25295step0 raw25295step0Labels = mixedMoment B raw25295step1 raw25295step1Labels := by
      have ha : raw25295step1 = (fun i j => raw25295step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25295step1 raw25295step0; decide +kernel
      have hl : raw25295step1Labels = raw25295step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25295step0 raw25295step0Labels permutation34 permutation6
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw25296 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25296step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25296 raw25296Labels = mixedMoment B node1020 node1020Labels := by
  calc
    mixedMoment B raw25296 raw25296Labels = mixedMoment B raw25296step0 raw25296step0Labels := by
      have ha : raw25296step0 = (fun i j => raw25296 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25296step0 raw25296; decide +kernel
      have hl : raw25296step0Labels = raw25296Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25296 raw25296Labels permutation152 permutation6
    _ = mixedMoment B node1020 node1020Labels := by rfl

def raw25297 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25297step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25297 raw25297Labels = mixedMoment B node1018 node1018Labels := by
  calc
    mixedMoment B raw25297 raw25297Labels = mixedMoment B raw25297step0 raw25297step0Labels := by
      have ha : raw25297step0 = (fun i j => raw25297 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25297step0 raw25297; decide +kernel
      have hl : raw25297step0Labels = raw25297Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25297 raw25297Labels permutation154 permutation6
    _ = mixedMoment B node1018 node1018Labels := by rfl

def raw25298 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25298step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25298 raw25298Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw25298 raw25298Labels = mixedMoment B raw25298step0 raw25298step0Labels := by
      have hz : ∀ j, raw25298 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25298step0 = (fun i j => raw25298 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25298step0 raw25298; decide +kernel
      have hl : raw25298step0Labels = raw25298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25298 raw25298Labels permutation346 hz
    mixedMoment B raw25298step0 raw25298step0Labels = mixedMoment B raw25298step1 raw25298step1Labels := by
      have ha : raw25298step1 = (fun i j => raw25298step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25298step1 raw25298step0; decide +kernel
      have hl : raw25298step1Labels = raw25298step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25298step0 raw25298step0Labels permutation34 permutation6
    _ = mixedMoment B node807 node807Labels := by rfl

def raw25299 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25299step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25299step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25299 raw25299Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw25299 raw25299Labels = mixedMoment B raw25299step0 raw25299step0Labels := by
      have hz : ∀ j, raw25299 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25299step0 = (fun i j => raw25299 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25299step0 raw25299; decide +kernel
      have hl : raw25299step0Labels = raw25299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25299 raw25299Labels permutation346 hz
    mixedMoment B raw25299step0 raw25299step0Labels = mixedMoment B raw25299step1 raw25299step1Labels := by
      have hz : ∀ j, raw25299step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25299step1 = (fun i j => raw25299step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25299step1 raw25299step0; decide +kernel
      have hl : raw25299step1Labels = raw25299step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25299step0 raw25299step0Labels permutation56 hz
    mixedMoment B raw25299step1 raw25299step1Labels = mixedMoment B raw25299step2 raw25299step2Labels := by
      have ha : raw25299step2 = (fun i j => raw25299step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25299step2 raw25299step1; decide +kernel
      have hl : raw25299step2Labels = raw25299step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25299step1 raw25299step1Labels permutation10 permutation6
    _ = mixedMoment B node1083 node1083Labels := by rfl

def raw25300 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25300step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25300 raw25300Labels = mixedMoment B node978 node978Labels := by
  calc
    mixedMoment B raw25300 raw25300Labels = mixedMoment B raw25300step0 raw25300step0Labels := by
      have ha : raw25300step0 = (fun i j => raw25300 (permutation178 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25300step0 raw25300; decide +kernel
      have hl : raw25300step0Labels = raw25300Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25300 raw25300Labels permutation178 permutation6
    _ = mixedMoment B node978 node978Labels := by rfl

def raw25301 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25301step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25301 raw25301Labels = mixedMoment B node1036 node1036Labels := by
  calc
    mixedMoment B raw25301 raw25301Labels = mixedMoment B raw25301step0 raw25301step0Labels := by
      have hz : ∀ j, raw25301 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25301step0 = (fun i j => raw25301 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25301step0 raw25301; decide +kernel
      have hl : raw25301step0Labels = raw25301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25301 raw25301Labels permutation346 hz
    mixedMoment B raw25301step0 raw25301step0Labels = mixedMoment B raw25301step1 raw25301step1Labels := by
      have ha : raw25301step1 = (fun i j => raw25301step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25301step1 raw25301step0; decide +kernel
      have hl : raw25301step1Labels = raw25301step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25301step0 raw25301step0Labels permutation34 permutation6
    _ = mixedMoment B node1036 node1036Labels := by rfl

def raw25302 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25302 raw25302Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw25302 raw25302Labels = mixedMoment B raw25302step0 raw25302step0Labels := by
      have hz : ∀ j, raw25302 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25302step0 = (fun i j => raw25302 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25302step0 raw25302; decide +kernel
      have hl : raw25302step0Labels = raw25302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25302 raw25302Labels permutation346 hz
    mixedMoment B raw25302step0 raw25302step0Labels = mixedMoment B raw25302step1 raw25302step1Labels := by
      have ha : raw25302step1 = (fun i j => raw25302step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25302step1 raw25302step0; decide +kernel
      have hl : raw25302step1Labels = raw25302step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25302step0 raw25302step0Labels permutation32 permutation6
    _ = mixedMoment B node1044 node1044Labels := by rfl

def raw25303 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25303step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25303step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25303 raw25303Labels = mixedMoment B node806 node806Labels := by
  calc
    mixedMoment B raw25303 raw25303Labels = mixedMoment B raw25303step0 raw25303step0Labels := by
      have hz : ∀ j, raw25303 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25303step0 = (fun i j => raw25303 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25303step0 raw25303; decide +kernel
      have hl : raw25303step0Labels = raw25303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25303 raw25303Labels permutation346 hz
    mixedMoment B raw25303step0 raw25303step0Labels = mixedMoment B raw25303step1 raw25303step1Labels := by
      have ha : raw25303step1 = (fun i j => raw25303step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25303step1 raw25303step0; decide +kernel
      have hl : raw25303step1Labels = raw25303step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25303step0 raw25303step0Labels permutation34 permutation6
    _ = mixedMoment B node806 node806Labels := by rfl

def raw25304 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25304step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25304step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25304step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25304 raw25304Labels = mixedMoment B node1082 node1082Labels := by
  calc
    mixedMoment B raw25304 raw25304Labels = mixedMoment B raw25304step0 raw25304step0Labels := by
      have hz : ∀ j, raw25304 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25304step0 = (fun i j => raw25304 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25304step0 raw25304; decide +kernel
      have hl : raw25304step0Labels = raw25304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25304 raw25304Labels permutation346 hz
    mixedMoment B raw25304step0 raw25304step0Labels = mixedMoment B raw25304step1 raw25304step1Labels := by
      have hz : ∀ j, raw25304step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25304step1 = (fun i j => raw25304step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25304step1 raw25304step0; decide +kernel
      have hl : raw25304step1Labels = raw25304step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25304step0 raw25304step0Labels permutation56 hz
    mixedMoment B raw25304step1 raw25304step1Labels = mixedMoment B raw25304step2 raw25304step2Labels := by
      have ha : raw25304step2 = (fun i j => raw25304step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25304step2 raw25304step1; decide +kernel
      have hl : raw25304step2Labels = raw25304step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25304step1 raw25304step1Labels permutation10 permutation6
    _ = mixedMoment B node1082 node1082Labels := by rfl

def raw25305 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25305Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25305step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25305 raw25305Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw25305 raw25305Labels = mixedMoment B raw25305step0 raw25305step0Labels := by
      have ha : raw25305step0 = (fun i j => raw25305 (permutation178 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25305step0 raw25305; decide +kernel
      have hl : raw25305step0Labels = raw25305Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25305 raw25305Labels permutation178 permutation6
    _ = mixedMoment B node977 node977Labels := by rfl

def raw25306 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25306step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25306step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25306 raw25306Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw25306 raw25306Labels = mixedMoment B raw25306step0 raw25306step0Labels := by
      have hz : ∀ j, raw25306 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25306step0 = (fun i j => raw25306 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25306step0 raw25306; decide +kernel
      have hl : raw25306step0Labels = raw25306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25306 raw25306Labels permutation346 hz
    mixedMoment B raw25306step0 raw25306step0Labels = mixedMoment B raw25306step1 raw25306step1Labels := by
      have ha : raw25306step1 = (fun i j => raw25306step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25306step1 raw25306step0; decide +kernel
      have hl : raw25306step1Labels = raw25306step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25306step0 raw25306step0Labels permutation32 permutation6
    _ = mixedMoment B node1040 node1040Labels := by rfl

def raw25307 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25307step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25307 raw25307Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw25307 raw25307Labels = mixedMoment B raw25307step0 raw25307step0Labels := by
      have hz : ∀ j, raw25307 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25307step0 = (fun i j => raw25307 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25307step0 raw25307; decide +kernel
      have hl : raw25307step0Labels = raw25307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25307 raw25307Labels permutation346 hz
    mixedMoment B raw25307step0 raw25307step0Labels = mixedMoment B raw25307step1 raw25307step1Labels := by
      have ha : raw25307step1 = (fun i j => raw25307step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25307step1 raw25307step0; decide +kernel
      have hl : raw25307step1Labels = raw25307step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25307step0 raw25307step0Labels permutation34 permutation6
    _ = mixedMoment B node1035 node1035Labels := by rfl

def raw25308 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25308Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25308step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25308 raw25308Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw25308 raw25308Labels = mixedMoment B raw25308step0 raw25308step0Labels := by
      have ha : raw25308step0 = (fun i j => raw25308 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25308step0 raw25308; decide +kernel
      have hl : raw25308step0Labels = raw25308Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25308 raw25308Labels permutation152 permutation7
    mixedMoment B raw25308step0 raw25308step0Labels = mixedMoment B raw25308step1 raw25308step1Labels := by
      have ha : raw25308step1 = raw25308step0 := by apply Matrix.ext; unfold raw25308step1 raw25308step0; decide +kernel
      have hl : raw25308step0Labels = labelEmbedding1 ∘ raw25308step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25308step0 raw25308step0Labels raw25308step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw25309 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25309Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25309step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25309step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25309step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25309step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25309 raw25309Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw25309 raw25309Labels = mixedMoment B raw25309step0 raw25309step0Labels := by
      have hz : ∀ j, raw25309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25309step0 = (fun i j => raw25309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25309step0 raw25309; decide +kernel
      have hl : raw25309step0Labels = raw25309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25309 raw25309Labels permutation346 hz
    mixedMoment B raw25309step0 raw25309step0Labels = mixedMoment B raw25309step1 raw25309step1Labels := by
      have ha : raw25309step1 = (fun i j => raw25309step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25309step1 raw25309step0; decide +kernel
      have hl : raw25309step1Labels = raw25309step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25309step0 raw25309step0Labels permutation32 permutation7
    mixedMoment B raw25309step1 raw25309step1Labels = mixedMoment B raw25309step2 raw25309step2Labels := by
      have ha : raw25309step2 = raw25309step1 := by apply Matrix.ext; unfold raw25309step2 raw25309step1; decide +kernel
      have hl : raw25309step1Labels = labelEmbedding1 ∘ raw25309step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25309step1 raw25309step1Labels raw25309step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw25310 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25310Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25310step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25310step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25310 raw25310Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw25310 raw25310Labels = mixedMoment B raw25310step0 raw25310step0Labels := by
      have hz : ∀ j, raw25310 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25310step0 = (fun i j => raw25310 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25310step0 raw25310; decide +kernel
      have hl : raw25310step0Labels = raw25310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25310 raw25310Labels permutation346 hz
    mixedMoment B raw25310step0 raw25310step0Labels = mixedMoment B raw25310step1 raw25310step1Labels := by
      have ha : raw25310step1 = (fun i j => raw25310step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25310step1 raw25310step0; decide +kernel
      have hl : raw25310step1Labels = raw25310step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25310step0 raw25310step0Labels permutation32 permutation7
    mixedMoment B raw25310step1 raw25310step1Labels = mixedMoment B raw25310step2 raw25310step2Labels := by
      have ha : raw25310step2 = raw25310step1 := by apply Matrix.ext; unfold raw25310step2 raw25310step1; decide +kernel
      have hl : raw25310step1Labels = labelEmbedding1 ∘ raw25310step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25310step1 raw25310step1Labels raw25310step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw25311 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25311Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25311step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25311step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25311 raw25311Labels = mixedMoment B node1468 node1468Labels := by
  calc
    mixedMoment B raw25311 raw25311Labels = mixedMoment B raw25311step0 raw25311step0Labels := by
      have hz : ∀ j, raw25311 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25311step0 = (fun i j => raw25311 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25311step0 raw25311; decide +kernel
      have hl : raw25311step0Labels = raw25311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25311 raw25311Labels permutation346 hz
    mixedMoment B raw25311step0 raw25311step0Labels = mixedMoment B raw25311step1 raw25311step1Labels := by
      have ha : raw25311step1 = (fun i j => raw25311step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25311step1 raw25311step0; decide +kernel
      have hl : raw25311step1Labels = raw25311step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25311step0 raw25311step0Labels permutation32 permutation7
    mixedMoment B raw25311step1 raw25311step1Labels = mixedMoment B raw25311step2 raw25311step2Labels := by
      have ha : raw25311step2 = raw25311step1 := by apply Matrix.ext; unfold raw25311step2 raw25311step1; decide +kernel
      have hl : raw25311step1Labels = labelEmbedding1 ∘ raw25311step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25311step1 raw25311step1Labels raw25311step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1468 node1468Labels := by rfl

def raw25312 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25312Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25312step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25312step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25312 raw25312Labels = mixedMoment B node1358 node1358Labels := by
  calc
    mixedMoment B raw25312 raw25312Labels = mixedMoment B raw25312step0 raw25312step0Labels := by
      have ha : raw25312step0 = (fun i j => raw25312 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25312step0 raw25312; decide +kernel
      have hl : raw25312step0Labels = raw25312Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25312 raw25312Labels permutation152 permutation7
    mixedMoment B raw25312step0 raw25312step0Labels = mixedMoment B raw25312step1 raw25312step1Labels := by
      have ha : raw25312step1 = raw25312step0 := by apply Matrix.ext; unfold raw25312step1 raw25312step0; decide +kernel
      have hl : raw25312step0Labels = labelEmbedding1 ∘ raw25312step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25312step0 raw25312step0Labels raw25312step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1358 node1358Labels := by rfl

def raw25313 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25313Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25313step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25313step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25313 raw25313Labels = mixedMoment B node1370 node1370Labels := by
  calc
    mixedMoment B raw25313 raw25313Labels = mixedMoment B raw25313step0 raw25313step0Labels := by
      have hz : ∀ j, raw25313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25313step0 = (fun i j => raw25313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25313step0 raw25313; decide +kernel
      have hl : raw25313step0Labels = raw25313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25313 raw25313Labels permutation346 hz
    mixedMoment B raw25313step0 raw25313step0Labels = mixedMoment B raw25313step1 raw25313step1Labels := by
      have ha : raw25313step1 = (fun i j => raw25313step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25313step1 raw25313step0; decide +kernel
      have hl : raw25313step1Labels = raw25313step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25313step0 raw25313step0Labels permutation32 permutation7
    mixedMoment B raw25313step1 raw25313step1Labels = mixedMoment B raw25313step2 raw25313step2Labels := by
      have ha : raw25313step2 = raw25313step1 := by apply Matrix.ext; unfold raw25313step2 raw25313step1; decide +kernel
      have hl : raw25313step1Labels = labelEmbedding1 ∘ raw25313step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25313step1 raw25313step1Labels raw25313step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1370 node1370Labels := by rfl

def raw25314 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25314Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25314step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25314step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25314 raw25314Labels = mixedMoment B node1368 node1368Labels := by
  calc
    mixedMoment B raw25314 raw25314Labels = mixedMoment B raw25314step0 raw25314step0Labels := by
      have hz : ∀ j, raw25314 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25314step0 = (fun i j => raw25314 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25314step0 raw25314; decide +kernel
      have hl : raw25314step0Labels = raw25314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25314 raw25314Labels permutation346 hz
    mixedMoment B raw25314step0 raw25314step0Labels = mixedMoment B raw25314step1 raw25314step1Labels := by
      have ha : raw25314step1 = (fun i j => raw25314step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25314step1 raw25314step0; decide +kernel
      have hl : raw25314step1Labels = raw25314step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25314step0 raw25314step0Labels permutation32 permutation7
    mixedMoment B raw25314step1 raw25314step1Labels = mixedMoment B raw25314step2 raw25314step2Labels := by
      have ha : raw25314step2 = raw25314step1 := by apply Matrix.ext; unfold raw25314step2 raw25314step1; decide +kernel
      have hl : raw25314step1Labels = labelEmbedding1 ∘ raw25314step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25314step1 raw25314step1Labels raw25314step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1368 node1368Labels := by rfl

def raw25315 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25315Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25315step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25315step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25315step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25315 raw25315Labels = mixedMoment B node1367 node1367Labels := by
  calc
    mixedMoment B raw25315 raw25315Labels = mixedMoment B raw25315step0 raw25315step0Labels := by
      have hz : ∀ j, raw25315 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25315step0 = (fun i j => raw25315 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25315step0 raw25315; decide +kernel
      have hl : raw25315step0Labels = raw25315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25315 raw25315Labels permutation346 hz
    mixedMoment B raw25315step0 raw25315step0Labels = mixedMoment B raw25315step1 raw25315step1Labels := by
      have ha : raw25315step1 = (fun i j => raw25315step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25315step1 raw25315step0; decide +kernel
      have hl : raw25315step1Labels = raw25315step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25315step0 raw25315step0Labels permutation32 permutation7
    mixedMoment B raw25315step1 raw25315step1Labels = mixedMoment B raw25315step2 raw25315step2Labels := by
      have ha : raw25315step2 = raw25315step1 := by apply Matrix.ext; unfold raw25315step2 raw25315step1; decide +kernel
      have hl : raw25315step1Labels = labelEmbedding1 ∘ raw25315step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25315step1 raw25315step1Labels raw25315step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1367 node1367Labels := by rfl

def raw25316 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25316Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25316step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25316 raw25316Labels = mixedMoment B node1475 node1475Labels := by
  calc
    mixedMoment B raw25316 raw25316Labels = mixedMoment B raw25316step0 raw25316step0Labels := by
      have ha : raw25316step0 = (fun i j => raw25316 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25316step0 raw25316; decide +kernel
      have hl : raw25316step0Labels = raw25316Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25316 raw25316Labels permutation152 permutation7
    mixedMoment B raw25316step0 raw25316step0Labels = mixedMoment B raw25316step1 raw25316step1Labels := by
      have ha : raw25316step1 = raw25316step0 := by apply Matrix.ext; unfold raw25316step1 raw25316step0; decide +kernel
      have hl : raw25316step0Labels = labelEmbedding1 ∘ raw25316step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25316step0 raw25316step0Labels raw25316step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1475 node1475Labels := by rfl

def raw25317 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25317Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25317step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25317step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25317step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25317 raw25317Labels = mixedMoment B node1411 node1411Labels := by
  calc
    mixedMoment B raw25317 raw25317Labels = mixedMoment B raw25317step0 raw25317step0Labels := by
      have hz : ∀ j, raw25317 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25317step0 = (fun i j => raw25317 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25317step0 raw25317; decide +kernel
      have hl : raw25317step0Labels = raw25317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25317 raw25317Labels permutation265 hz
    mixedMoment B raw25317step0 raw25317step0Labels = mixedMoment B raw25317step1 raw25317step1Labels := by
      have ha : raw25317step1 = (fun i j => raw25317step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25317step1 raw25317step0; decide +kernel
      have hl : raw25317step1Labels = raw25317step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25317step0 raw25317step0Labels permutation32 permutation7
    mixedMoment B raw25317step1 raw25317step1Labels = mixedMoment B raw25317step2 raw25317step2Labels := by
      have ha : raw25317step2 = raw25317step1 := by apply Matrix.ext; unfold raw25317step2 raw25317step1; decide +kernel
      have hl : raw25317step1Labels = labelEmbedding1 ∘ raw25317step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25317step1 raw25317step1Labels raw25317step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1411 node1411Labels := by rfl

def raw25318 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25318Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25318step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25318 raw25318Labels = mixedMoment B node1386 node1386Labels := by
  calc
    mixedMoment B raw25318 raw25318Labels = mixedMoment B raw25318step0 raw25318step0Labels := by
      have ha : raw25318step0 = (fun i j => raw25318 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25318step0 raw25318; decide +kernel
      have hl : raw25318step0Labels = raw25318Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25318 raw25318Labels permutation152 permutation7
    mixedMoment B raw25318step0 raw25318step0Labels = mixedMoment B raw25318step1 raw25318step1Labels := by
      have ha : raw25318step1 = raw25318step0 := by apply Matrix.ext; unfold raw25318step1 raw25318step0; decide +kernel
      have hl : raw25318step0Labels = labelEmbedding1 ∘ raw25318step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25318step0 raw25318step0Labels raw25318step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1386 node1386Labels := by rfl

def raw25319 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25319Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25319step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25319step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw25319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25319 raw25319Labels = mixedMoment B node1384 node1384Labels := by
  calc
    mixedMoment B raw25319 raw25319Labels = mixedMoment B raw25319step0 raw25319step0Labels := by
      have ha : raw25319step0 = (fun i j => raw25319 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25319step0 raw25319; decide +kernel
      have hl : raw25319step0Labels = raw25319Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25319 raw25319Labels permutation152 permutation7
    mixedMoment B raw25319step0 raw25319step0Labels = mixedMoment B raw25319step1 raw25319step1Labels := by
      have ha : raw25319step1 = raw25319step0 := by apply Matrix.ext; unfold raw25319step1 raw25319step0; decide +kernel
      have hl : raw25319step0Labels = labelEmbedding1 ∘ raw25319step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25319step0 raw25319step0Labels raw25319step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1384 node1384Labels := by rfl

def raw25320 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25320Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25320step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25320 raw25320Labels = mixedMoment B node1383 node1383Labels := by
  calc
    mixedMoment B raw25320 raw25320Labels = mixedMoment B raw25320step0 raw25320step0Labels := by
      have ha : raw25320step0 = (fun i j => raw25320 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25320step0 raw25320; decide +kernel
      have hl : raw25320step0Labels = raw25320Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25320 raw25320Labels permutation152 permutation7
    mixedMoment B raw25320step0 raw25320step0Labels = mixedMoment B raw25320step1 raw25320step1Labels := by
      have ha : raw25320step1 = raw25320step0 := by apply Matrix.ext; unfold raw25320step1 raw25320step0; decide +kernel
      have hl : raw25320step0Labels = labelEmbedding1 ∘ raw25320step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25320step0 raw25320step0Labels raw25320step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1383 node1383Labels := by rfl

def raw25321 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25321Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25321step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw25321step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25321step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25321step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25321step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25321step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25321 raw25321Labels = mixedMoment B node1480 node1480Labels := by
  calc
    mixedMoment B raw25321 raw25321Labels = mixedMoment B raw25321step0 raw25321step0Labels := by
      have hz : ∀ j, raw25321 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25321step0 = (fun i j => raw25321 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25321step0 raw25321; decide +kernel
      have hl : raw25321step0Labels = raw25321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25321 raw25321Labels permutation346 hz
    mixedMoment B raw25321step0 raw25321step0Labels = mixedMoment B raw25321step1 raw25321step1Labels := by
      have ha : raw25321step1 = (fun i j => raw25321step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw25321step1 raw25321step0; decide +kernel
      have hl : raw25321step1Labels = raw25321step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25321step0 raw25321step0Labels permutation48 permutation5
    mixedMoment B raw25321step1 raw25321step1Labels = mixedMoment B raw25321step2 raw25321step2Labels := by
      have ha : raw25321step2 = -raw25321step1 := by apply Matrix.ext; change ∀ i j, raw25321step2 i j = -(raw25321step1 i j); unfold raw25321step2 raw25321step1; decide +kernel
      have hl : raw25321step2Labels = raw25321step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25321step2 raw25321step2Labels = mixedMoment B raw25321step3 raw25321step3Labels := by
      have ha : raw25321step3 = raw25321step2 := by apply Matrix.ext; unfold raw25321step3 raw25321step2; decide +kernel
      have hl : raw25321step2Labels = labelEmbedding1 ∘ raw25321step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25321step2 raw25321step2Labels raw25321step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1480 node1480Labels := by rfl

def raw25322 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25322Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25322step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25322step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25322step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25322step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25322step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25322step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25322 raw25322Labels = mixedMoment B node1443 node1443Labels := by
  calc
    mixedMoment B raw25322 raw25322Labels = mixedMoment B raw25322step0 raw25322step0Labels := by
      have hz : ∀ j, raw25322 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25322step0 = (fun i j => raw25322 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25322step0 raw25322; decide +kernel
      have hl : raw25322step0Labels = raw25322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25322 raw25322Labels permutation346 hz
    mixedMoment B raw25322step0 raw25322step0Labels = mixedMoment B raw25322step1 raw25322step1Labels := by
      have hz : ∀ j, raw25322step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25322step1 = (fun i j => raw25322step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25322step1 raw25322step0; decide +kernel
      have hl : raw25322step1Labels = raw25322step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25322step0 raw25322step0Labels permutation56 hz
    mixedMoment B raw25322step1 raw25322step1Labels = mixedMoment B raw25322step2 raw25322step2Labels := by
      have ha : raw25322step2 = (fun i j => raw25322step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25322step2 raw25322step1; decide +kernel
      have hl : raw25322step2Labels = raw25322step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25322step1 raw25322step1Labels permutation8 permutation7
    mixedMoment B raw25322step2 raw25322step2Labels = mixedMoment B raw25322step3 raw25322step3Labels := by
      have ha : raw25322step3 = raw25322step2 := by apply Matrix.ext; unfold raw25322step3 raw25322step2; decide +kernel
      have hl : raw25322step2Labels = labelEmbedding1 ∘ raw25322step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25322step2 raw25322step2Labels raw25322step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1443 node1443Labels := by rfl

def raw25323 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25323Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25323step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25323step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25323 raw25323Labels = mixedMoment B node1393 node1393Labels := by
  calc
    mixedMoment B raw25323 raw25323Labels = mixedMoment B raw25323step0 raw25323step0Labels := by
      have ha : raw25323step0 = (fun i j => raw25323 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25323step0 raw25323; decide +kernel
      have hl : raw25323step0Labels = raw25323Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25323 raw25323Labels permutation152 permutation7
    mixedMoment B raw25323step0 raw25323step0Labels = mixedMoment B raw25323step1 raw25323step1Labels := by
      have ha : raw25323step1 = raw25323step0 := by apply Matrix.ext; unfold raw25323step1 raw25323step0; decide +kernel
      have hl : raw25323step0Labels = labelEmbedding1 ∘ raw25323step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25323step0 raw25323step0Labels raw25323step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1393 node1393Labels := by rfl

def raw25324 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25324Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw25324step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25324step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw25324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25324 raw25324Labels = mixedMoment B node1407 node1407Labels := by
  calc
    mixedMoment B raw25324 raw25324Labels = mixedMoment B raw25324step0 raw25324step0Labels := by
      have hz : ∀ j, raw25324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25324step0 = (fun i j => raw25324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25324step0 raw25324; decide +kernel
      have hl : raw25324step0Labels = raw25324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25324 raw25324Labels permutation346 hz
    mixedMoment B raw25324step0 raw25324step0Labels = mixedMoment B raw25324step1 raw25324step1Labels := by
      have ha : raw25324step1 = (fun i j => raw25324step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25324step1 raw25324step0; decide +kernel
      have hl : raw25324step1Labels = raw25324step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25324step0 raw25324step0Labels permutation32 permutation7
    mixedMoment B raw25324step1 raw25324step1Labels = mixedMoment B raw25324step2 raw25324step2Labels := by
      have ha : raw25324step2 = raw25324step1 := by apply Matrix.ext; unfold raw25324step2 raw25324step1; decide +kernel
      have hl : raw25324step1Labels = labelEmbedding1 ∘ raw25324step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25324step1 raw25324step1Labels raw25324step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1407 node1407Labels := by rfl

def raw25325 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25325Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25325step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25325step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25325step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25325step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25325 raw25325Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw25325 raw25325Labels = mixedMoment B raw25325step0 raw25325step0Labels := by
      have hz : ∀ j, raw25325 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25325step0 = (fun i j => raw25325 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25325step0 raw25325; decide +kernel
      have hl : raw25325step0Labels = raw25325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25325 raw25325Labels permutation346 hz
    mixedMoment B raw25325step0 raw25325step0Labels = mixedMoment B raw25325step1 raw25325step1Labels := by
      have ha : raw25325step1 = (fun i j => raw25325step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25325step1 raw25325step0; decide +kernel
      have hl : raw25325step1Labels = raw25325step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25325step0 raw25325step0Labels permutation32 permutation7
    mixedMoment B raw25325step1 raw25325step1Labels = mixedMoment B raw25325step2 raw25325step2Labels := by
      have ha : raw25325step2 = raw25325step1 := by apply Matrix.ext; unfold raw25325step2 raw25325step1; decide +kernel
      have hl : raw25325step1Labels = labelEmbedding1 ∘ raw25325step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25325step1 raw25325step1Labels raw25325step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1406 node1406Labels := by rfl

def raw25326 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25326Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25326step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25326step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25326step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25326 raw25326Labels = mixedMoment B node1482 node1482Labels := by
  calc
    mixedMoment B raw25326 raw25326Labels = mixedMoment B raw25326step0 raw25326step0Labels := by
      have hz : ∀ j, raw25326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25326step0 = (fun i j => raw25326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25326step0 raw25326; decide +kernel
      have hl : raw25326step0Labels = raw25326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25326 raw25326Labels permutation346 hz
    mixedMoment B raw25326step0 raw25326step0Labels = mixedMoment B raw25326step1 raw25326step1Labels := by
      have ha : raw25326step1 = (fun i j => raw25326step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25326step1 raw25326step0; decide +kernel
      have hl : raw25326step1Labels = raw25326step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25326step0 raw25326step0Labels permutation32 permutation7
    mixedMoment B raw25326step1 raw25326step1Labels = mixedMoment B raw25326step2 raw25326step2Labels := by
      have ha : raw25326step2 = raw25326step1 := by apply Matrix.ext; unfold raw25326step2 raw25326step1; decide +kernel
      have hl : raw25326step1Labels = labelEmbedding1 ∘ raw25326step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25326step1 raw25326step1Labels raw25326step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1482 node1482Labels := by rfl

def raw25327 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25327Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25327step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25327step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25327step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25327step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25327step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25327step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25327step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25327 raw25327Labels = mixedMoment B node1447 node1447Labels := by
  calc
    mixedMoment B raw25327 raw25327Labels = mixedMoment B raw25327step0 raw25327step0Labels := by
      have hz : ∀ j, raw25327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25327step0 = (fun i j => raw25327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25327step0 raw25327; decide +kernel
      have hl : raw25327step0Labels = raw25327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25327 raw25327Labels permutation346 hz
    mixedMoment B raw25327step0 raw25327step0Labels = mixedMoment B raw25327step1 raw25327step1Labels := by
      have hz : ∀ j, raw25327step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25327step1 = (fun i j => raw25327step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25327step1 raw25327step0; decide +kernel
      have hl : raw25327step1Labels = raw25327step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25327step0 raw25327step0Labels permutation56 hz
    mixedMoment B raw25327step1 raw25327step1Labels = mixedMoment B raw25327step2 raw25327step2Labels := by
      have ha : raw25327step2 = (fun i j => raw25327step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25327step2 raw25327step1; decide +kernel
      have hl : raw25327step2Labels = raw25327step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25327step1 raw25327step1Labels permutation8 permutation7
    mixedMoment B raw25327step2 raw25327step2Labels = mixedMoment B raw25327step3 raw25327step3Labels := by
      have ha : raw25327step3 = raw25327step2 := by apply Matrix.ext; unfold raw25327step3 raw25327step2; decide +kernel
      have hl : raw25327step2Labels = labelEmbedding1 ∘ raw25327step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25327step2 raw25327step2Labels raw25327step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1447 node1447Labels := by rfl

def raw25328 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25328Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25328step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25328 raw25328Labels = mixedMoment B node1395 node1395Labels := by
  calc
    mixedMoment B raw25328 raw25328Labels = mixedMoment B raw25328step0 raw25328step0Labels := by
      have ha : raw25328step0 = (fun i j => raw25328 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25328step0 raw25328; decide +kernel
      have hl : raw25328step0Labels = raw25328Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25328 raw25328Labels permutation152 permutation7
    mixedMoment B raw25328step0 raw25328step0Labels = mixedMoment B raw25328step1 raw25328step1Labels := by
      have ha : raw25328step1 = raw25328step0 := by apply Matrix.ext; unfold raw25328step1 raw25328step0; decide +kernel
      have hl : raw25328step0Labels = labelEmbedding1 ∘ raw25328step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25328step0 raw25328step0Labels raw25328step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1395 node1395Labels := by rfl

def raw25329 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25329Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25329step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25329step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25329 raw25329Labels = mixedMoment B node1411 node1411Labels := by
  calc
    mixedMoment B raw25329 raw25329Labels = mixedMoment B raw25329step0 raw25329step0Labels := by
      have hz : ∀ j, raw25329 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25329step0 = (fun i j => raw25329 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25329step0 raw25329; decide +kernel
      have hl : raw25329step0Labels = raw25329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25329 raw25329Labels permutation346 hz
    mixedMoment B raw25329step0 raw25329step0Labels = mixedMoment B raw25329step1 raw25329step1Labels := by
      have ha : raw25329step1 = (fun i j => raw25329step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25329step1 raw25329step0; decide +kernel
      have hl : raw25329step1Labels = raw25329step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25329step0 raw25329step0Labels permutation34 permutation7
    mixedMoment B raw25329step1 raw25329step1Labels = mixedMoment B raw25329step2 raw25329step2Labels := by
      have ha : raw25329step2 = raw25329step1 := by apply Matrix.ext; unfold raw25329step2 raw25329step1; decide +kernel
      have hl : raw25329step1Labels = labelEmbedding1 ∘ raw25329step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25329step1 raw25329step1Labels raw25329step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1411 node1411Labels := by rfl

def raw25330 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25330Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25330step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25330step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25330 raw25330Labels = mixedMoment B node1410 node1410Labels := by
  calc
    mixedMoment B raw25330 raw25330Labels = mixedMoment B raw25330step0 raw25330step0Labels := by
      have hz : ∀ j, raw25330 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25330step0 = (fun i j => raw25330 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25330step0 raw25330; decide +kernel
      have hl : raw25330step0Labels = raw25330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25330 raw25330Labels permutation346 hz
    mixedMoment B raw25330step0 raw25330step0Labels = mixedMoment B raw25330step1 raw25330step1Labels := by
      have ha : raw25330step1 = (fun i j => raw25330step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25330step1 raw25330step0; decide +kernel
      have hl : raw25330step1Labels = raw25330step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25330step0 raw25330step0Labels permutation32 permutation7
    mixedMoment B raw25330step1 raw25330step1Labels = mixedMoment B raw25330step2 raw25330step2Labels := by
      have ha : raw25330step2 = raw25330step1 := by apply Matrix.ext; unfold raw25330step2 raw25330step1; decide +kernel
      have hl : raw25330step1Labels = labelEmbedding1 ∘ raw25330step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25330step1 raw25330step1Labels raw25330step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1410 node1410Labels := by rfl

def raw25331 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25331Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25331step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw25331step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25331step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25331step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25331step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25331 raw25331Labels = mixedMoment B node1483 node1483Labels := by
  calc
    mixedMoment B raw25331 raw25331Labels = mixedMoment B raw25331step0 raw25331step0Labels := by
      have hz : ∀ j, raw25331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25331step0 = (fun i j => raw25331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25331step0 raw25331; decide +kernel
      have hl : raw25331step0Labels = raw25331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25331 raw25331Labels permutation346 hz
    mixedMoment B raw25331step0 raw25331step0Labels = mixedMoment B raw25331step1 raw25331step1Labels := by
      have ha : raw25331step1 = (fun i j => raw25331step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw25331step1 raw25331step0; decide +kernel
      have hl : raw25331step1Labels = raw25331step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25331step0 raw25331step0Labels permutation46 permutation5
    mixedMoment B raw25331step1 raw25331step1Labels = mixedMoment B raw25331step2 raw25331step2Labels := by
      have ha : raw25331step2 = -raw25331step1 := by apply Matrix.ext; change ∀ i j, raw25331step2 i j = -(raw25331step1 i j); unfold raw25331step2 raw25331step1; decide +kernel
      have hl : raw25331step2Labels = raw25331step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25331step2 raw25331step2Labels = mixedMoment B raw25331step3 raw25331step3Labels := by
      have ha : raw25331step3 = raw25331step2 := by apply Matrix.ext; unfold raw25331step3 raw25331step2; decide +kernel
      have hl : raw25331step2Labels = labelEmbedding1 ∘ raw25331step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25331step2 raw25331step2Labels raw25331step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1483 node1483Labels := by rfl

def raw25332 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw25332Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25332step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25332step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25332 raw25332Labels = mixedMoment B node1396 node1396Labels := by
  calc
    mixedMoment B raw25332 raw25332Labels = mixedMoment B raw25332step0 raw25332step0Labels := by
      have ha : raw25332step0 = (fun i j => raw25332 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25332step0 raw25332; decide +kernel
      have hl : raw25332step0Labels = raw25332Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25332 raw25332Labels permutation152 permutation7
    mixedMoment B raw25332step0 raw25332step0Labels = mixedMoment B raw25332step1 raw25332step1Labels := by
      have ha : raw25332step1 = raw25332step0 := by apply Matrix.ext; unfold raw25332step1 raw25332step0; decide +kernel
      have hl : raw25332step0Labels = labelEmbedding1 ∘ raw25332step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25332step0 raw25332step0Labels raw25332step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1396 node1396Labels := by rfl

def raw25333 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25333Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw25333step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25333step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25333 raw25333Labels = mixedMoment B node1412 node1412Labels := by
  calc
    mixedMoment B raw25333 raw25333Labels = mixedMoment B raw25333step0 raw25333step0Labels := by
      have hz : ∀ j, raw25333 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25333step0 = (fun i j => raw25333 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25333step0 raw25333; decide +kernel
      have hl : raw25333step0Labels = raw25333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25333 raw25333Labels permutation346 hz
    mixedMoment B raw25333step0 raw25333step0Labels = mixedMoment B raw25333step1 raw25333step1Labels := by
      have ha : raw25333step1 = (fun i j => raw25333step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25333step1 raw25333step0; decide +kernel
      have hl : raw25333step1Labels = raw25333step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25333step0 raw25333step0Labels permutation32 permutation7
    mixedMoment B raw25333step1 raw25333step1Labels = mixedMoment B raw25333step2 raw25333step2Labels := by
      have ha : raw25333step2 = raw25333step1 := by apply Matrix.ext; unfold raw25333step2 raw25333step1; decide +kernel
      have hl : raw25333step1Labels = labelEmbedding1 ∘ raw25333step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25333step1 raw25333step1Labels raw25333step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1412 node1412Labels := by rfl

def raw25334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25334 raw25334Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw25334 raw25334Labels = mixedMoment B raw25334step0 raw25334step0Labels := by
      have hz : ∀ j, raw25334 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25334step0 = (fun i j => raw25334 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25334step0 raw25334; decide +kernel
      have hl : raw25334step0Labels = raw25334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25334 raw25334Labels permutation346 hz
    mixedMoment B raw25334step0 raw25334step0Labels = mixedMoment B raw25334step1 raw25334step1Labels := by
      have ha : raw25334step1 = (fun i j => raw25334step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25334step1 raw25334step0; decide +kernel
      have hl : raw25334step1Labels = raw25334step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25334step0 raw25334step0Labels permutation34 permutation2
    _ = mixedMoment B node1035 node1035Labels := by rfl

def raw25335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25335 raw25335Labels = mixedMoment B node2101 node2101Labels := by
  calc
    mixedMoment B raw25335 raw25335Labels = mixedMoment B raw25335step0 raw25335step0Labels := by
      have hz : ∀ j, raw25335 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25335step0 = (fun i j => raw25335 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25335step0 raw25335; decide +kernel
      have hl : raw25335step0Labels = raw25335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25335 raw25335Labels permutation346 hz
    mixedMoment B raw25335step0 raw25335step0Labels = mixedMoment B raw25335step1 raw25335step1Labels := by
      have ha : raw25335step1 = (fun i j => raw25335step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25335step1 raw25335step0; decide +kernel
      have hl : raw25335step1Labels = raw25335step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25335step0 raw25335step0Labels permutation34 permutation2
    _ = mixedMoment B node2101 node2101Labels := by rfl

def raw25336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25336 raw25336Labels = mixedMoment B node2016 node2016Labels := by
  calc
    mixedMoment B raw25336 raw25336Labels = mixedMoment B raw25336step0 raw25336step0Labels := by
      have ha : raw25336step0 = (fun i j => raw25336 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25336step0 raw25336; decide +kernel
      have hl : raw25336step0Labels = raw25336Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25336 raw25336Labels permutation178 permutation2
    _ = mixedMoment B node2016 node2016Labels := by rfl

def raw25337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25337 raw25337Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw25337 raw25337Labels = mixedMoment B raw25337step0 raw25337step0Labels := by
      have hz : ∀ j, raw25337 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25337step0 = (fun i j => raw25337 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25337step0 raw25337; decide +kernel
      have hl : raw25337step0Labels = raw25337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25337 raw25337Labels permutation346 hz
    _ = mixedMoment B node2242 node2242Labels := by rfl

def raw25338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw25338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw25338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25338 raw25338Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw25338 raw25338Labels = mixedMoment B raw25338step0 raw25338step0Labels := by
      have hz : ∀ j, raw25338 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25338step0 = (fun i j => raw25338 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25338step0 raw25338; decide +kernel
      have hl : raw25338step0Labels = raw25338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25338 raw25338Labels permutation346 hz
    mixedMoment B raw25338step0 raw25338step0Labels = mixedMoment B raw25338step1 raw25338step1Labels := by
      have ha : raw25338step1 = (fun i j => raw25338step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25338step1 raw25338step0; decide +kernel
      have hl : raw25338step1Labels = raw25338step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25338step0 raw25338step0Labels permutation44 permutation2
    _ = mixedMoment B node2205 node2205Labels := by rfl

def raw25339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw25339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw25339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25339 raw25339Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw25339 raw25339Labels = mixedMoment B raw25339step0 raw25339step0Labels := by
      have hz : ∀ j, raw25339 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25339step0 = (fun i j => raw25339 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25339step0 raw25339; decide +kernel
      have hl : raw25339step0Labels = raw25339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25339 raw25339Labels permutation346 hz
    mixedMoment B raw25339step0 raw25339step0Labels = mixedMoment B raw25339step1 raw25339step1Labels := by
      have ha : raw25339step1 = (fun i j => raw25339step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25339step1 raw25339step0; decide +kernel
      have hl : raw25339step1Labels = raw25339step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25339step0 raw25339step0Labels permutation34 permutation2
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw25340 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![-1, 1], ![2, -2]]
def raw25340Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25340step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![-1, 1], ![2, -2]]
def raw25340step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25340step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw25340step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical25340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25340 raw25340Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw25340 raw25340Labels = mixedMoment B raw25340step0 raw25340step0Labels := by
      have hz : ∀ j, raw25340 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25340step0 = (fun i j => raw25340 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25340step0 raw25340; decide +kernel
      have hl : raw25340step0Labels = raw25340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25340 raw25340Labels permutation346 hz
    mixedMoment B raw25340step0 raw25340step0Labels = mixedMoment B raw25340step1 raw25340step1Labels := by
      have ha : raw25340step1 = (fun i j => raw25340step0 (permutation44 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25340step1 raw25340step0; decide +kernel
      have hl : raw25340step1Labels = raw25340step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25340step0 raw25340step0Labels permutation44 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw25341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25341 raw25341Labels = mixedMoment B node593 node593Labels := by
  calc
    mixedMoment B raw25341 raw25341Labels = mixedMoment B raw25341step0 raw25341step0Labels := by
      have hz : ∀ j, raw25341 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25341step0 = (fun i j => raw25341 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25341step0 raw25341; decide +kernel
      have hl : raw25341step0Labels = raw25341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25341 raw25341Labels permutation346 hz
    mixedMoment B raw25341step0 raw25341step0Labels = mixedMoment B raw25341step1 raw25341step1Labels := by
      have ha : raw25341step1 = (fun i j => raw25341step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25341step1 raw25341step0; decide +kernel
      have hl : raw25341step1Labels = raw25341step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25341step0 raw25341step0Labels permutation44 permutation2
    _ = mixedMoment B node593 node593Labels := by rfl

def raw25342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw25342step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25342 raw25342Labels = mixedMoment B node915 node915Labels := by
  calc
    mixedMoment B raw25342 raw25342Labels = mixedMoment B raw25342step0 raw25342step0Labels := by
      have ha : raw25342step0 = (fun i j => raw25342 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25342step0 raw25342; decide +kernel
      have hl : raw25342step0Labels = raw25342Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25342 raw25342Labels permutation188 permutation2
    _ = mixedMoment B node915 node915Labels := by rfl

def raw25343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw25343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw25343step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25343 raw25343Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw25343 raw25343Labels = mixedMoment B raw25343step0 raw25343step0Labels := by
      have hz : ∀ j, raw25343 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25343step0 = (fun i j => raw25343 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25343step0 raw25343; decide +kernel
      have hl : raw25343step0Labels = raw25343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25343 raw25343Labels permutation346 hz
    mixedMoment B raw25343step0 raw25343step0Labels = mixedMoment B raw25343step1 raw25343step1Labels := by
      have ha : raw25343step1 = (fun i j => raw25343step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25343step1 raw25343step0; decide +kernel
      have hl : raw25343step1Labels = raw25343step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25343step0 raw25343step0Labels permutation40 permutation2
    _ = mixedMoment B node1035 node1035Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
