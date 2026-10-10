import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw10752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10752Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10752step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw10752step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10752step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw10752step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10752step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10752step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10752step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10752step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10752 raw10752Labels = mixedMoment B node1740 node1740Labels := by
  calc
    mixedMoment B raw10752 raw10752Labels = mixedMoment B raw10752step0 raw10752step0Labels := by
      have hz : ∀ j, raw10752 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10752step0 = (fun i j => raw10752 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10752step0 raw10752; decide +kernel
      have hl : raw10752step0Labels = raw10752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10752 raw10752Labels permutation434 hz
    mixedMoment B raw10752step0 raw10752step0Labels = mixedMoment B raw10752step1 raw10752step1Labels := by
      have hz : ∀ j, raw10752step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10752step1 = (fun i j => raw10752step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10752step1 raw10752step0; decide +kernel
      have hl : raw10752step1Labels = raw10752step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10752step0 raw10752step0Labels permutation80 hz
    mixedMoment B raw10752step1 raw10752step1Labels = mixedMoment B raw10752step2 raw10752step2Labels := by
      have ha : raw10752step2 = (fun i j => raw10752step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10752step2 raw10752step1; decide +kernel
      have hl : raw10752step2Labels = raw10752step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10752step1 raw10752step1Labels permutation13 permutation7
    mixedMoment B raw10752step2 raw10752step2Labels = mixedMoment B raw10752step3 raw10752step3Labels := by
      have ha : raw10752step3 = -raw10752step2 := by apply Matrix.ext; change ∀ i j, raw10752step3 i j = -(raw10752step2 i j); unfold raw10752step3 raw10752step2; decide +kernel
      have hl : raw10752step3Labels = raw10752step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10752step3 raw10752step3Labels = mixedMoment B raw10752step4 raw10752step4Labels := by
      have ha : raw10752step4 = raw10752step3 := by apply Matrix.ext; unfold raw10752step4 raw10752step3; decide +kernel
      have hl : raw10752step3Labels = labelEmbedding1 ∘ raw10752step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10752step3 raw10752step3Labels raw10752step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1740 node1740Labels := by rfl

def raw10753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10753Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10753step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -1, -1], ![2, -2, 0]]
def raw10753step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10753step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, -1, 2], ![-2, 3, -1]]
def raw10753step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10753step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw10753step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10753step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw10753step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10753 raw10753Labels = mixedMoment B node2280 node2280Labels := by
  calc
    mixedMoment B raw10753 raw10753Labels = mixedMoment B raw10753step0 raw10753step0Labels := by
      have hz : ∀ j, raw10753 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10753step0 = (fun i j => raw10753 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10753step0 raw10753; decide +kernel
      have hl : raw10753step0Labels = raw10753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10753 raw10753Labels permutation434 hz
    mixedMoment B raw10753step0 raw10753step0Labels = mixedMoment B raw10753step1 raw10753step1Labels := by
      have hz : ∀ j, raw10753step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10753step1 = (fun i j => raw10753step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10753step1 raw10753step0; decide +kernel
      have hl : raw10753step1Labels = raw10753step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10753step0 raw10753step0Labels permutation80 hz
    mixedMoment B raw10753step1 raw10753step1Labels = mixedMoment B raw10753step2 raw10753step2Labels := by
      have ha : raw10753step2 = (fun i j => raw10753step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10753step2 raw10753step1; decide +kernel
      have hl : raw10753step2Labels = raw10753step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10753step1 raw10753step1Labels permutation13 permutation7
    mixedMoment B raw10753step2 raw10753step2Labels = mixedMoment B raw10753step3 raw10753step3Labels := by
      have ha : raw10753step3 = -raw10753step2 := by apply Matrix.ext; change ∀ i j, raw10753step3 i j = -(raw10753step2 i j); unfold raw10753step3 raw10753step2; decide +kernel
      have hl : raw10753step3Labels = raw10753step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10753step3 raw10753step3Labels = mixedMoment B raw10753step4 raw10753step4Labels := by
      have ha : raw10753step4 = raw10753step3 := by apply Matrix.ext; unfold raw10753step4 raw10753step3; decide +kernel
      have hl : raw10753step3Labels = labelEmbedding1 ∘ raw10753step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10753step3 raw10753step3Labels raw10753step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2280 node2280Labels := by rfl

def raw10754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10754Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10754step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw10754step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10754step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10754step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10754step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10754 raw10754Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw10754 raw10754Labels = mixedMoment B raw10754step0 raw10754step0Labels := by
      have hz : ∀ j, raw10754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10754step0 = (fun i j => raw10754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10754step0 raw10754; decide +kernel
      have hl : raw10754step0Labels = raw10754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10754 raw10754Labels permutation434 hz
    mixedMoment B raw10754step0 raw10754step0Labels = mixedMoment B raw10754step1 raw10754step1Labels := by
      have ha : raw10754step1 = (fun i j => raw10754step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10754step1 raw10754step0; decide +kernel
      have hl : raw10754step1Labels = raw10754step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10754step0 raw10754step0Labels permutation43 permutation7
    mixedMoment B raw10754step1 raw10754step1Labels = mixedMoment B raw10754step2 raw10754step2Labels := by
      have ha : raw10754step2 = -raw10754step1 := by apply Matrix.ext; change ∀ i j, raw10754step2 i j = -(raw10754step1 i j); unfold raw10754step2 raw10754step1; decide +kernel
      have hl : raw10754step2Labels = raw10754step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10754step2 raw10754step2Labels = mixedMoment B raw10754step3 raw10754step3Labels := by
      have ha : raw10754step3 = raw10754step2 := by apply Matrix.ext; unfold raw10754step3 raw10754step2; decide +kernel
      have hl : raw10754step2Labels = labelEmbedding1 ∘ raw10754step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10754step2 raw10754step2Labels raw10754step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2217 node2217Labels := by rfl

def raw10755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10755Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw10755step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw10755step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10755step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10755step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10755step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10755step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10755 raw10755Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw10755 raw10755Labels = mixedMoment B raw10755step0 raw10755step0Labels := by
      have hz : ∀ j, raw10755 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10755step0 = (fun i j => raw10755 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10755step0 raw10755; decide +kernel
      have hl : raw10755step0Labels = raw10755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10755 raw10755Labels permutation346 hz
    mixedMoment B raw10755step0 raw10755step0Labels = mixedMoment B raw10755step1 raw10755step1Labels := by
      have ha : raw10755step1 = (fun i j => raw10755step0 (permutation43 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10755step1 raw10755step0; decide +kernel
      have hl : raw10755step1Labels = raw10755step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10755step0 raw10755step0Labels permutation43 permutation7
    mixedMoment B raw10755step1 raw10755step1Labels = mixedMoment B raw10755step2 raw10755step2Labels := by
      have ha : raw10755step2 = -raw10755step1 := by apply Matrix.ext; change ∀ i j, raw10755step2 i j = -(raw10755step1 i j); unfold raw10755step2 raw10755step1; decide +kernel
      have hl : raw10755step2Labels = raw10755step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10755step2 raw10755step2Labels = mixedMoment B raw10755step3 raw10755step3Labels := by
      have ha : raw10755step3 = raw10755step2 := by apply Matrix.ext; unfold raw10755step3 raw10755step2; decide +kernel
      have hl : raw10755step2Labels = labelEmbedding1 ∘ raw10755step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10755step2 raw10755step2Labels raw10755step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2217 node2217Labels := by rfl

def raw10756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw10756Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw10756step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10756step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw10756step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10756step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10756step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10756step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10756step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10756step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10756step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10756 raw10756Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw10756 raw10756Labels = mixedMoment B raw10756step0 raw10756step0Labels := by
      have hz : ∀ j, raw10756 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10756step0 = (fun i j => raw10756 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10756step0 raw10756; decide +kernel
      have hl : raw10756step0Labels = raw10756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10756 raw10756Labels permutation434 hz
    mixedMoment B raw10756step0 raw10756step0Labels = mixedMoment B raw10756step1 raw10756step1Labels := by
      have hz : ∀ j, raw10756step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10756step1 = (fun i j => raw10756step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10756step1 raw10756step0; decide +kernel
      have hl : raw10756step1Labels = raw10756step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10756step0 raw10756step0Labels permutation80 hz
    mixedMoment B raw10756step1 raw10756step1Labels = mixedMoment B raw10756step2 raw10756step2Labels := by
      have ha : raw10756step2 = (fun i j => raw10756step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10756step2 raw10756step1; decide +kernel
      have hl : raw10756step2Labels = raw10756step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10756step1 raw10756step1Labels permutation13 permutation7
    mixedMoment B raw10756step2 raw10756step2Labels = mixedMoment B raw10756step3 raw10756step3Labels := by
      have ha : raw10756step3 = -raw10756step2 := by apply Matrix.ext; change ∀ i j, raw10756step3 i j = -(raw10756step2 i j); unfold raw10756step3 raw10756step2; decide +kernel
      have hl : raw10756step3Labels = raw10756step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10756step3 raw10756step3Labels = mixedMoment B raw10756step4 raw10756step4Labels := by
      have ha : raw10756step4 = raw10756step3 := by apply Matrix.ext; unfold raw10756step4 raw10756step3; decide +kernel
      have hl : raw10756step3Labels = labelEmbedding1 ∘ raw10756step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10756step3 raw10756step3Labels raw10756step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw10757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10757Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10757step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10757step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw10757step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10757step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]
def raw10757step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10757step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw10757step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10757step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw10757step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10757 raw10757Labels = mixedMoment B node1746 node1746Labels := by
  calc
    mixedMoment B raw10757 raw10757Labels = mixedMoment B raw10757step0 raw10757step0Labels := by
      have hz : ∀ j, raw10757 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10757step0 = (fun i j => raw10757 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10757step0 raw10757; decide +kernel
      have hl : raw10757step0Labels = raw10757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10757 raw10757Labels permutation434 hz
    mixedMoment B raw10757step0 raw10757step0Labels = mixedMoment B raw10757step1 raw10757step1Labels := by
      have hz : ∀ j, raw10757step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10757step1 = (fun i j => raw10757step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10757step1 raw10757step0; decide +kernel
      have hl : raw10757step1Labels = raw10757step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10757step0 raw10757step0Labels permutation80 hz
    mixedMoment B raw10757step1 raw10757step1Labels = mixedMoment B raw10757step2 raw10757step2Labels := by
      have ha : raw10757step2 = (fun i j => raw10757step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10757step2 raw10757step1; decide +kernel
      have hl : raw10757step2Labels = raw10757step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10757step1 raw10757step1Labels permutation13 permutation7
    mixedMoment B raw10757step2 raw10757step2Labels = mixedMoment B raw10757step3 raw10757step3Labels := by
      have ha : raw10757step3 = -raw10757step2 := by apply Matrix.ext; change ∀ i j, raw10757step3 i j = -(raw10757step2 i j); unfold raw10757step3 raw10757step2; decide +kernel
      have hl : raw10757step3Labels = raw10757step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10757step3 raw10757step3Labels = mixedMoment B raw10757step4 raw10757step4Labels := by
      have ha : raw10757step4 = raw10757step3 := by apply Matrix.ext; unfold raw10757step4 raw10757step3; decide +kernel
      have hl : raw10757step3Labels = labelEmbedding1 ∘ raw10757step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10757step3 raw10757step3Labels raw10757step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1746 node1746Labels := by rfl

def raw10758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10758Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10758step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10758step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw10758step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10758step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw10758step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10758step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw10758step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10758 raw10758Labels = mixedMoment B node2222 node2222Labels := by
  calc
    mixedMoment B raw10758 raw10758Labels = mixedMoment B raw10758step0 raw10758step0Labels := by
      have hz : ∀ j, raw10758 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10758step0 = (fun i j => raw10758 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10758step0 raw10758; decide +kernel
      have hl : raw10758step0Labels = raw10758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10758 raw10758Labels permutation434 hz
    mixedMoment B raw10758step0 raw10758step0Labels = mixedMoment B raw10758step1 raw10758step1Labels := by
      have hz : ∀ j, raw10758step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10758step1 = (fun i j => raw10758step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10758step1 raw10758step0; decide +kernel
      have hl : raw10758step1Labels = raw10758step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10758step0 raw10758step0Labels permutation80 hz
    mixedMoment B raw10758step1 raw10758step1Labels = mixedMoment B raw10758step2 raw10758step2Labels := by
      have ha : raw10758step2 = (fun i j => raw10758step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10758step2 raw10758step1; decide +kernel
      have hl : raw10758step2Labels = raw10758step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10758step1 raw10758step1Labels permutation30 permutation5
    mixedMoment B raw10758step2 raw10758step2Labels = mixedMoment B raw10758step3 raw10758step3Labels := by
      have ha : raw10758step3 = raw10758step2 := by apply Matrix.ext; unfold raw10758step3 raw10758step2; decide +kernel
      have hl : raw10758step2Labels = labelEmbedding1 ∘ raw10758step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10758step2 raw10758step2Labels raw10758step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2222 node2222Labels := by rfl

def raw10759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10759Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10759step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw10759step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw10759step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10759 raw10759Labels = mixedMoment B node2221 node2221Labels := by
  calc
    mixedMoment B raw10759 raw10759Labels = mixedMoment B raw10759step0 raw10759step0Labels := by
      have hz : ∀ j, raw10759 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10759step0 = (fun i j => raw10759 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10759step0 raw10759; decide +kernel
      have hl : raw10759step0Labels = raw10759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10759 raw10759Labels permutation434 hz
    mixedMoment B raw10759step0 raw10759step0Labels = mixedMoment B raw10759step1 raw10759step1Labels := by
      have ha : raw10759step1 = (fun i j => raw10759step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10759step1 raw10759step0; decide +kernel
      have hl : raw10759step1Labels = raw10759step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10759step0 raw10759step0Labels permutation147 permutation5
    mixedMoment B raw10759step1 raw10759step1Labels = mixedMoment B raw10759step2 raw10759step2Labels := by
      have ha : raw10759step2 = raw10759step1 := by apply Matrix.ext; unfold raw10759step2 raw10759step1; decide +kernel
      have hl : raw10759step1Labels = labelEmbedding1 ∘ raw10759step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10759step1 raw10759step1Labels raw10759step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2221 node2221Labels := by rfl

def raw10760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10760Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw10760step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw10760step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10760step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw10760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10760 raw10760Labels = mixedMoment B node2221 node2221Labels := by
  calc
    mixedMoment B raw10760 raw10760Labels = mixedMoment B raw10760step0 raw10760step0Labels := by
      have hz : ∀ j, raw10760 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10760step0 = (fun i j => raw10760 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10760step0 raw10760; decide +kernel
      have hl : raw10760step0Labels = raw10760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10760 raw10760Labels permutation346 hz
    mixedMoment B raw10760step0 raw10760step0Labels = mixedMoment B raw10760step1 raw10760step1Labels := by
      have ha : raw10760step1 = (fun i j => raw10760step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10760step1 raw10760step0; decide +kernel
      have hl : raw10760step1Labels = raw10760step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10760step0 raw10760step0Labels permutation147 permutation5
    mixedMoment B raw10760step1 raw10760step1Labels = mixedMoment B raw10760step2 raw10760step2Labels := by
      have ha : raw10760step2 = raw10760step1 := by apply Matrix.ext; unfold raw10760step2 raw10760step1; decide +kernel
      have hl : raw10760step1Labels = labelEmbedding1 ∘ raw10760step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10760step1 raw10760step1Labels raw10760step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2221 node2221Labels := by rfl

def raw10761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw10761Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw10761step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw10761step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10761step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw10761step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10761step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw10761step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10761 raw10761Labels = mixedMoment B node2284 node2284Labels := by
  calc
    mixedMoment B raw10761 raw10761Labels = mixedMoment B raw10761step0 raw10761step0Labels := by
      have hz : ∀ j, raw10761 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10761step0 = (fun i j => raw10761 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10761step0 raw10761; decide +kernel
      have hl : raw10761step0Labels = raw10761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10761 raw10761Labels permutation434 hz
    mixedMoment B raw10761step0 raw10761step0Labels = mixedMoment B raw10761step1 raw10761step1Labels := by
      have hz : ∀ j, raw10761step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10761step1 = (fun i j => raw10761step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10761step1 raw10761step0; decide +kernel
      have hl : raw10761step1Labels = raw10761step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10761step0 raw10761step0Labels permutation80 hz
    mixedMoment B raw10761step1 raw10761step1Labels = mixedMoment B raw10761step2 raw10761step2Labels := by
      have ha : raw10761step2 = (fun i j => raw10761step1 (permutation27 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10761step2 raw10761step1; decide +kernel
      have hl : raw10761step2Labels = raw10761step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10761step1 raw10761step1Labels permutation27 permutation5
    mixedMoment B raw10761step2 raw10761step2Labels = mixedMoment B raw10761step3 raw10761step3Labels := by
      have ha : raw10761step3 = raw10761step2 := by apply Matrix.ext; unfold raw10761step3 raw10761step2; decide +kernel
      have hl : raw10761step2Labels = labelEmbedding1 ∘ raw10761step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10761step2 raw10761step2Labels raw10761step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2284 node2284Labels := by rfl

def raw10762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10762 raw10762Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw10762 raw10762Labels = mixedMoment B raw10762step0 raw10762step0Labels := by
      have hz : ∀ j, raw10762 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10762step0 = (fun i j => raw10762 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10762step0 raw10762; decide +kernel
      have hl : raw10762step0Labels = raw10762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10762 raw10762Labels permutation434 hz
    mixedMoment B raw10762step0 raw10762step0Labels = mixedMoment B raw10762step1 raw10762step1Labels := by
      have hz : ∀ j, raw10762step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10762step1 = (fun i j => raw10762step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10762step1 raw10762step0; decide +kernel
      have hl : raw10762step1Labels = raw10762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10762step0 raw10762step0Labels permutation80 hz
    mixedMoment B raw10762step1 raw10762step1Labels = mixedMoment B raw10762step2 raw10762step2Labels := by
      have ha : raw10762step2 = (fun i j => raw10762step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10762step2 raw10762step1; decide +kernel
      have hl : raw10762step2Labels = raw10762step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10762step1 raw10762step1Labels permutation10 permutation2
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw10763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10763step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10763 raw10763Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw10763 raw10763Labels = mixedMoment B raw10763step0 raw10763step0Labels := by
      have hz : ∀ j, raw10763 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10763step0 = (fun i j => raw10763 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10763step0 raw10763; decide +kernel
      have hl : raw10763step0Labels = raw10763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10763 raw10763Labels permutation434 hz
    mixedMoment B raw10763step0 raw10763step0Labels = mixedMoment B raw10763step1 raw10763step1Labels := by
      have hz : ∀ j, raw10763step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10763step1 = (fun i j => raw10763step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10763step1 raw10763step0; decide +kernel
      have hl : raw10763step1Labels = raw10763step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10763step0 raw10763step0Labels permutation80 hz
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw10764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10764step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10764 raw10764Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw10764 raw10764Labels = mixedMoment B raw10764step0 raw10764step0Labels := by
      have hz : ∀ j, raw10764 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10764step0 = (fun i j => raw10764 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10764step0 raw10764; decide +kernel
      have hl : raw10764step0Labels = raw10764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10764 raw10764Labels permutation434 hz
    mixedMoment B raw10764step0 raw10764step0Labels = mixedMoment B raw10764step1 raw10764step1Labels := by
      have ha : raw10764step1 = (fun i j => raw10764step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10764step1 raw10764step0; decide +kernel
      have hl : raw10764step1Labels = raw10764step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10764step0 raw10764step0Labels permutation40 permutation2
    _ = mixedMoment B node2058 node2058Labels := by rfl

def raw10765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10765step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10765step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10765 raw10765Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw10765 raw10765Labels = mixedMoment B raw10765step0 raw10765step0Labels := by
      have hz : ∀ j, raw10765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10765step0 = (fun i j => raw10765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10765step0 raw10765; decide +kernel
      have hl : raw10765step0Labels = raw10765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10765 raw10765Labels permutation346 hz
    mixedMoment B raw10765step0 raw10765step0Labels = mixedMoment B raw10765step1 raw10765step1Labels := by
      have ha : raw10765step1 = (fun i j => raw10765step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10765step1 raw10765step0; decide +kernel
      have hl : raw10765step1Labels = raw10765step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10765step0 raw10765step0Labels permutation40 permutation2
    _ = mixedMoment B node2058 node2058Labels := by rfl

def raw10766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw10766step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10766step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw10766step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10766step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10766 raw10766Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw10766 raw10766Labels = mixedMoment B raw10766step0 raw10766step0Labels := by
      have hz : ∀ j, raw10766 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10766step0 = (fun i j => raw10766 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10766step0 raw10766; decide +kernel
      have hl : raw10766step0Labels = raw10766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10766 raw10766Labels permutation434 hz
    mixedMoment B raw10766step0 raw10766step0Labels = mixedMoment B raw10766step1 raw10766step1Labels := by
      have hz : ∀ j, raw10766step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10766step1 = (fun i j => raw10766step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10766step1 raw10766step0; decide +kernel
      have hl : raw10766step1Labels = raw10766step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10766step0 raw10766step0Labels permutation80 hz
    mixedMoment B raw10766step1 raw10766step1Labels = mixedMoment B raw10766step2 raw10766step2Labels := by
      have ha : raw10766step2 = (fun i j => raw10766step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10766step2 raw10766step1; decide +kernel
      have hl : raw10766step2Labels = raw10766step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10766step1 raw10766step1Labels permutation10 permutation2
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw10767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10767Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw10767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10767step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw10767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10767step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10767step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10767 raw10767Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw10767 raw10767Labels = mixedMoment B raw10767step0 raw10767step0Labels := by
      have hz : ∀ j, raw10767 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10767step0 = (fun i j => raw10767 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10767step0 raw10767; decide +kernel
      have hl : raw10767step0Labels = raw10767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10767 raw10767Labels permutation434 hz
    mixedMoment B raw10767step0 raw10767step0Labels = mixedMoment B raw10767step1 raw10767step1Labels := by
      have hz : ∀ j, raw10767step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10767step1 = (fun i j => raw10767step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10767step1 raw10767step0; decide +kernel
      have hl : raw10767step1Labels = raw10767step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10767step0 raw10767step0Labels permutation80 hz
    mixedMoment B raw10767step1 raw10767step1Labels = mixedMoment B raw10767step2 raw10767step2Labels := by
      have ha : raw10767step2 = (fun i j => raw10767step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10767step2 raw10767step1; decide +kernel
      have hl : raw10767step2Labels = raw10767step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10767step1 raw10767step1Labels permutation13 permutation2
    _ = mixedMoment B node2291 node2291Labels := by rfl

def raw10768 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![0, 0], ![1, -1], ![0, 0]]
def raw10768Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10768step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![0, 0], ![1, -1]]
def raw10768step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10768step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![1, -1]]
def raw10768step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10768step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw10768step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10768step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw10768step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical10768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10768 raw10768Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw10768 raw10768Labels = mixedMoment B raw10768step0 raw10768step0Labels := by
      have hz : ∀ j, raw10768 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw10768step0 = (fun i j => raw10768 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw10768step0 raw10768; decide +kernel
      have hl : raw10768step0Labels = raw10768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10768 raw10768Labels permutation590 hz
    mixedMoment B raw10768step0 raw10768step0Labels = mixedMoment B raw10768step1 raw10768step1Labels := by
      have hz : ∀ j, raw10768step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10768step1 = (fun i j => raw10768step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10768step1 raw10768step0; decide +kernel
      have hl : raw10768step1Labels = raw10768step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10768step0 raw10768step0Labels permutation104 hz
    mixedMoment B raw10768step1 raw10768step1Labels = mixedMoment B raw10768step2 raw10768step2Labels := by
      have hz : ∀ j, raw10768step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10768step2 = (fun i j => raw10768step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10768step2 raw10768step1; decide +kernel
      have hl : raw10768step2Labels = raw10768step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10768step1 raw10768step1Labels permutation20 hz
    mixedMoment B raw10768step2 raw10768step2Labels = mixedMoment B raw10768step3 raw10768step3Labels := by
      have ha : raw10768step3 = (fun i j => raw10768step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw10768step3 raw10768step2; decide +kernel
      have hl : raw10768step3Labels = raw10768step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10768step2 raw10768step2Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw10769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw10769step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10769step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw10769step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10769step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10769step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10769 raw10769Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw10769 raw10769Labels = mixedMoment B raw10769step0 raw10769step0Labels := by
      have hz : ∀ j, raw10769 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10769step0 = (fun i j => raw10769 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10769step0 raw10769; decide +kernel
      have hl : raw10769step0Labels = raw10769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10769 raw10769Labels permutation434 hz
    mixedMoment B raw10769step0 raw10769step0Labels = mixedMoment B raw10769step1 raw10769step1Labels := by
      have hz : ∀ j, raw10769step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10769step1 = (fun i j => raw10769step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10769step1 raw10769step0; decide +kernel
      have hl : raw10769step1Labels = raw10769step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10769step0 raw10769step0Labels permutation80 hz
    mixedMoment B raw10769step1 raw10769step1Labels = mixedMoment B raw10769step2 raw10769step2Labels := by
      have ha : raw10769step2 = (fun i j => raw10769step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10769step2 raw10769step1; decide +kernel
      have hl : raw10769step2Labels = raw10769step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10769step1 raw10769step1Labels permutation31 permutation2
    mixedMoment B raw10769step2 raw10769step2Labels = mixedMoment B raw10769step3 raw10769step3Labels := by
      have ha : raw10769step3 = -raw10769step2 := by apply Matrix.ext; change ∀ i j, raw10769step3 i j = -(raw10769step2 i j); unfold raw10769step3 raw10769step2; decide +kernel
      have hl : raw10769step3Labels = raw10769step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw10770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10770step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10770step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10770 raw10770Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw10770 raw10770Labels = mixedMoment B raw10770step0 raw10770step0Labels := by
      have hz : ∀ j, raw10770 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10770step0 = (fun i j => raw10770 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10770step0 raw10770; decide +kernel
      have hl : raw10770step0Labels = raw10770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10770 raw10770Labels permutation434 hz
    mixedMoment B raw10770step0 raw10770step0Labels = mixedMoment B raw10770step1 raw10770step1Labels := by
      have ha : raw10770step1 = (fun i j => raw10770step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10770step1 raw10770step0; decide +kernel
      have hl : raw10770step1Labels = raw10770step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10770step0 raw10770step0Labels permutation38 permutation3
    mixedMoment B raw10770step1 raw10770step1Labels = mixedMoment B raw10770step2 raw10770step2Labels := by
      have ha : raw10770step2 = raw10770step1 := by apply Matrix.ext; unfold raw10770step2 raw10770step1; decide +kernel
      have hl : raw10770step1Labels = labelEmbedding6 ∘ raw10770step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10770step1 raw10770step1Labels raw10770step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw10771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10771step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10771step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10771 raw10771Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw10771 raw10771Labels = mixedMoment B raw10771step0 raw10771step0Labels := by
      have hz : ∀ j, raw10771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10771step0 = (fun i j => raw10771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10771step0 raw10771; decide +kernel
      have hl : raw10771step0Labels = raw10771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10771 raw10771Labels permutation346 hz
    mixedMoment B raw10771step0 raw10771step0Labels = mixedMoment B raw10771step1 raw10771step1Labels := by
      have ha : raw10771step1 = (fun i j => raw10771step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10771step1 raw10771step0; decide +kernel
      have hl : raw10771step1Labels = raw10771step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10771step0 raw10771step0Labels permutation38 permutation3
    mixedMoment B raw10771step1 raw10771step1Labels = mixedMoment B raw10771step2 raw10771step2Labels := by
      have ha : raw10771step2 = raw10771step1 := by apply Matrix.ext; unfold raw10771step2 raw10771step1; decide +kernel
      have hl : raw10771step1Labels = labelEmbedding6 ∘ raw10771step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10771step1 raw10771step1Labels raw10771step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw10772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw10772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw10772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10772step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw10772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10772step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![2, 0, -2]]
def raw10772step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10772step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, 2, 0]]
def raw10772step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10772step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw10772step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10772 raw10772Labels = mixedMoment B node5456 node5456Labels := by
  calc
    mixedMoment B raw10772 raw10772Labels = mixedMoment B raw10772step0 raw10772step0Labels := by
      have hz : ∀ j, raw10772 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10772step0 = (fun i j => raw10772 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10772step0 raw10772; decide +kernel
      have hl : raw10772step0Labels = raw10772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10772 raw10772Labels permutation520 hz
    mixedMoment B raw10772step0 raw10772step0Labels = mixedMoment B raw10772step1 raw10772step1Labels := by
      have hz : ∀ j, raw10772step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10772step1 = (fun i j => raw10772step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10772step1 raw10772step0; decide +kernel
      have hl : raw10772step1Labels = raw10772step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10772step0 raw10772step0Labels permutation104 hz
    mixedMoment B raw10772step1 raw10772step1Labels = mixedMoment B raw10772step2 raw10772step2Labels := by
      have hz : ∀ j, raw10772step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10772step2 = (fun i j => raw10772step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10772step2 raw10772step1; decide +kernel
      have hl : raw10772step2Labels = raw10772step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10772step1 raw10772step1Labels permutation20 hz
    mixedMoment B raw10772step2 raw10772step2Labels = mixedMoment B raw10772step3 raw10772step3Labels := by
      have ha : raw10772step3 = (fun i j => raw10772step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10772step3 raw10772step2; decide +kernel
      have hl : raw10772step3Labels = raw10772step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10772step2 raw10772step2Labels permutation7 permutation2
    mixedMoment B raw10772step3 raw10772step3Labels = mixedMoment B raw10772step4 raw10772step4Labels := by
      have ha : raw10772step4 = -raw10772step3 := by apply Matrix.ext; change ∀ i j, raw10772step4 i j = -(raw10772step3 i j); unfold raw10772step4 raw10772step3; decide +kernel
      have hl : raw10772step4Labels = raw10772step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5456 node5456Labels := by rfl

def raw10773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw10773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10773step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10773step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10773step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10773step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10773 raw10773Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw10773 raw10773Labels = mixedMoment B raw10773step0 raw10773step0Labels := by
      have hz : ∀ j, raw10773 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10773step0 = (fun i j => raw10773 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10773step0 raw10773; decide +kernel
      have hl : raw10773step0Labels = raw10773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10773 raw10773Labels permutation434 hz
    mixedMoment B raw10773step0 raw10773step0Labels = mixedMoment B raw10773step1 raw10773step1Labels := by
      have hz : ∀ j, raw10773step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10773step1 = (fun i j => raw10773step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10773step1 raw10773step0; decide +kernel
      have hl : raw10773step1Labels = raw10773step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10773step0 raw10773step0Labels permutation80 hz
    mixedMoment B raw10773step1 raw10773step1Labels = mixedMoment B raw10773step2 raw10773step2Labels := by
      have ha : raw10773step2 = (fun i j => raw10773step1 (permutation17 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10773step2 raw10773step1; decide +kernel
      have hl : raw10773step2Labels = raw10773step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10773step1 raw10773step1Labels permutation17 permutation4
    mixedMoment B raw10773step2 raw10773step2Labels = mixedMoment B raw10773step3 raw10773step3Labels := by
      have ha : raw10773step3 = raw10773step2 := by apply Matrix.ext; unfold raw10773step3 raw10773step2; decide +kernel
      have hl : raw10773step2Labels = labelEmbedding7 ∘ raw10773step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10773step2 raw10773step2Labels raw10773step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw10774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -3, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw10774step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10774step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw10774step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10774step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10774step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10774step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10774step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10774 raw10774Labels = mixedMoment B node4276 node4276Labels := by
  calc
    mixedMoment B raw10774 raw10774Labels = mixedMoment B raw10774step0 raw10774step0Labels := by
      have hz : ∀ j, raw10774 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10774step0 = (fun i j => raw10774 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10774step0 raw10774; decide +kernel
      have hl : raw10774step0Labels = raw10774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10774 raw10774Labels permutation434 hz
    mixedMoment B raw10774step0 raw10774step0Labels = mixedMoment B raw10774step1 raw10774step1Labels := by
      have hz : ∀ j, raw10774step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10774step1 = (fun i j => raw10774step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10774step1 raw10774step0; decide +kernel
      have hl : raw10774step1Labels = raw10774step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10774step0 raw10774step0Labels permutation80 hz
    mixedMoment B raw10774step1 raw10774step1Labels = mixedMoment B raw10774step2 raw10774step2Labels := by
      have ha : raw10774step2 = (fun i j => raw10774step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10774step2 raw10774step1; decide +kernel
      have hl : raw10774step2Labels = raw10774step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10774step1 raw10774step1Labels permutation13 permutation5
    mixedMoment B raw10774step2 raw10774step2Labels = mixedMoment B raw10774step3 raw10774step3Labels := by
      have ha : raw10774step3 = -raw10774step2 := by apply Matrix.ext; change ∀ i j, raw10774step3 i j = -(raw10774step2 i j); unfold raw10774step3 raw10774step2; decide +kernel
      have hl : raw10774step3Labels = raw10774step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10774step3 raw10774step3Labels = mixedMoment B raw10774step4 raw10774step4Labels := by
      have ha : raw10774step4 = raw10774step3 := by apply Matrix.ext; unfold raw10774step4 raw10774step3; decide +kernel
      have hl : raw10774step3Labels = labelEmbedding8 ∘ raw10774step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10774step3 raw10774step3Labels raw10774step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4276 node4276Labels := by rfl

def raw10775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw10775step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10775step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10775step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10775step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10775 raw10775Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw10775 raw10775Labels = mixedMoment B raw10775step0 raw10775step0Labels := by
      have hz : ∀ j, raw10775 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10775step0 = (fun i j => raw10775 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10775step0 raw10775; decide +kernel
      have hl : raw10775step0Labels = raw10775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10775 raw10775Labels permutation434 hz
    mixedMoment B raw10775step0 raw10775step0Labels = mixedMoment B raw10775step1 raw10775step1Labels := by
      have ha : raw10775step1 = (fun i j => raw10775step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10775step1 raw10775step0; decide +kernel
      have hl : raw10775step1Labels = raw10775step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10775step0 raw10775step0Labels permutation43 permutation5
    mixedMoment B raw10775step1 raw10775step1Labels = mixedMoment B raw10775step2 raw10775step2Labels := by
      have ha : raw10775step2 = -raw10775step1 := by apply Matrix.ext; change ∀ i j, raw10775step2 i j = -(raw10775step1 i j); unfold raw10775step2 raw10775step1; decide +kernel
      have hl : raw10775step2Labels = raw10775step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10775step2 raw10775step2Labels = mixedMoment B raw10775step3 raw10775step3Labels := by
      have ha : raw10775step3 = raw10775step2 := by apply Matrix.ext; unfold raw10775step3 raw10775step2; decide +kernel
      have hl : raw10775step2Labels = labelEmbedding8 ∘ raw10775step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10775step2 raw10775step2Labels raw10775step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

def raw10776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw10776step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10776step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10776step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10776step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10776step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10776 raw10776Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw10776 raw10776Labels = mixedMoment B raw10776step0 raw10776step0Labels := by
      have hz : ∀ j, raw10776 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10776step0 = (fun i j => raw10776 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10776step0 raw10776; decide +kernel
      have hl : raw10776step0Labels = raw10776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10776 raw10776Labels permutation346 hz
    mixedMoment B raw10776step0 raw10776step0Labels = mixedMoment B raw10776step1 raw10776step1Labels := by
      have ha : raw10776step1 = (fun i j => raw10776step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10776step1 raw10776step0; decide +kernel
      have hl : raw10776step1Labels = raw10776step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10776step0 raw10776step0Labels permutation43 permutation5
    mixedMoment B raw10776step1 raw10776step1Labels = mixedMoment B raw10776step2 raw10776step2Labels := by
      have ha : raw10776step2 = -raw10776step1 := by apply Matrix.ext; change ∀ i j, raw10776step2 i j = -(raw10776step1 i j); unfold raw10776step2 raw10776step1; decide +kernel
      have hl : raw10776step2Labels = raw10776step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10776step2 raw10776step2Labels = mixedMoment B raw10776step3 raw10776step3Labels := by
      have ha : raw10776step3 = raw10776step2 := by apply Matrix.ext; unfold raw10776step3 raw10776step2; decide +kernel
      have hl : raw10776step2Labels = labelEmbedding8 ∘ raw10776step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10776step2 raw10776step2Labels raw10776step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

def raw10777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw10777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw10777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10777step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![2, 0, -2]]
def raw10777step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10777step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![2, 0, -2]]
def raw10777step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10777step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw10777step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10777step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw10777step4Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10777step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw10777step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10777 raw10777Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw10777 raw10777Labels = mixedMoment B raw10777step0 raw10777step0Labels := by
      have hz : ∀ j, raw10777 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10777step0 = (fun i j => raw10777 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10777step0 raw10777; decide +kernel
      have hl : raw10777step0Labels = raw10777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10777 raw10777Labels permutation520 hz
    mixedMoment B raw10777step0 raw10777step0Labels = mixedMoment B raw10777step1 raw10777step1Labels := by
      have hz : ∀ j, raw10777step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10777step1 = (fun i j => raw10777step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10777step1 raw10777step0; decide +kernel
      have hl : raw10777step1Labels = raw10777step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10777step0 raw10777step0Labels permutation104 hz
    mixedMoment B raw10777step1 raw10777step1Labels = mixedMoment B raw10777step2 raw10777step2Labels := by
      have hz : ∀ j, raw10777step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10777step2 = (fun i j => raw10777step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10777step2 raw10777step1; decide +kernel
      have hl : raw10777step2Labels = raw10777step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10777step1 raw10777step1Labels permutation20 hz
    mixedMoment B raw10777step2 raw10777step2Labels = mixedMoment B raw10777step3 raw10777step3Labels := by
      have ha : raw10777step3 = (fun i j => raw10777step2 (permutation3 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10777step3 raw10777step2; decide +kernel
      have hl : raw10777step3Labels = raw10777step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10777step2 raw10777step2Labels permutation3 permutation5
    mixedMoment B raw10777step3 raw10777step3Labels = mixedMoment B raw10777step4 raw10777step4Labels := by
      have ha : raw10777step4 = -raw10777step3 := by apply Matrix.ext; change ∀ i j, raw10777step4 i j = -(raw10777step3 i j); unfold raw10777step4 raw10777step3; decide +kernel
      have hl : raw10777step4Labels = raw10777step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10777step4 raw10777step4Labels = mixedMoment B raw10777step5 raw10777step5Labels := by
      have ha : raw10777step5 = raw10777step4 := by apply Matrix.ext; unfold raw10777step5 raw10777step4; decide +kernel
      have hl : raw10777step4Labels = labelEmbedding8 ∘ raw10777step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10777step4 raw10777step4Labels raw10777step5Labels labelEmbedding8 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

def raw10778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10778step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![1, -1, 0], ![1, 1, -2]]
def raw10778step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10778step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw10778step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10778step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw10778step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10778step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw10778step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10778 raw10778Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw10778 raw10778Labels = mixedMoment B raw10778step0 raw10778step0Labels := by
      have hz : ∀ j, raw10778 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10778step0 = (fun i j => raw10778 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10778step0 raw10778; decide +kernel
      have hl : raw10778step0Labels = raw10778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10778 raw10778Labels permutation434 hz
    mixedMoment B raw10778step0 raw10778step0Labels = mixedMoment B raw10778step1 raw10778step1Labels := by
      have hz : ∀ j, raw10778step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10778step1 = (fun i j => raw10778step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10778step1 raw10778step0; decide +kernel
      have hl : raw10778step1Labels = raw10778step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10778step0 raw10778step0Labels permutation80 hz
    mixedMoment B raw10778step1 raw10778step1Labels = mixedMoment B raw10778step2 raw10778step2Labels := by
      have ha : raw10778step2 = (fun i j => raw10778step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10778step2 raw10778step1; decide +kernel
      have hl : raw10778step2Labels = raw10778step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10778step1 raw10778step1Labels permutation13 permutation5
    mixedMoment B raw10778step2 raw10778step2Labels = mixedMoment B raw10778step3 raw10778step3Labels := by
      have ha : raw10778step3 = -raw10778step2 := by apply Matrix.ext; change ∀ i j, raw10778step3 i j = -(raw10778step2 i j); unfold raw10778step3 raw10778step2; decide +kernel
      have hl : raw10778step3Labels = raw10778step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10778step3 raw10778step3Labels = mixedMoment B raw10778step4 raw10778step4Labels := by
      have ha : raw10778step4 = raw10778step3 := by apply Matrix.ext; unfold raw10778step4 raw10778step3; decide +kernel
      have hl : raw10778step3Labels = labelEmbedding8 ∘ raw10778step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10778step3 raw10778step3Labels raw10778step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

def raw10779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10779step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10779 raw10779Labels = mixedMoment B node4275 node4275Labels := by
  calc
    mixedMoment B raw10779 raw10779Labels = mixedMoment B raw10779step0 raw10779step0Labels := by
      have hz : ∀ j, raw10779 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10779step0 = (fun i j => raw10779 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10779step0 raw10779; decide +kernel
      have hl : raw10779step0Labels = raw10779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10779 raw10779Labels permutation434 hz
    mixedMoment B raw10779step0 raw10779step0Labels = mixedMoment B raw10779step1 raw10779step1Labels := by
      have ha : raw10779step1 = (fun i j => raw10779step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10779step1 raw10779step0; decide +kernel
      have hl : raw10779step1Labels = raw10779step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10779step0 raw10779step0Labels permutation32 permutation3
    mixedMoment B raw10779step1 raw10779step1Labels = mixedMoment B raw10779step2 raw10779step2Labels := by
      have ha : raw10779step2 = raw10779step1 := by apply Matrix.ext; unfold raw10779step2 raw10779step1; decide +kernel
      have hl : raw10779step1Labels = labelEmbedding6 ∘ raw10779step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10779step1 raw10779step1Labels raw10779step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4275 node4275Labels := by rfl

def raw10780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10780step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10780step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10780step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10780 raw10780Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw10780 raw10780Labels = mixedMoment B raw10780step0 raw10780step0Labels := by
      have hz : ∀ j, raw10780 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10780step0 = (fun i j => raw10780 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10780step0 raw10780; decide +kernel
      have hl : raw10780step0Labels = raw10780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10780 raw10780Labels permutation434 hz
    mixedMoment B raw10780step0 raw10780step0Labels = mixedMoment B raw10780step1 raw10780step1Labels := by
      have ha : raw10780step1 = (fun i j => raw10780step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10780step1 raw10780step0; decide +kernel
      have hl : raw10780step1Labels = raw10780step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10780step0 raw10780step0Labels permutation32 permutation3
    mixedMoment B raw10780step1 raw10780step1Labels = mixedMoment B raw10780step2 raw10780step2Labels := by
      have ha : raw10780step2 = raw10780step1 := by apply Matrix.ext; unfold raw10780step2 raw10780step1; decide +kernel
      have hl : raw10780step1Labels = labelEmbedding6 ∘ raw10780step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10780step1 raw10780step1Labels raw10780step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

def raw10781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10781step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10781step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10781step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10781 raw10781Labels = mixedMoment B node4746 node4746Labels := by
  calc
    mixedMoment B raw10781 raw10781Labels = mixedMoment B raw10781step0 raw10781step0Labels := by
      have ha : raw10781step0 = (fun i j => raw10781 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10781step0 raw10781; decide +kernel
      have hl : raw10781step0Labels = raw10781Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10781 raw10781Labels permutation200 permutation3
    mixedMoment B raw10781step0 raw10781step0Labels = mixedMoment B raw10781step1 raw10781step1Labels := by
      have ha : raw10781step1 = raw10781step0 := by apply Matrix.ext; unfold raw10781step1 raw10781step0; decide +kernel
      have hl : raw10781step0Labels = labelEmbedding6 ∘ raw10781step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10781step0 raw10781step0Labels raw10781step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4746 node4746Labels := by rfl

def raw10782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw10782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw10782step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw10782step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10782step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10782step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10782step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10782step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10782 raw10782Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw10782 raw10782Labels = mixedMoment B raw10782step0 raw10782step0Labels := by
      have hz : ∀ j, raw10782 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10782step0 = (fun i j => raw10782 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10782step0 raw10782; decide +kernel
      have hl : raw10782step0Labels = raw10782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10782 raw10782Labels permutation520 hz
    mixedMoment B raw10782step0 raw10782step0Labels = mixedMoment B raw10782step1 raw10782step1Labels := by
      have hz : ∀ j, raw10782step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10782step1 = (fun i j => raw10782step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10782step1 raw10782step0; decide +kernel
      have hl : raw10782step1Labels = raw10782step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10782step0 raw10782step0Labels permutation104 hz
    mixedMoment B raw10782step1 raw10782step1Labels = mixedMoment B raw10782step2 raw10782step2Labels := by
      have ha : raw10782step2 = (fun i j => raw10782step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10782step2 raw10782step1; decide +kernel
      have hl : raw10782step2Labels = raw10782step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10782step1 raw10782step1Labels permutation8 permutation3
    mixedMoment B raw10782step2 raw10782step2Labels = mixedMoment B raw10782step3 raw10782step3Labels := by
      have ha : raw10782step3 = raw10782step2 := by apply Matrix.ext; unfold raw10782step3 raw10782step2; decide +kernel
      have hl : raw10782step2Labels = labelEmbedding6 ∘ raw10782step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10782step2 raw10782step2Labels raw10782step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

def raw10783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10783step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10783step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10783step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10783step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10783 raw10783Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw10783 raw10783Labels = mixedMoment B raw10783step0 raw10783step0Labels := by
      have hz : ∀ j, raw10783 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10783step0 = (fun i j => raw10783 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10783step0 raw10783; decide +kernel
      have hl : raw10783step0Labels = raw10783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10783 raw10783Labels permutation434 hz
    mixedMoment B raw10783step0 raw10783step0Labels = mixedMoment B raw10783step1 raw10783step1Labels := by
      have ha : raw10783step1 = (fun i j => raw10783step0 (permutation53 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10783step1 raw10783step0; decide +kernel
      have hl : raw10783step1Labels = raw10783step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10783step0 raw10783step0Labels permutation53 permutation5
    mixedMoment B raw10783step1 raw10783step1Labels = mixedMoment B raw10783step2 raw10783step2Labels := by
      have ha : raw10783step2 = -raw10783step1 := by apply Matrix.ext; change ∀ i j, raw10783step2 i j = -(raw10783step1 i j); unfold raw10783step2 raw10783step1; decide +kernel
      have hl : raw10783step2Labels = raw10783step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10783step2 raw10783step2Labels = mixedMoment B raw10783step3 raw10783step3Labels := by
      have ha : raw10783step3 = raw10783step2 := by apply Matrix.ext; unfold raw10783step3 raw10783step2; decide +kernel
      have hl : raw10783step2Labels = labelEmbedding8 ∘ raw10783step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10783step2 raw10783step2Labels raw10783step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

def raw10784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10784step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10784step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10784 raw10784Labels = mixedMoment B node4275 node4275Labels := by
  calc
    mixedMoment B raw10784 raw10784Labels = mixedMoment B raw10784step0 raw10784step0Labels := by
      have hz : ∀ j, raw10784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10784step0 = (fun i j => raw10784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10784step0 raw10784; decide +kernel
      have hl : raw10784step0Labels = raw10784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10784 raw10784Labels permutation346 hz
    mixedMoment B raw10784step0 raw10784step0Labels = mixedMoment B raw10784step1 raw10784step1Labels := by
      have ha : raw10784step1 = (fun i j => raw10784step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10784step1 raw10784step0; decide +kernel
      have hl : raw10784step1Labels = raw10784step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10784step0 raw10784step0Labels permutation32 permutation3
    mixedMoment B raw10784step1 raw10784step1Labels = mixedMoment B raw10784step2 raw10784step2Labels := by
      have ha : raw10784step2 = raw10784step1 := by apply Matrix.ext; unfold raw10784step2 raw10784step1; decide +kernel
      have hl : raw10784step1Labels = labelEmbedding6 ∘ raw10784step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10784step1 raw10784step1Labels raw10784step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4275 node4275Labels := by rfl

def raw10785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10785step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10785step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10785 raw10785Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw10785 raw10785Labels = mixedMoment B raw10785step0 raw10785step0Labels := by
      have hz : ∀ j, raw10785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10785step0 = (fun i j => raw10785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10785step0 raw10785; decide +kernel
      have hl : raw10785step0Labels = raw10785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10785 raw10785Labels permutation346 hz
    mixedMoment B raw10785step0 raw10785step0Labels = mixedMoment B raw10785step1 raw10785step1Labels := by
      have ha : raw10785step1 = (fun i j => raw10785step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10785step1 raw10785step0; decide +kernel
      have hl : raw10785step1Labels = raw10785step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10785step0 raw10785step0Labels permutation32 permutation3
    mixedMoment B raw10785step1 raw10785step1Labels = mixedMoment B raw10785step2 raw10785step2Labels := by
      have ha : raw10785step2 = raw10785step1 := by apply Matrix.ext; unfold raw10785step2 raw10785step1; decide +kernel
      have hl : raw10785step1Labels = labelEmbedding6 ∘ raw10785step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10785step1 raw10785step1Labels raw10785step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

def raw10786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10786step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10786step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10786 raw10786Labels = mixedMoment B node4746 node4746Labels := by
  calc
    mixedMoment B raw10786 raw10786Labels = mixedMoment B raw10786step0 raw10786step0Labels := by
      have ha : raw10786step0 = (fun i j => raw10786 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10786step0 raw10786; decide +kernel
      have hl : raw10786step0Labels = raw10786Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10786 raw10786Labels permutation176 permutation3
    mixedMoment B raw10786step0 raw10786step0Labels = mixedMoment B raw10786step1 raw10786step1Labels := by
      have ha : raw10786step1 = raw10786step0 := by apply Matrix.ext; unfold raw10786step1 raw10786step0; decide +kernel
      have hl : raw10786step0Labels = labelEmbedding6 ∘ raw10786step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10786step0 raw10786step0Labels raw10786step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4746 node4746Labels := by rfl

def raw10787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw10787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw10787step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10787step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10787step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10787step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10787step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10787 raw10787Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw10787 raw10787Labels = mixedMoment B raw10787step0 raw10787step0Labels := by
      have hz : ∀ j, raw10787 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10787step0 = (fun i j => raw10787 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10787step0 raw10787; decide +kernel
      have hl : raw10787step0Labels = raw10787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10787 raw10787Labels permutation520 hz
    mixedMoment B raw10787step0 raw10787step0Labels = mixedMoment B raw10787step1 raw10787step1Labels := by
      have hz : ∀ j, raw10787step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10787step1 = (fun i j => raw10787step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10787step1 raw10787step0; decide +kernel
      have hl : raw10787step1Labels = raw10787step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10787step0 raw10787step0Labels permutation80 hz
    mixedMoment B raw10787step1 raw10787step1Labels = mixedMoment B raw10787step2 raw10787step2Labels := by
      have ha : raw10787step2 = (fun i j => raw10787step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10787step2 raw10787step1; decide +kernel
      have hl : raw10787step2Labels = raw10787step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10787step1 raw10787step1Labels permutation8 permutation3
    mixedMoment B raw10787step2 raw10787step2Labels = mixedMoment B raw10787step3 raw10787step3Labels := by
      have ha : raw10787step3 = raw10787step2 := by apply Matrix.ext; unfold raw10787step3 raw10787step2; decide +kernel
      have hl : raw10787step2Labels = labelEmbedding6 ∘ raw10787step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10787step2 raw10787step2Labels raw10787step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

def raw10788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10788step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10788step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10788step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10788step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10788 raw10788Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw10788 raw10788Labels = mixedMoment B raw10788step0 raw10788step0Labels := by
      have hz : ∀ j, raw10788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10788step0 = (fun i j => raw10788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10788step0 raw10788; decide +kernel
      have hl : raw10788step0Labels = raw10788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10788 raw10788Labels permutation346 hz
    mixedMoment B raw10788step0 raw10788step0Labels = mixedMoment B raw10788step1 raw10788step1Labels := by
      have ha : raw10788step1 = (fun i j => raw10788step0 (permutation53 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10788step1 raw10788step0; decide +kernel
      have hl : raw10788step1Labels = raw10788step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10788step0 raw10788step0Labels permutation53 permutation5
    mixedMoment B raw10788step1 raw10788step1Labels = mixedMoment B raw10788step2 raw10788step2Labels := by
      have ha : raw10788step2 = -raw10788step1 := by apply Matrix.ext; change ∀ i j, raw10788step2 i j = -(raw10788step1 i j); unfold raw10788step2 raw10788step1; decide +kernel
      have hl : raw10788step2Labels = raw10788step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10788step2 raw10788step2Labels = mixedMoment B raw10788step3 raw10788step3Labels := by
      have ha : raw10788step3 = raw10788step2 := by apply Matrix.ext; unfold raw10788step3 raw10788step2; decide +kernel
      have hl : raw10788step2Labels = labelEmbedding8 ∘ raw10788step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10788step2 raw10788step2Labels raw10788step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

def raw10789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10789step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw10789step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10789step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw10789step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10789step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw10789step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10789 raw10789Labels = mixedMoment B node4278 node4278Labels := by
  calc
    mixedMoment B raw10789 raw10789Labels = mixedMoment B raw10789step0 raw10789step0Labels := by
      have hz : ∀ j, raw10789 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10789step0 = (fun i j => raw10789 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10789step0 raw10789; decide +kernel
      have hl : raw10789step0Labels = raw10789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10789 raw10789Labels permutation434 hz
    mixedMoment B raw10789step0 raw10789step0Labels = mixedMoment B raw10789step1 raw10789step1Labels := by
      have hz : ∀ j, raw10789step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10789step1 = (fun i j => raw10789step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10789step1 raw10789step0; decide +kernel
      have hl : raw10789step1Labels = raw10789step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10789step0 raw10789step0Labels permutation80 hz
    mixedMoment B raw10789step1 raw10789step1Labels = mixedMoment B raw10789step2 raw10789step2Labels := by
      have ha : raw10789step2 = (fun i j => raw10789step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10789step2 raw10789step1; decide +kernel
      have hl : raw10789step2Labels = raw10789step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10789step1 raw10789step1Labels permutation9 permutation3
    mixedMoment B raw10789step2 raw10789step2Labels = mixedMoment B raw10789step3 raw10789step3Labels := by
      have ha : raw10789step3 = raw10789step2 := by apply Matrix.ext; unfold raw10789step3 raw10789step2; decide +kernel
      have hl : raw10789step2Labels = labelEmbedding6 ∘ raw10789step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10789step2 raw10789step2Labels raw10789step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4278 node4278Labels := by rfl

def raw10790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10790step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw10790step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10790step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10790step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10790step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10790step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10790 raw10790Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw10790 raw10790Labels = mixedMoment B raw10790step0 raw10790step0Labels := by
      have hz : ∀ j, raw10790 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10790step0 = (fun i j => raw10790 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10790step0 raw10790; decide +kernel
      have hl : raw10790step0Labels = raw10790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10790 raw10790Labels permutation434 hz
    mixedMoment B raw10790step0 raw10790step0Labels = mixedMoment B raw10790step1 raw10790step1Labels := by
      have hz : ∀ j, raw10790step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10790step1 = (fun i j => raw10790step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10790step1 raw10790step0; decide +kernel
      have hl : raw10790step1Labels = raw10790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10790step0 raw10790step0Labels permutation80 hz
    mixedMoment B raw10790step1 raw10790step1Labels = mixedMoment B raw10790step2 raw10790step2Labels := by
      have ha : raw10790step2 = (fun i j => raw10790step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10790step2 raw10790step1; decide +kernel
      have hl : raw10790step2Labels = raw10790step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10790step1 raw10790step1Labels permutation9 permutation3
    mixedMoment B raw10790step2 raw10790step2Labels = mixedMoment B raw10790step3 raw10790step3Labels := by
      have ha : raw10790step3 = raw10790step2 := by apply Matrix.ext; unfold raw10790step3 raw10790step2; decide +kernel
      have hl : raw10790step2Labels = labelEmbedding6 ∘ raw10790step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10790step2 raw10790step2Labels raw10790step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

def raw10791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw10791step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw10791step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10791 raw10791Labels = mixedMoment B node4749 node4749Labels := by
  calc
    mixedMoment B raw10791 raw10791Labels = mixedMoment B raw10791step0 raw10791step0Labels := by
      have hz : ∀ j, raw10791 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10791step0 = (fun i j => raw10791 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10791step0 raw10791; decide +kernel
      have hl : raw10791step0Labels = raw10791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10791 raw10791Labels permutation434 hz
    mixedMoment B raw10791step0 raw10791step0Labels = mixedMoment B raw10791step1 raw10791step1Labels := by
      have ha : raw10791step1 = (fun i j => raw10791step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10791step1 raw10791step0; decide +kernel
      have hl : raw10791step1Labels = raw10791step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10791step0 raw10791step0Labels permutation39 permutation3
    mixedMoment B raw10791step1 raw10791step1Labels = mixedMoment B raw10791step2 raw10791step2Labels := by
      have ha : raw10791step2 = raw10791step1 := by apply Matrix.ext; unfold raw10791step2 raw10791step1; decide +kernel
      have hl : raw10791step1Labels = labelEmbedding6 ∘ raw10791step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10791step1 raw10791step1Labels raw10791step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4749 node4749Labels := by rfl

def raw10792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw10792step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw10792step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10792 raw10792Labels = mixedMoment B node4749 node4749Labels := by
  calc
    mixedMoment B raw10792 raw10792Labels = mixedMoment B raw10792step0 raw10792step0Labels := by
      have hz : ∀ j, raw10792 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10792step0 = (fun i j => raw10792 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10792step0 raw10792; decide +kernel
      have hl : raw10792step0Labels = raw10792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10792 raw10792Labels permutation346 hz
    mixedMoment B raw10792step0 raw10792step0Labels = mixedMoment B raw10792step1 raw10792step1Labels := by
      have ha : raw10792step1 = (fun i j => raw10792step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10792step1 raw10792step0; decide +kernel
      have hl : raw10792step1Labels = raw10792step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10792step0 raw10792step0Labels permutation39 permutation3
    mixedMoment B raw10792step1 raw10792step1Labels = mixedMoment B raw10792step2 raw10792step2Labels := by
      have ha : raw10792step2 = raw10792step1 := by apply Matrix.ext; unfold raw10792step2 raw10792step1; decide +kernel
      have hl : raw10792step1Labels = labelEmbedding6 ∘ raw10792step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10792step1 raw10792step1Labels raw10792step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4749 node4749Labels := by rfl

def raw10793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw10793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw10793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10793step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![2, -2, 0], ![1, 1, -2]]
def raw10793step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10793step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw10793step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10793step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10793step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10793step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10793step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10793 raw10793Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw10793 raw10793Labels = mixedMoment B raw10793step0 raw10793step0Labels := by
      have hz : ∀ j, raw10793 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10793step0 = (fun i j => raw10793 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10793step0 raw10793; decide +kernel
      have hl : raw10793step0Labels = raw10793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10793 raw10793Labels permutation434 hz
    mixedMoment B raw10793step0 raw10793step0Labels = mixedMoment B raw10793step1 raw10793step1Labels := by
      have hz : ∀ j, raw10793step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10793step1 = (fun i j => raw10793step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10793step1 raw10793step0; decide +kernel
      have hl : raw10793step1Labels = raw10793step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10793step0 raw10793step0Labels permutation80 hz
    mixedMoment B raw10793step1 raw10793step1Labels = mixedMoment B raw10793step2 raw10793step2Labels := by
      have ha : raw10793step2 = (fun i j => raw10793step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10793step2 raw10793step1; decide +kernel
      have hl : raw10793step2Labels = raw10793step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10793step1 raw10793step1Labels permutation12 permutation5
    mixedMoment B raw10793step2 raw10793step2Labels = mixedMoment B raw10793step3 raw10793step3Labels := by
      have ha : raw10793step3 = -raw10793step2 := by apply Matrix.ext; change ∀ i j, raw10793step3 i j = -(raw10793step2 i j); unfold raw10793step3 raw10793step2; decide +kernel
      have hl : raw10793step3Labels = raw10793step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10793step3 raw10793step3Labels = mixedMoment B raw10793step4 raw10793step4Labels := by
      have ha : raw10793step4 = raw10793step3 := by apply Matrix.ext; unfold raw10793step4 raw10793step3; decide +kernel
      have hl : raw10793step3Labels = labelEmbedding8 ∘ raw10793step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10793step3 raw10793step3Labels raw10793step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

def raw10794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw10794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw10794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw10794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10794step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10794step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10794step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10794step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10794 raw10794Labels = mixedMoment B node4276 node4276Labels := by
  calc
    mixedMoment B raw10794 raw10794Labels = mixedMoment B raw10794step0 raw10794step0Labels := by
      have hz : ∀ j, raw10794 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10794step0 = (fun i j => raw10794 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10794step0 raw10794; decide +kernel
      have hl : raw10794step0Labels = raw10794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10794 raw10794Labels permutation434 hz
    mixedMoment B raw10794step0 raw10794step0Labels = mixedMoment B raw10794step1 raw10794step1Labels := by
      have hz : ∀ j, raw10794step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10794step1 = (fun i j => raw10794step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10794step1 raw10794step0; decide +kernel
      have hl : raw10794step1Labels = raw10794step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10794step0 raw10794step0Labels permutation80 hz
    mixedMoment B raw10794step1 raw10794step1Labels = mixedMoment B raw10794step2 raw10794step2Labels := by
      have ha : raw10794step2 = (fun i j => raw10794step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10794step2 raw10794step1; decide +kernel
      have hl : raw10794step2Labels = raw10794step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10794step1 raw10794step1Labels permutation8 permutation3
    mixedMoment B raw10794step2 raw10794step2Labels = mixedMoment B raw10794step3 raw10794step3Labels := by
      have ha : raw10794step3 = raw10794step2 := by apply Matrix.ext; unfold raw10794step3 raw10794step2; decide +kernel
      have hl : raw10794step2Labels = labelEmbedding6 ∘ raw10794step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10794step2 raw10794step2Labels raw10794step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4276 node4276Labels := by rfl

def raw10795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw10795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw10795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw10795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10795step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw10795step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10795step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw10795step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10795 raw10795Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw10795 raw10795Labels = mixedMoment B raw10795step0 raw10795step0Labels := by
      have hz : ∀ j, raw10795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10795step0 = (fun i j => raw10795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10795step0 raw10795; decide +kernel
      have hl : raw10795step0Labels = raw10795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10795 raw10795Labels permutation434 hz
    mixedMoment B raw10795step0 raw10795step0Labels = mixedMoment B raw10795step1 raw10795step1Labels := by
      have hz : ∀ j, raw10795step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10795step1 = (fun i j => raw10795step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10795step1 raw10795step0; decide +kernel
      have hl : raw10795step1Labels = raw10795step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10795step0 raw10795step0Labels permutation80 hz
    mixedMoment B raw10795step1 raw10795step1Labels = mixedMoment B raw10795step2 raw10795step2Labels := by
      have ha : raw10795step2 = (fun i j => raw10795step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10795step2 raw10795step1; decide +kernel
      have hl : raw10795step2Labels = raw10795step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10795step1 raw10795step1Labels permutation8 permutation3
    mixedMoment B raw10795step2 raw10795step2Labels = mixedMoment B raw10795step3 raw10795step3Labels := by
      have ha : raw10795step3 = raw10795step2 := by apply Matrix.ext; unfold raw10795step3 raw10795step2; decide +kernel
      have hl : raw10795step2Labels = labelEmbedding6 ∘ raw10795step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10795step2 raw10795step2Labels raw10795step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

def raw10796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw10796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw10796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10796step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10796step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10796step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10796 raw10796Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw10796 raw10796Labels = mixedMoment B raw10796step0 raw10796step0Labels := by
      have hz : ∀ j, raw10796 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10796step0 = (fun i j => raw10796 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10796step0 raw10796; decide +kernel
      have hl : raw10796step0Labels = raw10796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10796 raw10796Labels permutation434 hz
    mixedMoment B raw10796step0 raw10796step0Labels = mixedMoment B raw10796step1 raw10796step1Labels := by
      have ha : raw10796step1 = (fun i j => raw10796step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10796step1 raw10796step0; decide +kernel
      have hl : raw10796step1Labels = raw10796step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10796step0 raw10796step0Labels permutation38 permutation3
    mixedMoment B raw10796step1 raw10796step1Labels = mixedMoment B raw10796step2 raw10796step2Labels := by
      have ha : raw10796step2 = raw10796step1 := by apply Matrix.ext; unfold raw10796step2 raw10796step1; decide +kernel
      have hl : raw10796step1Labels = labelEmbedding6 ∘ raw10796step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10796step1 raw10796step1Labels raw10796step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

def raw10797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw10797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw10797step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10797step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw10797step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10797 raw10797Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw10797 raw10797Labels = mixedMoment B raw10797step0 raw10797step0Labels := by
      have hz : ∀ j, raw10797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10797step0 = (fun i j => raw10797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10797step0 raw10797; decide +kernel
      have hl : raw10797step0Labels = raw10797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10797 raw10797Labels permutation346 hz
    mixedMoment B raw10797step0 raw10797step0Labels = mixedMoment B raw10797step1 raw10797step1Labels := by
      have ha : raw10797step1 = (fun i j => raw10797step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10797step1 raw10797step0; decide +kernel
      have hl : raw10797step1Labels = raw10797step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10797step0 raw10797step0Labels permutation38 permutation3
    mixedMoment B raw10797step1 raw10797step1Labels = mixedMoment B raw10797step2 raw10797step2Labels := by
      have ha : raw10797step2 = raw10797step1 := by apply Matrix.ext; unfold raw10797step2 raw10797step1; decide +kernel
      have hl : raw10797step1Labels = labelEmbedding6 ∘ raw10797step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10797step1 raw10797step1Labels raw10797step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

def raw10798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw10798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw10798step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10798step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![3, -1, -2]]
def raw10798step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10798step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![3, -1, -2]]
def raw10798step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10798step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw10798step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10798step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw10798step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10798 raw10798Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw10798 raw10798Labels = mixedMoment B raw10798step0 raw10798step0Labels := by
      have hz : ∀ j, raw10798 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10798step0 = (fun i j => raw10798 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10798step0 raw10798; decide +kernel
      have hl : raw10798step0Labels = raw10798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10798 raw10798Labels permutation520 hz
    mixedMoment B raw10798step0 raw10798step0Labels = mixedMoment B raw10798step1 raw10798step1Labels := by
      have hz : ∀ j, raw10798step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10798step1 = (fun i j => raw10798step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10798step1 raw10798step0; decide +kernel
      have hl : raw10798step1Labels = raw10798step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10798step0 raw10798step0Labels permutation104 hz
    mixedMoment B raw10798step1 raw10798step1Labels = mixedMoment B raw10798step2 raw10798step2Labels := by
      have hz : ∀ j, raw10798step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10798step2 = (fun i j => raw10798step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10798step2 raw10798step1; decide +kernel
      have hl : raw10798step2Labels = raw10798step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10798step1 raw10798step1Labels permutation20 hz
    mixedMoment B raw10798step2 raw10798step2Labels = mixedMoment B raw10798step3 raw10798step3Labels := by
      have ha : raw10798step3 = (fun i j => raw10798step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10798step3 raw10798step2; decide +kernel
      have hl : raw10798step3Labels = raw10798step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10798step2 raw10798step2Labels permutation2 permutation3
    mixedMoment B raw10798step3 raw10798step3Labels = mixedMoment B raw10798step4 raw10798step4Labels := by
      have ha : raw10798step4 = raw10798step3 := by apply Matrix.ext; unfold raw10798step4 raw10798step3; decide +kernel
      have hl : raw10798step3Labels = labelEmbedding6 ∘ raw10798step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10798step3 raw10798step3Labels raw10798step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

def raw10799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10799step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10799step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw10799step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10799step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10799step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10799step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10799step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10799 raw10799Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw10799 raw10799Labels = mixedMoment B raw10799step0 raw10799step0Labels := by
      have hz : ∀ j, raw10799 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10799step0 = (fun i j => raw10799 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10799step0 raw10799; decide +kernel
      have hl : raw10799step0Labels = raw10799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10799 raw10799Labels permutation434 hz
    mixedMoment B raw10799step0 raw10799step0Labels = mixedMoment B raw10799step1 raw10799step1Labels := by
      have hz : ∀ j, raw10799step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10799step1 = (fun i j => raw10799step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10799step1 raw10799step0; decide +kernel
      have hl : raw10799step1Labels = raw10799step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10799step0 raw10799step0Labels permutation80 hz
    mixedMoment B raw10799step1 raw10799step1Labels = mixedMoment B raw10799step2 raw10799step2Labels := by
      have ha : raw10799step2 = (fun i j => raw10799step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10799step2 raw10799step1; decide +kernel
      have hl : raw10799step2Labels = raw10799step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10799step1 raw10799step1Labels permutation11 permutation7
    mixedMoment B raw10799step2 raw10799step2Labels = mixedMoment B raw10799step3 raw10799step3Labels := by
      have ha : raw10799step3 = -raw10799step2 := by apply Matrix.ext; change ∀ i j, raw10799step3 i j = -(raw10799step2 i j); unfold raw10799step3 raw10799step2; decide +kernel
      have hl : raw10799step3Labels = raw10799step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10799step3 raw10799step3Labels = mixedMoment B raw10799step4 raw10799step4Labels := by
      have ha : raw10799step4 = raw10799step3 := by apply Matrix.ext; unfold raw10799step4 raw10799step3; decide +kernel
      have hl : raw10799step3Labels = labelEmbedding10 ∘ raw10799step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10799step3 raw10799step3Labels raw10799step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw10800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10800step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10800step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10800step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10800step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10800 raw10800Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw10800 raw10800Labels = mixedMoment B raw10800step0 raw10800step0Labels := by
      have hz : ∀ j, raw10800 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10800step0 = (fun i j => raw10800 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10800step0 raw10800; decide +kernel
      have hl : raw10800step0Labels = raw10800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10800 raw10800Labels permutation434 hz
    mixedMoment B raw10800step0 raw10800step0Labels = mixedMoment B raw10800step1 raw10800step1Labels := by
      have ha : raw10800step1 = (fun i j => raw10800step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10800step1 raw10800step0; decide +kernel
      have hl : raw10800step1Labels = raw10800step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10800step0 raw10800step0Labels permutation41 permutation7
    mixedMoment B raw10800step1 raw10800step1Labels = mixedMoment B raw10800step2 raw10800step2Labels := by
      have ha : raw10800step2 = -raw10800step1 := by apply Matrix.ext; change ∀ i j, raw10800step2 i j = -(raw10800step1 i j); unfold raw10800step2 raw10800step1; decide +kernel
      have hl : raw10800step2Labels = raw10800step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10800step2 raw10800step2Labels = mixedMoment B raw10800step3 raw10800step3Labels := by
      have ha : raw10800step3 = raw10800step2 := by apply Matrix.ext; unfold raw10800step3 raw10800step2; decide +kernel
      have hl : raw10800step2Labels = labelEmbedding10 ∘ raw10800step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10800step2 raw10800step2Labels raw10800step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw10801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10801step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10801step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10801step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10801step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10801step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10801 raw10801Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw10801 raw10801Labels = mixedMoment B raw10801step0 raw10801step0Labels := by
      have hz : ∀ j, raw10801 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10801step0 = (fun i j => raw10801 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10801step0 raw10801; decide +kernel
      have hl : raw10801step0Labels = raw10801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10801 raw10801Labels permutation346 hz
    mixedMoment B raw10801step0 raw10801step0Labels = mixedMoment B raw10801step1 raw10801step1Labels := by
      have ha : raw10801step1 = (fun i j => raw10801step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10801step1 raw10801step0; decide +kernel
      have hl : raw10801step1Labels = raw10801step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10801step0 raw10801step0Labels permutation41 permutation7
    mixedMoment B raw10801step1 raw10801step1Labels = mixedMoment B raw10801step2 raw10801step2Labels := by
      have ha : raw10801step2 = -raw10801step1 := by apply Matrix.ext; change ∀ i j, raw10801step2 i j = -(raw10801step1 i j); unfold raw10801step2 raw10801step1; decide +kernel
      have hl : raw10801step2Labels = raw10801step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10801step2 raw10801step2Labels = mixedMoment B raw10801step3 raw10801step3Labels := by
      have ha : raw10801step3 = raw10801step2 := by apply Matrix.ext; unfold raw10801step3 raw10801step2; decide +kernel
      have hl : raw10801step2Labels = labelEmbedding10 ∘ raw10801step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10801step2 raw10801step2Labels raw10801step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw10802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10802step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw10802step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10802step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw10802step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10802step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw10802step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10802step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10802step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10802step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10802step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10802 raw10802Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw10802 raw10802Labels = mixedMoment B raw10802step0 raw10802step0Labels := by
      have hz : ∀ j, raw10802 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10802step0 = (fun i j => raw10802 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10802step0 raw10802; decide +kernel
      have hl : raw10802step0Labels = raw10802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10802 raw10802Labels permutation520 hz
    mixedMoment B raw10802step0 raw10802step0Labels = mixedMoment B raw10802step1 raw10802step1Labels := by
      have hz : ∀ j, raw10802step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10802step1 = (fun i j => raw10802step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10802step1 raw10802step0; decide +kernel
      have hl : raw10802step1Labels = raw10802step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10802step0 raw10802step0Labels permutation104 hz
    mixedMoment B raw10802step1 raw10802step1Labels = mixedMoment B raw10802step2 raw10802step2Labels := by
      have hz : ∀ j, raw10802step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10802step2 = (fun i j => raw10802step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10802step2 raw10802step1; decide +kernel
      have hl : raw10802step2Labels = raw10802step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10802step1 raw10802step1Labels permutation20 hz
    mixedMoment B raw10802step2 raw10802step2Labels = mixedMoment B raw10802step3 raw10802step3Labels := by
      have ha : raw10802step3 = (fun i j => raw10802step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10802step3 raw10802step2; decide +kernel
      have hl : raw10802step3Labels = raw10802step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10802step2 raw10802step2Labels permutation3 permutation7
    mixedMoment B raw10802step3 raw10802step3Labels = mixedMoment B raw10802step4 raw10802step4Labels := by
      have ha : raw10802step4 = -raw10802step3 := by apply Matrix.ext; change ∀ i j, raw10802step4 i j = -(raw10802step3 i j); unfold raw10802step4 raw10802step3; decide +kernel
      have hl : raw10802step4Labels = raw10802step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10802step4 raw10802step4Labels = mixedMoment B raw10802step5 raw10802step5Labels := by
      have ha : raw10802step5 = raw10802step4 := by apply Matrix.ext; unfold raw10802step5 raw10802step4; decide +kernel
      have hl : raw10802step4Labels = labelEmbedding10 ∘ raw10802step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10802step4 raw10802step4Labels raw10802step5Labels labelEmbedding10 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw10803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw10803step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10803step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10803step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10803step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10803step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10803step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10803step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10803 raw10803Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw10803 raw10803Labels = mixedMoment B raw10803step0 raw10803step0Labels := by
      have hz : ∀ j, raw10803 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10803step0 = (fun i j => raw10803 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10803step0 raw10803; decide +kernel
      have hl : raw10803step0Labels = raw10803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10803 raw10803Labels permutation434 hz
    mixedMoment B raw10803step0 raw10803step0Labels = mixedMoment B raw10803step1 raw10803step1Labels := by
      have hz : ∀ j, raw10803step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10803step1 = (fun i j => raw10803step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10803step1 raw10803step0; decide +kernel
      have hl : raw10803step1Labels = raw10803step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10803step0 raw10803step0Labels permutation80 hz
    mixedMoment B raw10803step1 raw10803step1Labels = mixedMoment B raw10803step2 raw10803step2Labels := by
      have ha : raw10803step2 = (fun i j => raw10803step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10803step2 raw10803step1; decide +kernel
      have hl : raw10803step2Labels = raw10803step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10803step1 raw10803step1Labels permutation11 permutation7
    mixedMoment B raw10803step2 raw10803step2Labels = mixedMoment B raw10803step3 raw10803step3Labels := by
      have ha : raw10803step3 = -raw10803step2 := by apply Matrix.ext; change ∀ i j, raw10803step3 i j = -(raw10803step2 i j); unfold raw10803step3 raw10803step2; decide +kernel
      have hl : raw10803step3Labels = raw10803step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10803step3 raw10803step3Labels = mixedMoment B raw10803step4 raw10803step4Labels := by
      have ha : raw10803step4 = raw10803step3 := by apply Matrix.ext; unfold raw10803step4 raw10803step3; decide +kernel
      have hl : raw10803step3Labels = labelEmbedding10 ∘ raw10803step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10803step3 raw10803step3Labels raw10803step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw10804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10804step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10804step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10804step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10804step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10804step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10804 raw10804Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw10804 raw10804Labels = mixedMoment B raw10804step0 raw10804step0Labels := by
      have hz : ∀ j, raw10804 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10804step0 = (fun i j => raw10804 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10804step0 raw10804; decide +kernel
      have hl : raw10804step0Labels = raw10804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10804 raw10804Labels permutation434 hz
    mixedMoment B raw10804step0 raw10804step0Labels = mixedMoment B raw10804step1 raw10804step1Labels := by
      have hz : ∀ j, raw10804step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10804step1 = (fun i j => raw10804step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10804step1 raw10804step0; decide +kernel
      have hl : raw10804step1Labels = raw10804step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10804step0 raw10804step0Labels permutation80 hz
    mixedMoment B raw10804step1 raw10804step1Labels = mixedMoment B raw10804step2 raw10804step2Labels := by
      have ha : raw10804step2 = (fun i j => raw10804step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10804step2 raw10804step1; decide +kernel
      have hl : raw10804step2Labels = raw10804step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10804step1 raw10804step1Labels permutation10 permutation2
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw10805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10805step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10805step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10805 raw10805Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw10805 raw10805Labels = mixedMoment B raw10805step0 raw10805step0Labels := by
      have hz : ∀ j, raw10805 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10805step0 = (fun i j => raw10805 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10805step0 raw10805; decide +kernel
      have hl : raw10805step0Labels = raw10805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10805 raw10805Labels permutation434 hz
    mixedMoment B raw10805step0 raw10805step0Labels = mixedMoment B raw10805step1 raw10805step1Labels := by
      have ha : raw10805step1 = (fun i j => raw10805step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10805step1 raw10805step0; decide +kernel
      have hl : raw10805step1Labels = raw10805step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10805step0 raw10805step0Labels permutation40 permutation2
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw10806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10806step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10806step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10806 raw10806Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw10806 raw10806Labels = mixedMoment B raw10806step0 raw10806step0Labels := by
      have hz : ∀ j, raw10806 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10806step0 = (fun i j => raw10806 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10806step0 raw10806; decide +kernel
      have hl : raw10806step0Labels = raw10806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10806 raw10806Labels permutation346 hz
    mixedMoment B raw10806step0 raw10806step0Labels = mixedMoment B raw10806step1 raw10806step1Labels := by
      have ha : raw10806step1 = (fun i j => raw10806step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10806step1 raw10806step0; decide +kernel
      have hl : raw10806step1Labels = raw10806step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10806step0 raw10806step0Labels permutation40 permutation2
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw10807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10807step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw10807step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10807step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw10807step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10807 raw10807Labels = mixedMoment B node4901 node4901Labels := by
  calc
    mixedMoment B raw10807 raw10807Labels = mixedMoment B raw10807step0 raw10807step0Labels := by
      have hz : ∀ j, raw10807 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10807step0 = (fun i j => raw10807 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10807step0 raw10807; decide +kernel
      have hl : raw10807step0Labels = raw10807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10807 raw10807Labels permutation520 hz
    mixedMoment B raw10807step0 raw10807step0Labels = mixedMoment B raw10807step1 raw10807step1Labels := by
      have hz : ∀ j, raw10807step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10807step1 = (fun i j => raw10807step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10807step1 raw10807step0; decide +kernel
      have hl : raw10807step1Labels = raw10807step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10807step0 raw10807step0Labels permutation104 hz
    mixedMoment B raw10807step1 raw10807step1Labels = mixedMoment B raw10807step2 raw10807step2Labels := by
      have hz : ∀ j, raw10807step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10807step2 = (fun i j => raw10807step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10807step2 raw10807step1; decide +kernel
      have hl : raw10807step2Labels = raw10807step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10807step1 raw10807step1Labels permutation20 hz
    _ = mixedMoment B node4901 node4901Labels := by rfl

def raw10808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10808step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw10808step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10808step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10808step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10808step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10808step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10808step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10808step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10808 raw10808Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw10808 raw10808Labels = mixedMoment B raw10808step0 raw10808step0Labels := by
      have hz : ∀ j, raw10808 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10808step0 = (fun i j => raw10808 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10808step0 raw10808; decide +kernel
      have hl : raw10808step0Labels = raw10808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10808 raw10808Labels permutation434 hz
    mixedMoment B raw10808step0 raw10808step0Labels = mixedMoment B raw10808step1 raw10808step1Labels := by
      have hz : ∀ j, raw10808step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10808step1 = (fun i j => raw10808step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10808step1 raw10808step0; decide +kernel
      have hl : raw10808step1Labels = raw10808step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10808step0 raw10808step0Labels permutation80 hz
    mixedMoment B raw10808step1 raw10808step1Labels = mixedMoment B raw10808step2 raw10808step2Labels := by
      have ha : raw10808step2 = (fun i j => raw10808step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10808step2 raw10808step1; decide +kernel
      have hl : raw10808step2Labels = raw10808step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10808step1 raw10808step1Labels permutation11 permutation7
    mixedMoment B raw10808step2 raw10808step2Labels = mixedMoment B raw10808step3 raw10808step3Labels := by
      have ha : raw10808step3 = -raw10808step2 := by apply Matrix.ext; change ∀ i j, raw10808step3 i j = -(raw10808step2 i j); unfold raw10808step3 raw10808step2; decide +kernel
      have hl : raw10808step3Labels = raw10808step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10808step3 raw10808step3Labels = mixedMoment B raw10808step4 raw10808step4Labels := by
      have ha : raw10808step4 = raw10808step3 := by apply Matrix.ext; unfold raw10808step4 raw10808step3; decide +kernel
      have hl : raw10808step3Labels = labelEmbedding10 ∘ raw10808step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10808step3 raw10808step3Labels raw10808step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw10809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10809 raw10809Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw10809 raw10809Labels = mixedMoment B raw10809step0 raw10809step0Labels := by
      have hz : ∀ j, raw10809 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10809step0 = (fun i j => raw10809 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10809step0 raw10809; decide +kernel
      have hl : raw10809step0Labels = raw10809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10809 raw10809Labels permutation434 hz
    _ = mixedMoment B node4474 node4474Labels := by rfl

def raw10810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10810 raw10810Labels = mixedMoment B node4879 node4879Labels := by
  calc
    mixedMoment B raw10810 raw10810Labels = mixedMoment B raw10810step0 raw10810step0Labels := by
      have hz : ∀ j, raw10810 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10810step0 = (fun i j => raw10810 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10810step0 raw10810; decide +kernel
      have hl : raw10810step0Labels = raw10810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10810 raw10810Labels permutation434 hz
    _ = mixedMoment B node4879 node4879Labels := by rfl

def raw10811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10811 raw10811Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw10811 raw10811Labels = mixedMoment B raw10811step0 raw10811step0Labels := by
      have ha : raw10811step0 = (fun i j => raw10811 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10811step0 raw10811; decide +kernel
      have hl : raw10811step0Labels = raw10811Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10811 raw10811Labels permutation200 permutation2
    _ = mixedMoment B node4815 node4815Labels := by rfl

def raw10812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10812step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10812step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10812step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10812step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10812step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10812step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10812step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10812step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10812 raw10812Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw10812 raw10812Labels = mixedMoment B raw10812step0 raw10812step0Labels := by
      have hz : ∀ j, raw10812 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10812step0 = (fun i j => raw10812 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10812step0 raw10812; decide +kernel
      have hl : raw10812step0Labels = raw10812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10812 raw10812Labels permutation520 hz
    mixedMoment B raw10812step0 raw10812step0Labels = mixedMoment B raw10812step1 raw10812step1Labels := by
      have hz : ∀ j, raw10812step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10812step1 = (fun i j => raw10812step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10812step1 raw10812step0; decide +kernel
      have hl : raw10812step1Labels = raw10812step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10812step0 raw10812step0Labels permutation104 hz
    mixedMoment B raw10812step1 raw10812step1Labels = mixedMoment B raw10812step2 raw10812step2Labels := by
      have ha : raw10812step2 = (fun i j => raw10812step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10812step2 raw10812step1; decide +kernel
      have hl : raw10812step2Labels = raw10812step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10812step1 raw10812step1Labels permutation11 permutation7
    mixedMoment B raw10812step2 raw10812step2Labels = mixedMoment B raw10812step3 raw10812step3Labels := by
      have ha : raw10812step3 = -raw10812step2 := by apply Matrix.ext; change ∀ i j, raw10812step3 i j = -(raw10812step2 i j); unfold raw10812step3 raw10812step2; decide +kernel
      have hl : raw10812step3Labels = raw10812step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10812step3 raw10812step3Labels = mixedMoment B raw10812step4 raw10812step4Labels := by
      have ha : raw10812step4 = raw10812step3 := by apply Matrix.ext; unfold raw10812step4 raw10812step3; decide +kernel
      have hl : raw10812step3Labels = labelEmbedding10 ∘ raw10812step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10812step3 raw10812step3Labels raw10812step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw10813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10813step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10813step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10813step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10813step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10813step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10813 raw10813Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw10813 raw10813Labels = mixedMoment B raw10813step0 raw10813step0Labels := by
      have hz : ∀ j, raw10813 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10813step0 = (fun i j => raw10813 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10813step0 raw10813; decide +kernel
      have hl : raw10813step0Labels = raw10813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10813 raw10813Labels permutation434 hz
    mixedMoment B raw10813step0 raw10813step0Labels = mixedMoment B raw10813step1 raw10813step1Labels := by
      have ha : raw10813step1 = (fun i j => raw10813step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10813step1 raw10813step0; decide +kernel
      have hl : raw10813step1Labels = raw10813step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10813step0 raw10813step0Labels permutation41 permutation7
    mixedMoment B raw10813step1 raw10813step1Labels = mixedMoment B raw10813step2 raw10813step2Labels := by
      have ha : raw10813step2 = -raw10813step1 := by apply Matrix.ext; change ∀ i j, raw10813step2 i j = -(raw10813step1 i j); unfold raw10813step2 raw10813step1; decide +kernel
      have hl : raw10813step2Labels = raw10813step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10813step2 raw10813step2Labels = mixedMoment B raw10813step3 raw10813step3Labels := by
      have ha : raw10813step3 = raw10813step2 := by apply Matrix.ext; unfold raw10813step3 raw10813step2; decide +kernel
      have hl : raw10813step2Labels = labelEmbedding10 ∘ raw10813step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10813step2 raw10813step2Labels raw10813step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw10814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10814step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10814 raw10814Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw10814 raw10814Labels = mixedMoment B raw10814step0 raw10814step0Labels := by
      have hz : ∀ j, raw10814 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10814step0 = (fun i j => raw10814 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10814step0 raw10814; decide +kernel
      have hl : raw10814step0Labels = raw10814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10814 raw10814Labels permutation346 hz
    _ = mixedMoment B node4474 node4474Labels := by rfl

def raw10815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10815 raw10815Labels = mixedMoment B node4879 node4879Labels := by
  calc
    mixedMoment B raw10815 raw10815Labels = mixedMoment B raw10815step0 raw10815step0Labels := by
      have hz : ∀ j, raw10815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10815step0 = (fun i j => raw10815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10815step0 raw10815; decide +kernel
      have hl : raw10815step0Labels = raw10815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10815 raw10815Labels permutation346 hz
    _ = mixedMoment B node4879 node4879Labels := by rfl

def raw10816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10816step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10816 raw10816Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw10816 raw10816Labels = mixedMoment B raw10816step0 raw10816step0Labels := by
      have ha : raw10816step0 = (fun i j => raw10816 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10816step0 raw10816; decide +kernel
      have hl : raw10816step0Labels = raw10816Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10816 raw10816Labels permutation176 permutation2
    _ = mixedMoment B node4815 node4815Labels := by rfl

def raw10817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10817step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10817step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10817step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10817step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10817step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10817step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10817step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10817step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10817step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10817 raw10817Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw10817 raw10817Labels = mixedMoment B raw10817step0 raw10817step0Labels := by
      have hz : ∀ j, raw10817 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10817step0 = (fun i j => raw10817 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10817step0 raw10817; decide +kernel
      have hl : raw10817step0Labels = raw10817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10817 raw10817Labels permutation520 hz
    mixedMoment B raw10817step0 raw10817step0Labels = mixedMoment B raw10817step1 raw10817step1Labels := by
      have hz : ∀ j, raw10817step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10817step1 = (fun i j => raw10817step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10817step1 raw10817step0; decide +kernel
      have hl : raw10817step1Labels = raw10817step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10817step0 raw10817step0Labels permutation80 hz
    mixedMoment B raw10817step1 raw10817step1Labels = mixedMoment B raw10817step2 raw10817step2Labels := by
      have ha : raw10817step2 = (fun i j => raw10817step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10817step2 raw10817step1; decide +kernel
      have hl : raw10817step2Labels = raw10817step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10817step1 raw10817step1Labels permutation11 permutation7
    mixedMoment B raw10817step2 raw10817step2Labels = mixedMoment B raw10817step3 raw10817step3Labels := by
      have ha : raw10817step3 = -raw10817step2 := by apply Matrix.ext; change ∀ i j, raw10817step3 i j = -(raw10817step2 i j); unfold raw10817step3 raw10817step2; decide +kernel
      have hl : raw10817step3Labels = raw10817step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10817step3 raw10817step3Labels = mixedMoment B raw10817step4 raw10817step4Labels := by
      have ha : raw10817step4 = raw10817step3 := by apply Matrix.ext; unfold raw10817step4 raw10817step3; decide +kernel
      have hl : raw10817step3Labels = labelEmbedding10 ∘ raw10817step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10817step3 raw10817step3Labels raw10817step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw10818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10818step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10818step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10818step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10818step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10818 raw10818Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw10818 raw10818Labels = mixedMoment B raw10818step0 raw10818step0Labels := by
      have hz : ∀ j, raw10818 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10818step0 = (fun i j => raw10818 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10818step0 raw10818; decide +kernel
      have hl : raw10818step0Labels = raw10818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10818 raw10818Labels permutation346 hz
    mixedMoment B raw10818step0 raw10818step0Labels = mixedMoment B raw10818step1 raw10818step1Labels := by
      have ha : raw10818step1 = (fun i j => raw10818step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10818step1 raw10818step0; decide +kernel
      have hl : raw10818step1Labels = raw10818step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10818step0 raw10818step0Labels permutation41 permutation7
    mixedMoment B raw10818step1 raw10818step1Labels = mixedMoment B raw10818step2 raw10818step2Labels := by
      have ha : raw10818step2 = -raw10818step1 := by apply Matrix.ext; change ∀ i j, raw10818step2 i j = -(raw10818step1 i j); unfold raw10818step2 raw10818step1; decide +kernel
      have hl : raw10818step2Labels = raw10818step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10818step2 raw10818step2Labels = mixedMoment B raw10818step3 raw10818step3Labels := by
      have ha : raw10818step3 = raw10818step2 := by apply Matrix.ext; unfold raw10818step3 raw10818step2; decide +kernel
      have hl : raw10818step2Labels = labelEmbedding10 ∘ raw10818step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10818step2 raw10818step2Labels raw10818step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw10819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10819step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10819step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10819 raw10819Labels = mixedMoment B node4480 node4480Labels := by
  calc
    mixedMoment B raw10819 raw10819Labels = mixedMoment B raw10819step0 raw10819step0Labels := by
      have hz : ∀ j, raw10819 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10819step0 = (fun i j => raw10819 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10819step0 raw10819; decide +kernel
      have hl : raw10819step0Labels = raw10819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10819 raw10819Labels permutation434 hz
    mixedMoment B raw10819step0 raw10819step0Labels = mixedMoment B raw10819step1 raw10819step1Labels := by
      have hz : ∀ j, raw10819step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10819step1 = (fun i j => raw10819step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10819step1 raw10819step0; decide +kernel
      have hl : raw10819step1Labels = raw10819step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10819step0 raw10819step0Labels permutation80 hz
    _ = mixedMoment B node4480 node4480Labels := by rfl

def raw10820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10820step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10820step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10820 raw10820Labels = mixedMoment B node4884 node4884Labels := by
  calc
    mixedMoment B raw10820 raw10820Labels = mixedMoment B raw10820step0 raw10820step0Labels := by
      have hz : ∀ j, raw10820 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10820step0 = (fun i j => raw10820 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10820step0 raw10820; decide +kernel
      have hl : raw10820step0Labels = raw10820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10820 raw10820Labels permutation434 hz
    mixedMoment B raw10820step0 raw10820step0Labels = mixedMoment B raw10820step1 raw10820step1Labels := by
      have hz : ∀ j, raw10820step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10820step1 = (fun i j => raw10820step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10820step1 raw10820step0; decide +kernel
      have hl : raw10820step1Labels = raw10820step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10820step0 raw10820step0Labels permutation80 hz
    _ = mixedMoment B node4884 node4884Labels := by rfl

def raw10821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10821step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10821 raw10821Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw10821 raw10821Labels = mixedMoment B raw10821step0 raw10821step0Labels := by
      have hz : ∀ j, raw10821 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10821step0 = (fun i j => raw10821 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10821step0 raw10821; decide +kernel
      have hl : raw10821step0Labels = raw10821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10821 raw10821Labels permutation434 hz
    mixedMoment B raw10821step0 raw10821step0Labels = mixedMoment B raw10821step1 raw10821step1Labels := by
      have ha : raw10821step1 = (fun i j => raw10821step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10821step1 raw10821step0; decide +kernel
      have hl : raw10821step1Labels = raw10821step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10821step0 raw10821step0Labels permutation38 permutation2
    _ = mixedMoment B node4821 node4821Labels := by rfl

def raw10822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10822 raw10822Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw10822 raw10822Labels = mixedMoment B raw10822step0 raw10822step0Labels := by
      have hz : ∀ j, raw10822 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10822step0 = (fun i j => raw10822 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10822step0 raw10822; decide +kernel
      have hl : raw10822step0Labels = raw10822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10822 raw10822Labels permutation346 hz
    mixedMoment B raw10822step0 raw10822step0Labels = mixedMoment B raw10822step1 raw10822step1Labels := by
      have ha : raw10822step1 = (fun i j => raw10822step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10822step1 raw10822step0; decide +kernel
      have hl : raw10822step1Labels = raw10822step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10822step0 raw10822step0Labels permutation38 permutation2
    _ = mixedMoment B node4821 node4821Labels := by rfl

def raw10823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw10823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw10823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10823step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw10823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10823step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10823step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10823 raw10823Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw10823 raw10823Labels = mixedMoment B raw10823step0 raw10823step0Labels := by
      have hz : ∀ j, raw10823 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10823step0 = (fun i j => raw10823 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10823step0 raw10823; decide +kernel
      have hl : raw10823step0Labels = raw10823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10823 raw10823Labels permutation434 hz
    mixedMoment B raw10823step0 raw10823step0Labels = mixedMoment B raw10823step1 raw10823step1Labels := by
      have hz : ∀ j, raw10823step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10823step1 = (fun i j => raw10823step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10823step1 raw10823step0; decide +kernel
      have hl : raw10823step1Labels = raw10823step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10823step0 raw10823step0Labels permutation80 hz
    mixedMoment B raw10823step1 raw10823step1Labels = mixedMoment B raw10823step2 raw10823step2Labels := by
      have ha : raw10823step2 = (fun i j => raw10823step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10823step2 raw10823step1; decide +kernel
      have hl : raw10823step2Labels = raw10823step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10823step1 raw10823step1Labels permutation9 permutation2
    _ = mixedMoment B node4898 node4898Labels := by rfl

def raw10824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10824step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw10824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10824 raw10824Labels = mixedMoment B node4476 node4476Labels := by
  calc
    mixedMoment B raw10824 raw10824Labels = mixedMoment B raw10824step0 raw10824step0Labels := by
      have hz : ∀ j, raw10824 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10824step0 = (fun i j => raw10824 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10824step0 raw10824; decide +kernel
      have hl : raw10824step0Labels = raw10824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10824 raw10824Labels permutation434 hz
    mixedMoment B raw10824step0 raw10824step0Labels = mixedMoment B raw10824step1 raw10824step1Labels := by
      have hz : ∀ j, raw10824step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10824step1 = (fun i j => raw10824step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10824step1 raw10824step0; decide +kernel
      have hl : raw10824step1Labels = raw10824step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10824step0 raw10824step0Labels permutation80 hz
    _ = mixedMoment B node4476 node4476Labels := by rfl

def raw10825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10825step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw10825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10825 raw10825Labels = mixedMoment B node4881 node4881Labels := by
  calc
    mixedMoment B raw10825 raw10825Labels = mixedMoment B raw10825step0 raw10825step0Labels := by
      have hz : ∀ j, raw10825 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10825step0 = (fun i j => raw10825 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10825step0 raw10825; decide +kernel
      have hl : raw10825step0Labels = raw10825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10825 raw10825Labels permutation434 hz
    mixedMoment B raw10825step0 raw10825step0Labels = mixedMoment B raw10825step1 raw10825step1Labels := by
      have hz : ∀ j, raw10825step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10825step1 = (fun i j => raw10825step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10825step1 raw10825step0; decide +kernel
      have hl : raw10825step1Labels = raw10825step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10825step0 raw10825step0Labels permutation80 hz
    _ = mixedMoment B node4881 node4881Labels := by rfl

def raw10826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw10826step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10826 raw10826Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw10826 raw10826Labels = mixedMoment B raw10826step0 raw10826step0Labels := by
      have hz : ∀ j, raw10826 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10826step0 = (fun i j => raw10826 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10826step0 raw10826; decide +kernel
      have hl : raw10826step0Labels = raw10826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10826 raw10826Labels permutation434 hz
    mixedMoment B raw10826step0 raw10826step0Labels = mixedMoment B raw10826step1 raw10826step1Labels := by
      have ha : raw10826step1 = (fun i j => raw10826step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10826step1 raw10826step0; decide +kernel
      have hl : raw10826step1Labels = raw10826step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10826step0 raw10826step0Labels permutation38 permutation2
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw10827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw10827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10827 raw10827Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw10827 raw10827Labels = mixedMoment B raw10827step0 raw10827step0Labels := by
      have hz : ∀ j, raw10827 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10827step0 = (fun i j => raw10827 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10827step0 raw10827; decide +kernel
      have hl : raw10827step0Labels = raw10827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10827 raw10827Labels permutation346 hz
    mixedMoment B raw10827step0 raw10827step0Labels = mixedMoment B raw10827step1 raw10827step1Labels := by
      have ha : raw10827step1 = (fun i j => raw10827step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10827step1 raw10827step0; decide +kernel
      have hl : raw10827step1Labels = raw10827step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10827step0 raw10827step0Labels permutation38 permutation2
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw10828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw10828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw10828step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10828step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw10828step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10828step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw10828step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10828 raw10828Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw10828 raw10828Labels = mixedMoment B raw10828step0 raw10828step0Labels := by
      have hz : ∀ j, raw10828 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10828step0 = (fun i j => raw10828 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10828step0 raw10828; decide +kernel
      have hl : raw10828step0Labels = raw10828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10828 raw10828Labels permutation520 hz
    mixedMoment B raw10828step0 raw10828step0Labels = mixedMoment B raw10828step1 raw10828step1Labels := by
      have hz : ∀ j, raw10828step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10828step1 = (fun i j => raw10828step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10828step1 raw10828step0; decide +kernel
      have hl : raw10828step1Labels = raw10828step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10828step0 raw10828step0Labels permutation104 hz
    mixedMoment B raw10828step1 raw10828step1Labels = mixedMoment B raw10828step2 raw10828step2Labels := by
      have hz : ∀ j, raw10828step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10828step2 = (fun i j => raw10828step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10828step2 raw10828step1; decide +kernel
      have hl : raw10828step2Labels = raw10828step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10828step1 raw10828step1Labels permutation20 hz
    _ = mixedMoment B node4899 node4899Labels := by rfl

def raw10829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10829Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10829step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10829step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10829step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 2, -1], ![-2, -1, 3]]
def raw10829step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10829step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw10829step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10829 raw10829Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw10829 raw10829Labels = mixedMoment B raw10829step0 raw10829step0Labels := by
      have hz : ∀ j, raw10829 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10829step0 = (fun i j => raw10829 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10829step0 raw10829; decide +kernel
      have hl : raw10829step0Labels = raw10829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10829 raw10829Labels permutation434 hz
    mixedMoment B raw10829step0 raw10829step0Labels = mixedMoment B raw10829step1 raw10829step1Labels := by
      have hz : ∀ j, raw10829step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10829step1 = (fun i j => raw10829step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10829step1 raw10829step0; decide +kernel
      have hl : raw10829step1Labels = raw10829step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10829step0 raw10829step0Labels permutation80 hz
    mixedMoment B raw10829step1 raw10829step1Labels = mixedMoment B raw10829step2 raw10829step2Labels := by
      have ha : raw10829step2 = (fun i j => raw10829step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10829step2 raw10829step1; decide +kernel
      have hl : raw10829step2Labels = raw10829step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10829step1 raw10829step1Labels permutation11 permutation6
    mixedMoment B raw10829step2 raw10829step2Labels = mixedMoment B raw10829step3 raw10829step3Labels := by
      have ha : raw10829step3 = -raw10829step2 := by apply Matrix.ext; change ∀ i j, raw10829step3 i j = -(raw10829step2 i j); unfold raw10829step3 raw10829step2; decide +kernel
      have hl : raw10829step3Labels = raw10829step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw10830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10830step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw10830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10830step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10830step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10830 raw10830Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw10830 raw10830Labels = mixedMoment B raw10830step0 raw10830step0Labels := by
      have hz : ∀ j, raw10830 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10830step0 = (fun i j => raw10830 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10830step0 raw10830; decide +kernel
      have hl : raw10830step0Labels = raw10830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10830 raw10830Labels permutation434 hz
    mixedMoment B raw10830step0 raw10830step0Labels = mixedMoment B raw10830step1 raw10830step1Labels := by
      have ha : raw10830step1 = (fun i j => raw10830step0 (permutation47 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10830step1 raw10830step0; decide +kernel
      have hl : raw10830step1Labels = raw10830step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10830step0 raw10830step0Labels permutation47 permutation6
    mixedMoment B raw10830step1 raw10830step1Labels = mixedMoment B raw10830step2 raw10830step2Labels := by
      have ha : raw10830step2 = -raw10830step1 := by apply Matrix.ext; change ∀ i j, raw10830step2 i j = -(raw10830step1 i j); unfold raw10830step2 raw10830step1; decide +kernel
      have hl : raw10830step2Labels = raw10830step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw10831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10831Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10831step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw10831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10831step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10831step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10831 raw10831Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw10831 raw10831Labels = mixedMoment B raw10831step0 raw10831step0Labels := by
      have hz : ∀ j, raw10831 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10831step0 = (fun i j => raw10831 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10831step0 raw10831; decide +kernel
      have hl : raw10831step0Labels = raw10831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10831 raw10831Labels permutation346 hz
    mixedMoment B raw10831step0 raw10831step0Labels = mixedMoment B raw10831step1 raw10831step1Labels := by
      have ha : raw10831step1 = (fun i j => raw10831step0 (permutation47 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10831step1 raw10831step0; decide +kernel
      have hl : raw10831step1Labels = raw10831step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10831step0 raw10831step0Labels permutation47 permutation6
    mixedMoment B raw10831step1 raw10831step1Labels = mixedMoment B raw10831step2 raw10831step2Labels := by
      have ha : raw10831step2 = -raw10831step1 := by apply Matrix.ext; change ∀ i j, raw10831step2 i j = -(raw10831step1 i j); unfold raw10831step2 raw10831step1; decide +kernel
      have hl : raw10831step2Labels = raw10831step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw10832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10832Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10832step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10832step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw10832step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10832step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw10832step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10832step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 2, -1], ![-2, 0, 2]]
def raw10832step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10832step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw10832step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10832 raw10832Labels = mixedMoment B node3121 node3121Labels := by
  calc
    mixedMoment B raw10832 raw10832Labels = mixedMoment B raw10832step0 raw10832step0Labels := by
      have hz : ∀ j, raw10832 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10832step0 = (fun i j => raw10832 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10832step0 raw10832; decide +kernel
      have hl : raw10832step0Labels = raw10832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10832 raw10832Labels permutation520 hz
    mixedMoment B raw10832step0 raw10832step0Labels = mixedMoment B raw10832step1 raw10832step1Labels := by
      have hz : ∀ j, raw10832step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10832step1 = (fun i j => raw10832step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10832step1 raw10832step0; decide +kernel
      have hl : raw10832step1Labels = raw10832step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10832step0 raw10832step0Labels permutation104 hz
    mixedMoment B raw10832step1 raw10832step1Labels = mixedMoment B raw10832step2 raw10832step2Labels := by
      have hz : ∀ j, raw10832step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10832step2 = (fun i j => raw10832step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10832step2 raw10832step1; decide +kernel
      have hl : raw10832step2Labels = raw10832step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10832step1 raw10832step1Labels permutation20 hz
    mixedMoment B raw10832step2 raw10832step2Labels = mixedMoment B raw10832step3 raw10832step3Labels := by
      have ha : raw10832step3 = (fun i j => raw10832step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10832step3 raw10832step2; decide +kernel
      have hl : raw10832step3Labels = raw10832step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10832step2 raw10832step2Labels permutation3 permutation6
    mixedMoment B raw10832step3 raw10832step3Labels = mixedMoment B raw10832step4 raw10832step4Labels := by
      have ha : raw10832step4 = -raw10832step3 := by apply Matrix.ext; change ∀ i j, raw10832step4 i j = -(raw10832step3 i j); unfold raw10832step4 raw10832step3; decide +kernel
      have hl : raw10832step4Labels = raw10832step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3121 node3121Labels := by rfl

def raw10833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10833Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10833step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10833step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw10833step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10833step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw10833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10833step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10833step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10833 raw10833Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw10833 raw10833Labels = mixedMoment B raw10833step0 raw10833step0Labels := by
      have hz : ∀ j, raw10833 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10833step0 = (fun i j => raw10833 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10833step0 raw10833; decide +kernel
      have hl : raw10833step0Labels = raw10833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10833 raw10833Labels permutation434 hz
    mixedMoment B raw10833step0 raw10833step0Labels = mixedMoment B raw10833step1 raw10833step1Labels := by
      have hz : ∀ j, raw10833step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10833step1 = (fun i j => raw10833step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10833step1 raw10833step0; decide +kernel
      have hl : raw10833step1Labels = raw10833step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10833step0 raw10833step0Labels permutation80 hz
    mixedMoment B raw10833step1 raw10833step1Labels = mixedMoment B raw10833step2 raw10833step2Labels := by
      have ha : raw10833step2 = (fun i j => raw10833step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10833step2 raw10833step1; decide +kernel
      have hl : raw10833step2Labels = raw10833step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10833step1 raw10833step1Labels permutation11 permutation6
    mixedMoment B raw10833step2 raw10833step2Labels = mixedMoment B raw10833step3 raw10833step3Labels := by
      have ha : raw10833step3 = -raw10833step2 := by apply Matrix.ext; change ∀ i j, raw10833step3 i j = -(raw10833step2 i j); unfold raw10833step3 raw10833step2; decide +kernel
      have hl : raw10833step3Labels = raw10833step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3101 node3101Labels := by rfl

def raw10834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10834Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10834step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10834step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10834step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw10834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10834 raw10834Labels = mixedMoment B node1443 node1443Labels := by
  calc
    mixedMoment B raw10834 raw10834Labels = mixedMoment B raw10834step0 raw10834step0Labels := by
      have hz : ∀ j, raw10834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10834step0 = (fun i j => raw10834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10834step0 raw10834; decide +kernel
      have hl : raw10834step0Labels = raw10834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10834 raw10834Labels permutation434 hz
    mixedMoment B raw10834step0 raw10834step0Labels = mixedMoment B raw10834step1 raw10834step1Labels := by
      have hz : ∀ j, raw10834step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10834step1 = (fun i j => raw10834step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10834step1 raw10834step0; decide +kernel
      have hl : raw10834step1Labels = raw10834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10834step0 raw10834step0Labels permutation80 hz
    mixedMoment B raw10834step1 raw10834step1Labels = mixedMoment B raw10834step2 raw10834step2Labels := by
      have ha : raw10834step2 = (fun i j => raw10834step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10834step2 raw10834step1; decide +kernel
      have hl : raw10834step2Labels = raw10834step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10834step1 raw10834step1Labels permutation8 permutation3
    _ = mixedMoment B node1443 node1443Labels := by rfl

def raw10835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10835step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw10835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10835 raw10835Labels = mixedMoment B node3211 node3211Labels := by
  calc
    mixedMoment B raw10835 raw10835Labels = mixedMoment B raw10835step0 raw10835step0Labels := by
      have hz : ∀ j, raw10835 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10835step0 = (fun i j => raw10835 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10835step0 raw10835; decide +kernel
      have hl : raw10835step0Labels = raw10835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10835 raw10835Labels permutation434 hz
    mixedMoment B raw10835step0 raw10835step0Labels = mixedMoment B raw10835step1 raw10835step1Labels := by
      have ha : raw10835step1 = (fun i j => raw10835step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10835step1 raw10835step0; decide +kernel
      have hl : raw10835step1Labels = raw10835step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10835step0 raw10835step0Labels permutation38 permutation3
    _ = mixedMoment B node3211 node3211Labels := by rfl

def raw10836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10836Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10836step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw10836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10836 raw10836Labels = mixedMoment B node3211 node3211Labels := by
  calc
    mixedMoment B raw10836 raw10836Labels = mixedMoment B raw10836step0 raw10836step0Labels := by
      have hz : ∀ j, raw10836 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10836step0 = (fun i j => raw10836 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10836step0 raw10836; decide +kernel
      have hl : raw10836step0Labels = raw10836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10836 raw10836Labels permutation346 hz
    mixedMoment B raw10836step0 raw10836step0Labels = mixedMoment B raw10836step1 raw10836step1Labels := by
      have ha : raw10836step1 = (fun i j => raw10836step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10836step1 raw10836step0; decide +kernel
      have hl : raw10836step1Labels = raw10836step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10836step0 raw10836step0Labels permutation38 permutation3
    _ = mixedMoment B node3211 node3211Labels := by rfl

def raw10837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10837Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10837step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10837step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw10837step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10837step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw10837step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10837step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw10837step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10837 raw10837Labels = mixedMoment B node3231 node3231Labels := by
  calc
    mixedMoment B raw10837 raw10837Labels = mixedMoment B raw10837step0 raw10837step0Labels := by
      have hz : ∀ j, raw10837 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10837step0 = (fun i j => raw10837 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10837step0 raw10837; decide +kernel
      have hl : raw10837step0Labels = raw10837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10837 raw10837Labels permutation520 hz
    mixedMoment B raw10837step0 raw10837step0Labels = mixedMoment B raw10837step1 raw10837step1Labels := by
      have hz : ∀ j, raw10837step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10837step1 = (fun i j => raw10837step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10837step1 raw10837step0; decide +kernel
      have hl : raw10837step1Labels = raw10837step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10837step0 raw10837step0Labels permutation104 hz
    mixedMoment B raw10837step1 raw10837step1Labels = mixedMoment B raw10837step2 raw10837step2Labels := by
      have hz : ∀ j, raw10837step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10837step2 = (fun i j => raw10837step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10837step2 raw10837step1; decide +kernel
      have hl : raw10837step2Labels = raw10837step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10837step1 raw10837step1Labels permutation20 hz
    mixedMoment B raw10837step2 raw10837step2Labels = mixedMoment B raw10837step3 raw10837step3Labels := by
      have ha : raw10837step3 = (fun i j => raw10837step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10837step3 raw10837step2; decide +kernel
      have hl : raw10837step3Labels = raw10837step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10837step2 raw10837step2Labels permutation2 permutation3
    _ = mixedMoment B node3231 node3231Labels := by rfl

def raw10838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10838Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10838step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw10838step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10838step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw10838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10838step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw10838step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10838 raw10838Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw10838 raw10838Labels = mixedMoment B raw10838step0 raw10838step0Labels := by
      have hz : ∀ j, raw10838 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10838step0 = (fun i j => raw10838 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10838step0 raw10838; decide +kernel
      have hl : raw10838step0Labels = raw10838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10838 raw10838Labels permutation434 hz
    mixedMoment B raw10838step0 raw10838step0Labels = mixedMoment B raw10838step1 raw10838step1Labels := by
      have hz : ∀ j, raw10838step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10838step1 = (fun i j => raw10838step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10838step1 raw10838step0; decide +kernel
      have hl : raw10838step1Labels = raw10838step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10838step0 raw10838step0Labels permutation80 hz
    mixedMoment B raw10838step1 raw10838step1Labels = mixedMoment B raw10838step2 raw10838step2Labels := by
      have ha : raw10838step2 = (fun i j => raw10838step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10838step2 raw10838step1; decide +kernel
      have hl : raw10838step2Labels = raw10838step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10838step1 raw10838step1Labels permutation11 permutation6
    mixedMoment B raw10838step2 raw10838step2Labels = mixedMoment B raw10838step3 raw10838step3Labels := by
      have ha : raw10838step3 = -raw10838step2 := by apply Matrix.ext; change ∀ i j, raw10838step3 i j = -(raw10838step2 i j); unfold raw10838step3 raw10838step2; decide +kernel
      have hl : raw10838step3Labels = raw10838step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw10839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10839step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10839step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10839 raw10839Labels = mixedMoment B node1370 node1370Labels := by
  calc
    mixedMoment B raw10839 raw10839Labels = mixedMoment B raw10839step0 raw10839step0Labels := by
      have hz : ∀ j, raw10839 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10839step0 = (fun i j => raw10839 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10839step0 raw10839; decide +kernel
      have hl : raw10839step0Labels = raw10839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10839 raw10839Labels permutation434 hz
    mixedMoment B raw10839step0 raw10839step0Labels = mixedMoment B raw10839step1 raw10839step1Labels := by
      have ha : raw10839step1 = (fun i j => raw10839step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10839step1 raw10839step0; decide +kernel
      have hl : raw10839step1Labels = raw10839step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10839step0 raw10839step0Labels permutation32 permutation3
    _ = mixedMoment B node1370 node1370Labels := by rfl

def raw10840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10840step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10840step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10840 raw10840Labels = mixedMoment B node3158 node3158Labels := by
  calc
    mixedMoment B raw10840 raw10840Labels = mixedMoment B raw10840step0 raw10840step0Labels := by
      have hz : ∀ j, raw10840 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10840step0 = (fun i j => raw10840 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10840step0 raw10840; decide +kernel
      have hl : raw10840step0Labels = raw10840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10840 raw10840Labels permutation434 hz
    mixedMoment B raw10840step0 raw10840step0Labels = mixedMoment B raw10840step1 raw10840step1Labels := by
      have ha : raw10840step1 = (fun i j => raw10840step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10840step1 raw10840step0; decide +kernel
      have hl : raw10840step1Labels = raw10840step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10840step0 raw10840step0Labels permutation32 permutation3
    _ = mixedMoment B node3158 node3158Labels := by rfl

def raw10841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10841 raw10841Labels = mixedMoment B node3197 node3197Labels := by
  calc
    mixedMoment B raw10841 raw10841Labels = mixedMoment B raw10841step0 raw10841step0Labels := by
      have ha : raw10841step0 = (fun i j => raw10841 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10841step0 raw10841; decide +kernel
      have hl : raw10841step0Labels = raw10841Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10841 raw10841Labels permutation200 permutation3
    _ = mixedMoment B node3197 node3197Labels := by rfl

def raw10842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10842step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10842step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10842step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10842step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw10842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10842 raw10842Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw10842 raw10842Labels = mixedMoment B raw10842step0 raw10842step0Labels := by
      have hz : ∀ j, raw10842 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10842step0 = (fun i j => raw10842 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10842step0 raw10842; decide +kernel
      have hl : raw10842step0Labels = raw10842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10842 raw10842Labels permutation520 hz
    mixedMoment B raw10842step0 raw10842step0Labels = mixedMoment B raw10842step1 raw10842step1Labels := by
      have hz : ∀ j, raw10842step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10842step1 = (fun i j => raw10842step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10842step1 raw10842step0; decide +kernel
      have hl : raw10842step1Labels = raw10842step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10842step0 raw10842step0Labels permutation104 hz
    mixedMoment B raw10842step1 raw10842step1Labels = mixedMoment B raw10842step2 raw10842step2Labels := by
      have ha : raw10842step2 = (fun i j => raw10842step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10842step2 raw10842step1; decide +kernel
      have hl : raw10842step2Labels = raw10842step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10842step1 raw10842step1Labels permutation8 permutation3
    _ = mixedMoment B node3225 node3225Labels := by rfl

def raw10843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10843step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10843 raw10843Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw10843 raw10843Labels = mixedMoment B raw10843step0 raw10843step0Labels := by
      have hz : ∀ j, raw10843 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10843step0 = (fun i j => raw10843 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10843step0 raw10843; decide +kernel
      have hl : raw10843step0Labels = raw10843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10843 raw10843Labels permutation434 hz
    mixedMoment B raw10843step0 raw10843step0Labels = mixedMoment B raw10843step1 raw10843step1Labels := by
      have ha : raw10843step1 = (fun i j => raw10843step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10843step1 raw10843step0; decide +kernel
      have hl : raw10843step1Labels = raw10843step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10843step0 raw10843step0Labels permutation36 permutation3
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw10844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10844step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10844 raw10844Labels = mixedMoment B node1370 node1370Labels := by
  calc
    mixedMoment B raw10844 raw10844Labels = mixedMoment B raw10844step0 raw10844step0Labels := by
      have hz : ∀ j, raw10844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10844step0 = (fun i j => raw10844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10844step0 raw10844; decide +kernel
      have hl : raw10844step0Labels = raw10844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10844 raw10844Labels permutation346 hz
    mixedMoment B raw10844step0 raw10844step0Labels = mixedMoment B raw10844step1 raw10844step1Labels := by
      have ha : raw10844step1 = (fun i j => raw10844step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10844step1 raw10844step0; decide +kernel
      have hl : raw10844step1Labels = raw10844step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10844step0 raw10844step0Labels permutation32 permutation3
    _ = mixedMoment B node1370 node1370Labels := by rfl

def raw10845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10845Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10845step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10845 raw10845Labels = mixedMoment B node3158 node3158Labels := by
  calc
    mixedMoment B raw10845 raw10845Labels = mixedMoment B raw10845step0 raw10845step0Labels := by
      have hz : ∀ j, raw10845 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10845step0 = (fun i j => raw10845 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10845step0 raw10845; decide +kernel
      have hl : raw10845step0Labels = raw10845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10845 raw10845Labels permutation346 hz
    mixedMoment B raw10845step0 raw10845step0Labels = mixedMoment B raw10845step1 raw10845step1Labels := by
      have ha : raw10845step1 = (fun i j => raw10845step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10845step1 raw10845step0; decide +kernel
      have hl : raw10845step1Labels = raw10845step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10845step0 raw10845step0Labels permutation32 permutation3
    _ = mixedMoment B node3158 node3158Labels := by rfl

def raw10846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10846Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10846 raw10846Labels = mixedMoment B node3197 node3197Labels := by
  calc
    mixedMoment B raw10846 raw10846Labels = mixedMoment B raw10846step0 raw10846step0Labels := by
      have ha : raw10846step0 = (fun i j => raw10846 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10846step0 raw10846; decide +kernel
      have hl : raw10846step0Labels = raw10846Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10846 raw10846Labels permutation176 permutation3
    _ = mixedMoment B node3197 node3197Labels := by rfl

def raw10847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10847Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10847step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10847step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10847step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw10847step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10847 raw10847Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw10847 raw10847Labels = mixedMoment B raw10847step0 raw10847step0Labels := by
      have hz : ∀ j, raw10847 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10847step0 = (fun i j => raw10847 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10847step0 raw10847; decide +kernel
      have hl : raw10847step0Labels = raw10847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10847 raw10847Labels permutation520 hz
    mixedMoment B raw10847step0 raw10847step0Labels = mixedMoment B raw10847step1 raw10847step1Labels := by
      have hz : ∀ j, raw10847step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10847step1 = (fun i j => raw10847step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10847step1 raw10847step0; decide +kernel
      have hl : raw10847step1Labels = raw10847step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10847step0 raw10847step0Labels permutation80 hz
    mixedMoment B raw10847step1 raw10847step1Labels = mixedMoment B raw10847step2 raw10847step2Labels := by
      have ha : raw10847step2 = (fun i j => raw10847step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10847step2 raw10847step1; decide +kernel
      have hl : raw10847step2Labels = raw10847step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10847step1 raw10847step1Labels permutation8 permutation3
    _ = mixedMoment B node3225 node3225Labels := by rfl

def raw10848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10848step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10848 raw10848Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw10848 raw10848Labels = mixedMoment B raw10848step0 raw10848step0Labels := by
      have hz : ∀ j, raw10848 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10848step0 = (fun i j => raw10848 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10848step0 raw10848; decide +kernel
      have hl : raw10848step0Labels = raw10848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10848 raw10848Labels permutation346 hz
    mixedMoment B raw10848step0 raw10848step0Labels = mixedMoment B raw10848step1 raw10848step1Labels := by
      have ha : raw10848step1 = (fun i j => raw10848step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10848step1 raw10848step0; decide +kernel
      have hl : raw10848step1Labels = raw10848step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10848step0 raw10848step0Labels permutation36 permutation3
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw10849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10849step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10849step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10849step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10849step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw10849step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10849 raw10849Labels = mixedMoment B node1375 node1375Labels := by
  calc
    mixedMoment B raw10849 raw10849Labels = mixedMoment B raw10849step0 raw10849step0Labels := by
      have hz : ∀ j, raw10849 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10849step0 = (fun i j => raw10849 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10849step0 raw10849; decide +kernel
      have hl : raw10849step0Labels = raw10849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10849 raw10849Labels permutation434 hz
    mixedMoment B raw10849step0 raw10849step0Labels = mixedMoment B raw10849step1 raw10849step1Labels := by
      have hz : ∀ j, raw10849step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10849step1 = (fun i j => raw10849step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10849step1 raw10849step0; decide +kernel
      have hl : raw10849step1Labels = raw10849step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10849step0 raw10849step0Labels permutation80 hz
    mixedMoment B raw10849step1 raw10849step1Labels = mixedMoment B raw10849step2 raw10849step2Labels := by
      have ha : raw10849step2 = (fun i j => raw10849step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10849step2 raw10849step1; decide +kernel
      have hl : raw10849step2Labels = raw10849step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10849step1 raw10849step1Labels permutation9 permutation3
    _ = mixedMoment B node1375 node1375Labels := by rfl

def raw10850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10850step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10850step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10850step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10850step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw10850step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10850 raw10850Labels = mixedMoment B node3161 node3161Labels := by
  calc
    mixedMoment B raw10850 raw10850Labels = mixedMoment B raw10850step0 raw10850step0Labels := by
      have hz : ∀ j, raw10850 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10850step0 = (fun i j => raw10850 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10850step0 raw10850; decide +kernel
      have hl : raw10850step0Labels = raw10850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10850 raw10850Labels permutation434 hz
    mixedMoment B raw10850step0 raw10850step0Labels = mixedMoment B raw10850step1 raw10850step1Labels := by
      have hz : ∀ j, raw10850step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10850step1 = (fun i j => raw10850step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10850step1 raw10850step0; decide +kernel
      have hl : raw10850step1Labels = raw10850step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10850step0 raw10850step0Labels permutation80 hz
    mixedMoment B raw10850step1 raw10850step1Labels = mixedMoment B raw10850step2 raw10850step2Labels := by
      have ha : raw10850step2 = (fun i j => raw10850step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10850step2 raw10850step1; decide +kernel
      have hl : raw10850step2Labels = raw10850step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10850step1 raw10850step1Labels permutation9 permutation3
    _ = mixedMoment B node3161 node3161Labels := by rfl

def raw10851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10851step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw10851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10851 raw10851Labels = mixedMoment B node3198 node3198Labels := by
  calc
    mixedMoment B raw10851 raw10851Labels = mixedMoment B raw10851step0 raw10851step0Labels := by
      have hz : ∀ j, raw10851 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10851step0 = (fun i j => raw10851 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10851step0 raw10851; decide +kernel
      have hl : raw10851step0Labels = raw10851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10851 raw10851Labels permutation434 hz
    mixedMoment B raw10851step0 raw10851step0Labels = mixedMoment B raw10851step1 raw10851step1Labels := by
      have ha : raw10851step1 = (fun i j => raw10851step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10851step1 raw10851step0; decide +kernel
      have hl : raw10851step1Labels = raw10851step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10851step0 raw10851step0Labels permutation39 permutation3
    _ = mixedMoment B node3198 node3198Labels := by rfl

def raw10852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10852Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10852step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw10852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10852 raw10852Labels = mixedMoment B node3198 node3198Labels := by
  calc
    mixedMoment B raw10852 raw10852Labels = mixedMoment B raw10852step0 raw10852step0Labels := by
      have hz : ∀ j, raw10852 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10852step0 = (fun i j => raw10852 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10852step0 raw10852; decide +kernel
      have hl : raw10852step0Labels = raw10852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10852 raw10852Labels permutation346 hz
    mixedMoment B raw10852step0 raw10852step0Labels = mixedMoment B raw10852step1 raw10852step1Labels := by
      have ha : raw10852step1 = (fun i j => raw10852step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10852step1 raw10852step0; decide +kernel
      have hl : raw10852step1Labels = raw10852step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10852step0 raw10852step0Labels permutation39 permutation3
    _ = mixedMoment B node3198 node3198Labels := by rfl

def raw10853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw10853Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw10853step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10853step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw10853step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10853step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw10853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10853 raw10853Labels = mixedMoment B node3224 node3224Labels := by
  calc
    mixedMoment B raw10853 raw10853Labels = mixedMoment B raw10853step0 raw10853step0Labels := by
      have hz : ∀ j, raw10853 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10853step0 = (fun i j => raw10853 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10853step0 raw10853; decide +kernel
      have hl : raw10853step0Labels = raw10853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10853 raw10853Labels permutation434 hz
    mixedMoment B raw10853step0 raw10853step0Labels = mixedMoment B raw10853step1 raw10853step1Labels := by
      have hz : ∀ j, raw10853step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10853step1 = (fun i j => raw10853step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10853step1 raw10853step0; decide +kernel
      have hl : raw10853step1Labels = raw10853step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10853step0 raw10853step0Labels permutation80 hz
    mixedMoment B raw10853step1 raw10853step1Labels = mixedMoment B raw10853step2 raw10853step2Labels := by
      have ha : raw10853step2 = (fun i j => raw10853step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10853step2 raw10853step1; decide +kernel
      have hl : raw10853step2Labels = raw10853step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10853step1 raw10853step1Labels permutation9 permutation3
    _ = mixedMoment B node3224 node3224Labels := by rfl

def raw10854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10854Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10854step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10854step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw10854step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10854step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw10854step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10854 raw10854Labels = mixedMoment B node1372 node1372Labels := by
  calc
    mixedMoment B raw10854 raw10854Labels = mixedMoment B raw10854step0 raw10854step0Labels := by
      have hz : ∀ j, raw10854 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10854step0 = (fun i j => raw10854 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10854step0 raw10854; decide +kernel
      have hl : raw10854step0Labels = raw10854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10854 raw10854Labels permutation434 hz
    mixedMoment B raw10854step0 raw10854step0Labels = mixedMoment B raw10854step1 raw10854step1Labels := by
      have hz : ∀ j, raw10854step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10854step1 = (fun i j => raw10854step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10854step1 raw10854step0; decide +kernel
      have hl : raw10854step1Labels = raw10854step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10854step0 raw10854step0Labels permutation80 hz
    mixedMoment B raw10854step1 raw10854step1Labels = mixedMoment B raw10854step2 raw10854step2Labels := by
      have ha : raw10854step2 = (fun i j => raw10854step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10854step2 raw10854step1; decide +kernel
      have hl : raw10854step2Labels = raw10854step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10854step1 raw10854step1Labels permutation8 permutation3
    _ = mixedMoment B node1372 node1372Labels := by rfl

def raw10855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10855Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10855step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10855step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw10855step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10855step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -2, 3], ![-3, 3, 0]]
def raw10855step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10855step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw10855step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10855 raw10855Labels = mixedMoment B node2520 node2520Labels := by
  calc
    mixedMoment B raw10855 raw10855Labels = mixedMoment B raw10855step0 raw10855step0Labels := by
      have hz : ∀ j, raw10855 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10855step0 = (fun i j => raw10855 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10855step0 raw10855; decide +kernel
      have hl : raw10855step0Labels = raw10855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10855 raw10855Labels permutation434 hz
    mixedMoment B raw10855step0 raw10855step0Labels = mixedMoment B raw10855step1 raw10855step1Labels := by
      have hz : ∀ j, raw10855step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10855step1 = (fun i j => raw10855step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10855step1 raw10855step0; decide +kernel
      have hl : raw10855step1Labels = raw10855step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10855step0 raw10855step0Labels permutation80 hz
    mixedMoment B raw10855step1 raw10855step1Labels = mixedMoment B raw10855step2 raw10855step2Labels := by
      have ha : raw10855step2 = (fun i j => raw10855step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10855step2 raw10855step1; decide +kernel
      have hl : raw10855step2Labels = raw10855step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10855step1 raw10855step1Labels permutation31 permutation3
    mixedMoment B raw10855step2 raw10855step2Labels = mixedMoment B raw10855step3 raw10855step3Labels := by
      have ha : raw10855step3 = -raw10855step2 := by apply Matrix.ext; change ∀ i j, raw10855step3 i j = -(raw10855step2 i j); unfold raw10855step3 raw10855step2; decide +kernel
      have hl : raw10855step3Labels = raw10855step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2520 node2520Labels := by rfl

def raw10856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10856Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10856step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw10856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw10856step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10856 raw10856Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw10856 raw10856Labels = mixedMoment B raw10856step0 raw10856step0Labels := by
      have hz : ∀ j, raw10856 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10856step0 = (fun i j => raw10856 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10856step0 raw10856; decide +kernel
      have hl : raw10856step0Labels = raw10856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10856 raw10856Labels permutation434 hz
    mixedMoment B raw10856step0 raw10856step0Labels = mixedMoment B raw10856step1 raw10856step1Labels := by
      have ha : raw10856step1 = (fun i j => raw10856step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10856step1 raw10856step0; decide +kernel
      have hl : raw10856step1Labels = raw10856step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10856step0 raw10856step0Labels permutation149 permutation3
    mixedMoment B raw10856step1 raw10856step1Labels = mixedMoment B raw10856step2 raw10856step2Labels := by
      have ha : raw10856step2 = -raw10856step1 := by apply Matrix.ext; change ∀ i j, raw10856step2 i j = -(raw10856step1 i j); unfold raw10856step2 raw10856step1; decide +kernel
      have hl : raw10856step2Labels = raw10856step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2497 node2497Labels := by rfl

def raw10857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10857Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10857step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw10857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw10857step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10857 raw10857Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw10857 raw10857Labels = mixedMoment B raw10857step0 raw10857step0Labels := by
      have hz : ∀ j, raw10857 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10857step0 = (fun i j => raw10857 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10857step0 raw10857; decide +kernel
      have hl : raw10857step0Labels = raw10857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10857 raw10857Labels permutation346 hz
    mixedMoment B raw10857step0 raw10857step0Labels = mixedMoment B raw10857step1 raw10857step1Labels := by
      have ha : raw10857step1 = (fun i j => raw10857step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10857step1 raw10857step0; decide +kernel
      have hl : raw10857step1Labels = raw10857step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10857step0 raw10857step0Labels permutation149 permutation3
    mixedMoment B raw10857step1 raw10857step1Labels = mixedMoment B raw10857step2 raw10857step2Labels := by
      have ha : raw10857step2 = -raw10857step1 := by apply Matrix.ext; change ∀ i j, raw10857step2 i j = -(raw10857step1 i j); unfold raw10857step2 raw10857step1; decide +kernel
      have hl : raw10857step2Labels = raw10857step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2497 node2497Labels := by rfl

def raw10858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw10858Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw10858step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10858step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw10858step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10858step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw10858step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10858step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-3, 3, 0]]
def raw10858step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10858step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw10858step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10858 raw10858Labels = mixedMoment B node2778 node2778Labels := by
  calc
    mixedMoment B raw10858 raw10858Labels = mixedMoment B raw10858step0 raw10858step0Labels := by
      have hz : ∀ j, raw10858 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10858step0 = (fun i j => raw10858 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10858step0 raw10858; decide +kernel
      have hl : raw10858step0Labels = raw10858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10858 raw10858Labels permutation520 hz
    mixedMoment B raw10858step0 raw10858step0Labels = mixedMoment B raw10858step1 raw10858step1Labels := by
      have hz : ∀ j, raw10858step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10858step1 = (fun i j => raw10858step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10858step1 raw10858step0; decide +kernel
      have hl : raw10858step1Labels = raw10858step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10858step0 raw10858step0Labels permutation104 hz
    mixedMoment B raw10858step1 raw10858step1Labels = mixedMoment B raw10858step2 raw10858step2Labels := by
      have hz : ∀ j, raw10858step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10858step2 = (fun i j => raw10858step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10858step2 raw10858step1; decide +kernel
      have hl : raw10858step2Labels = raw10858step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10858step1 raw10858step1Labels permutation20 hz
    mixedMoment B raw10858step2 raw10858step2Labels = mixedMoment B raw10858step3 raw10858step3Labels := by
      have ha : raw10858step3 = (fun i j => raw10858step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10858step3 raw10858step2; decide +kernel
      have hl : raw10858step3Labels = raw10858step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10858step2 raw10858step2Labels permutation7 permutation3
    mixedMoment B raw10858step3 raw10858step3Labels = mixedMoment B raw10858step4 raw10858step4Labels := by
      have ha : raw10858step4 = -raw10858step3 := by apply Matrix.ext; change ∀ i j, raw10858step4 i j = -(raw10858step3 i j); unfold raw10858step4 raw10858step3; decide +kernel
      have hl : raw10858step4Labels = raw10858step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2778 node2778Labels := by rfl

def raw10859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10859Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10859step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10859step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10859step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw10859step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10859step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10859step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10859step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10859step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10859 raw10859Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw10859 raw10859Labels = mixedMoment B raw10859step0 raw10859step0Labels := by
      have hz : ∀ j, raw10859 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10859step0 = (fun i j => raw10859 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10859step0 raw10859; decide +kernel
      have hl : raw10859step0Labels = raw10859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10859 raw10859Labels permutation434 hz
    mixedMoment B raw10859step0 raw10859step0Labels = mixedMoment B raw10859step1 raw10859step1Labels := by
      have hz : ∀ j, raw10859step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10859step1 = (fun i j => raw10859step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10859step1 raw10859step0; decide +kernel
      have hl : raw10859step1Labels = raw10859step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10859step0 raw10859step0Labels permutation80 hz
    mixedMoment B raw10859step1 raw10859step1Labels = mixedMoment B raw10859step2 raw10859step2Labels := by
      have ha : raw10859step2 = (fun i j => raw10859step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10859step2 raw10859step1; decide +kernel
      have hl : raw10859step2Labels = raw10859step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10859step1 raw10859step1Labels permutation11 permutation7
    mixedMoment B raw10859step2 raw10859step2Labels = mixedMoment B raw10859step3 raw10859step3Labels := by
      have ha : raw10859step3 = -raw10859step2 := by apply Matrix.ext; change ∀ i j, raw10859step3 i j = -(raw10859step2 i j); unfold raw10859step3 raw10859step2; decide +kernel
      have hl : raw10859step3Labels = raw10859step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10859step3 raw10859step3Labels = mixedMoment B raw10859step4 raw10859step4Labels := by
      have ha : raw10859step4 = raw10859step3 := by apply Matrix.ext; unfold raw10859step4 raw10859step3; decide +kernel
      have hl : raw10859step3Labels = labelEmbedding1 ∘ raw10859step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10859step3 raw10859step3Labels raw10859step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw10860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10860Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10860step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10860step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10860step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10860step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10860step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10860 raw10860Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw10860 raw10860Labels = mixedMoment B raw10860step0 raw10860step0Labels := by
      have hz : ∀ j, raw10860 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10860step0 = (fun i j => raw10860 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10860step0 raw10860; decide +kernel
      have hl : raw10860step0Labels = raw10860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10860 raw10860Labels permutation434 hz
    mixedMoment B raw10860step0 raw10860step0Labels = mixedMoment B raw10860step1 raw10860step1Labels := by
      have ha : raw10860step1 = (fun i j => raw10860step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10860step1 raw10860step0; decide +kernel
      have hl : raw10860step1Labels = raw10860step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10860step0 raw10860step0Labels permutation41 permutation7
    mixedMoment B raw10860step1 raw10860step1Labels = mixedMoment B raw10860step2 raw10860step2Labels := by
      have ha : raw10860step2 = -raw10860step1 := by apply Matrix.ext; change ∀ i j, raw10860step2 i j = -(raw10860step1 i j); unfold raw10860step2 raw10860step1; decide +kernel
      have hl : raw10860step2Labels = raw10860step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10860step2 raw10860step2Labels = mixedMoment B raw10860step3 raw10860step3Labels := by
      have ha : raw10860step3 = raw10860step2 := by apply Matrix.ext; unfold raw10860step3 raw10860step2; decide +kernel
      have hl : raw10860step2Labels = labelEmbedding1 ∘ raw10860step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10860step2 raw10860step2Labels raw10860step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw10861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10861Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10861step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10861step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10861step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10861step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10861step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10861 raw10861Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw10861 raw10861Labels = mixedMoment B raw10861step0 raw10861step0Labels := by
      have hz : ∀ j, raw10861 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10861step0 = (fun i j => raw10861 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10861step0 raw10861; decide +kernel
      have hl : raw10861step0Labels = raw10861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10861 raw10861Labels permutation346 hz
    mixedMoment B raw10861step0 raw10861step0Labels = mixedMoment B raw10861step1 raw10861step1Labels := by
      have ha : raw10861step1 = (fun i j => raw10861step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10861step1 raw10861step0; decide +kernel
      have hl : raw10861step1Labels = raw10861step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10861step0 raw10861step0Labels permutation41 permutation7
    mixedMoment B raw10861step1 raw10861step1Labels = mixedMoment B raw10861step2 raw10861step2Labels := by
      have ha : raw10861step2 = -raw10861step1 := by apply Matrix.ext; change ∀ i j, raw10861step2 i j = -(raw10861step1 i j); unfold raw10861step2 raw10861step1; decide +kernel
      have hl : raw10861step2Labels = raw10861step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10861step2 raw10861step2Labels = mixedMoment B raw10861step3 raw10861step3Labels := by
      have ha : raw10861step3 = raw10861step2 := by apply Matrix.ext; unfold raw10861step3 raw10861step2; decide +kernel
      have hl : raw10861step2Labels = labelEmbedding1 ∘ raw10861step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10861step2 raw10861step2Labels raw10861step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw10862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10862Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10862step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10862step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw10862step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10862step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw10862step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10862step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw10862step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10862step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10862step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10862step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10862step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10862 raw10862Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw10862 raw10862Labels = mixedMoment B raw10862step0 raw10862step0Labels := by
      have hz : ∀ j, raw10862 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10862step0 = (fun i j => raw10862 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10862step0 raw10862; decide +kernel
      have hl : raw10862step0Labels = raw10862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10862 raw10862Labels permutation520 hz
    mixedMoment B raw10862step0 raw10862step0Labels = mixedMoment B raw10862step1 raw10862step1Labels := by
      have hz : ∀ j, raw10862step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10862step1 = (fun i j => raw10862step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10862step1 raw10862step0; decide +kernel
      have hl : raw10862step1Labels = raw10862step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10862step0 raw10862step0Labels permutation104 hz
    mixedMoment B raw10862step1 raw10862step1Labels = mixedMoment B raw10862step2 raw10862step2Labels := by
      have hz : ∀ j, raw10862step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10862step2 = (fun i j => raw10862step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10862step2 raw10862step1; decide +kernel
      have hl : raw10862step2Labels = raw10862step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10862step1 raw10862step1Labels permutation20 hz
    mixedMoment B raw10862step2 raw10862step2Labels = mixedMoment B raw10862step3 raw10862step3Labels := by
      have ha : raw10862step3 = (fun i j => raw10862step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10862step3 raw10862step2; decide +kernel
      have hl : raw10862step3Labels = raw10862step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10862step2 raw10862step2Labels permutation3 permutation7
    mixedMoment B raw10862step3 raw10862step3Labels = mixedMoment B raw10862step4 raw10862step4Labels := by
      have ha : raw10862step4 = -raw10862step3 := by apply Matrix.ext; change ∀ i j, raw10862step4 i j = -(raw10862step3 i j); unfold raw10862step4 raw10862step3; decide +kernel
      have hl : raw10862step4Labels = raw10862step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10862step4 raw10862step4Labels = mixedMoment B raw10862step5 raw10862step5Labels := by
      have ha : raw10862step5 = raw10862step4 := by apply Matrix.ext; unfold raw10862step5 raw10862step4; decide +kernel
      have hl : raw10862step4Labels = labelEmbedding1 ∘ raw10862step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10862step4 raw10862step4Labels raw10862step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2788 node2788Labels := by rfl

def raw10863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10863Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10863step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw10863step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10863step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10863step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10863step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10863step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10863step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10863step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10863 raw10863Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw10863 raw10863Labels = mixedMoment B raw10863step0 raw10863step0Labels := by
      have hz : ∀ j, raw10863 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10863step0 = (fun i j => raw10863 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10863step0 raw10863; decide +kernel
      have hl : raw10863step0Labels = raw10863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10863 raw10863Labels permutation434 hz
    mixedMoment B raw10863step0 raw10863step0Labels = mixedMoment B raw10863step1 raw10863step1Labels := by
      have hz : ∀ j, raw10863step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10863step1 = (fun i j => raw10863step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10863step1 raw10863step0; decide +kernel
      have hl : raw10863step1Labels = raw10863step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10863step0 raw10863step0Labels permutation80 hz
    mixedMoment B raw10863step1 raw10863step1Labels = mixedMoment B raw10863step2 raw10863step2Labels := by
      have ha : raw10863step2 = (fun i j => raw10863step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10863step2 raw10863step1; decide +kernel
      have hl : raw10863step2Labels = raw10863step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10863step1 raw10863step1Labels permutation11 permutation7
    mixedMoment B raw10863step2 raw10863step2Labels = mixedMoment B raw10863step3 raw10863step3Labels := by
      have ha : raw10863step3 = -raw10863step2 := by apply Matrix.ext; change ∀ i j, raw10863step3 i j = -(raw10863step2 i j); unfold raw10863step3 raw10863step2; decide +kernel
      have hl : raw10863step3Labels = raw10863step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10863step3 raw10863step3Labels = mixedMoment B raw10863step4 raw10863step4Labels := by
      have ha : raw10863step4 = raw10863step3 := by apply Matrix.ext; unfold raw10863step4 raw10863step3; decide +kernel
      have hl : raw10863step3Labels = labelEmbedding1 ∘ raw10863step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10863step3 raw10863step3Labels raw10863step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw10864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10864Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10864step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10864step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10864step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10864step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10864step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10864step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10864step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10864step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10864 raw10864Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw10864 raw10864Labels = mixedMoment B raw10864step0 raw10864step0Labels := by
      have hz : ∀ j, raw10864 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10864step0 = (fun i j => raw10864 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10864step0 raw10864; decide +kernel
      have hl : raw10864step0Labels = raw10864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10864 raw10864Labels permutation434 hz
    mixedMoment B raw10864step0 raw10864step0Labels = mixedMoment B raw10864step1 raw10864step1Labels := by
      have hz : ∀ j, raw10864step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10864step1 = (fun i j => raw10864step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10864step1 raw10864step0; decide +kernel
      have hl : raw10864step1Labels = raw10864step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10864step0 raw10864step0Labels permutation80 hz
    mixedMoment B raw10864step1 raw10864step1Labels = mixedMoment B raw10864step2 raw10864step2Labels := by
      have ha : raw10864step2 = (fun i j => raw10864step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10864step2 raw10864step1; decide +kernel
      have hl : raw10864step2Labels = raw10864step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10864step1 raw10864step1Labels permutation11 permutation7
    mixedMoment B raw10864step2 raw10864step2Labels = mixedMoment B raw10864step3 raw10864step3Labels := by
      have ha : raw10864step3 = -raw10864step2 := by apply Matrix.ext; change ∀ i j, raw10864step3 i j = -(raw10864step2 i j); unfold raw10864step3 raw10864step2; decide +kernel
      have hl : raw10864step3Labels = raw10864step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10864step3 raw10864step3Labels = mixedMoment B raw10864step4 raw10864step4Labels := by
      have ha : raw10864step4 = raw10864step3 := by apply Matrix.ext; unfold raw10864step4 raw10864step3; decide +kernel
      have hl : raw10864step3Labels = labelEmbedding1 ∘ raw10864step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10864step3 raw10864step3Labels raw10864step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

def raw10865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10865Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10865step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10865step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10865step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10865step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10865step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10865 raw10865Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw10865 raw10865Labels = mixedMoment B raw10865step0 raw10865step0Labels := by
      have hz : ∀ j, raw10865 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10865step0 = (fun i j => raw10865 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10865step0 raw10865; decide +kernel
      have hl : raw10865step0Labels = raw10865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10865 raw10865Labels permutation434 hz
    mixedMoment B raw10865step0 raw10865step0Labels = mixedMoment B raw10865step1 raw10865step1Labels := by
      have ha : raw10865step1 = (fun i j => raw10865step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10865step1 raw10865step0; decide +kernel
      have hl : raw10865step1Labels = raw10865step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10865step0 raw10865step0Labels permutation41 permutation7
    mixedMoment B raw10865step1 raw10865step1Labels = mixedMoment B raw10865step2 raw10865step2Labels := by
      have ha : raw10865step2 = -raw10865step1 := by apply Matrix.ext; change ∀ i j, raw10865step2 i j = -(raw10865step1 i j); unfold raw10865step2 raw10865step1; decide +kernel
      have hl : raw10865step2Labels = raw10865step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10865step2 raw10865step2Labels = mixedMoment B raw10865step3 raw10865step3Labels := by
      have ha : raw10865step3 = raw10865step2 := by apply Matrix.ext; unfold raw10865step3 raw10865step2; decide +kernel
      have hl : raw10865step2Labels = labelEmbedding1 ∘ raw10865step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10865step2 raw10865step2Labels raw10865step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw10866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10866Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10866step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10866step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10866step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10866step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10866step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10866 raw10866Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw10866 raw10866Labels = mixedMoment B raw10866step0 raw10866step0Labels := by
      have hz : ∀ j, raw10866 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10866step0 = (fun i j => raw10866 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10866step0 raw10866; decide +kernel
      have hl : raw10866step0Labels = raw10866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10866 raw10866Labels permutation346 hz
    mixedMoment B raw10866step0 raw10866step0Labels = mixedMoment B raw10866step1 raw10866step1Labels := by
      have ha : raw10866step1 = (fun i j => raw10866step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10866step1 raw10866step0; decide +kernel
      have hl : raw10866step1Labels = raw10866step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10866step0 raw10866step0Labels permutation41 permutation7
    mixedMoment B raw10866step1 raw10866step1Labels = mixedMoment B raw10866step2 raw10866step2Labels := by
      have ha : raw10866step2 = -raw10866step1 := by apply Matrix.ext; change ∀ i j, raw10866step2 i j = -(raw10866step1 i j); unfold raw10866step2 raw10866step1; decide +kernel
      have hl : raw10866step2Labels = raw10866step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10866step2 raw10866step2Labels = mixedMoment B raw10866step3 raw10866step3Labels := by
      have ha : raw10866step3 = raw10866step2 := by apply Matrix.ext; unfold raw10866step3 raw10866step2; decide +kernel
      have hl : raw10866step2Labels = labelEmbedding1 ∘ raw10866step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10866step2 raw10866step2Labels raw10866step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw10867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10867Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10867step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10867step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw10867step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10867step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw10867step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10867step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw10867step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10867step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw10867step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10867step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw10867step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10867 raw10867Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw10867 raw10867Labels = mixedMoment B raw10867step0 raw10867step0Labels := by
      have hz : ∀ j, raw10867 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10867step0 = (fun i j => raw10867 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10867step0 raw10867; decide +kernel
      have hl : raw10867step0Labels = raw10867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10867 raw10867Labels permutation520 hz
    mixedMoment B raw10867step0 raw10867step0Labels = mixedMoment B raw10867step1 raw10867step1Labels := by
      have hz : ∀ j, raw10867step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10867step1 = (fun i j => raw10867step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10867step1 raw10867step0; decide +kernel
      have hl : raw10867step1Labels = raw10867step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10867step0 raw10867step0Labels permutation104 hz
    mixedMoment B raw10867step1 raw10867step1Labels = mixedMoment B raw10867step2 raw10867step2Labels := by
      have hz : ∀ j, raw10867step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10867step2 = (fun i j => raw10867step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10867step2 raw10867step1; decide +kernel
      have hl : raw10867step2Labels = raw10867step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10867step1 raw10867step1Labels permutation20 hz
    mixedMoment B raw10867step2 raw10867step2Labels = mixedMoment B raw10867step3 raw10867step3Labels := by
      have ha : raw10867step3 = (fun i j => raw10867step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10867step3 raw10867step2; decide +kernel
      have hl : raw10867step3Labels = raw10867step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10867step2 raw10867step2Labels permutation3 permutation7
    mixedMoment B raw10867step3 raw10867step3Labels = mixedMoment B raw10867step4 raw10867step4Labels := by
      have ha : raw10867step4 = -raw10867step3 := by apply Matrix.ext; change ∀ i j, raw10867step4 i j = -(raw10867step3 i j); unfold raw10867step4 raw10867step3; decide +kernel
      have hl : raw10867step4Labels = raw10867step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10867step4 raw10867step4Labels = mixedMoment B raw10867step5 raw10867step5Labels := by
      have ha : raw10867step5 = raw10867step4 := by apply Matrix.ext; unfold raw10867step5 raw10867step4; decide +kernel
      have hl : raw10867step4Labels = labelEmbedding1 ∘ raw10867step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10867step4 raw10867step4Labels raw10867step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2293 node2293Labels := by rfl

def raw10868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10868Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10868step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw10868step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10868step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10868step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10868step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10868step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10868step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10868 raw10868Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw10868 raw10868Labels = mixedMoment B raw10868step0 raw10868step0Labels := by
      have hz : ∀ j, raw10868 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10868step0 = (fun i j => raw10868 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10868step0 raw10868; decide +kernel
      have hl : raw10868step0Labels = raw10868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10868 raw10868Labels permutation434 hz
    mixedMoment B raw10868step0 raw10868step0Labels = mixedMoment B raw10868step1 raw10868step1Labels := by
      have hz : ∀ j, raw10868step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10868step1 = (fun i j => raw10868step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10868step1 raw10868step0; decide +kernel
      have hl : raw10868step1Labels = raw10868step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10868step0 raw10868step0Labels permutation80 hz
    mixedMoment B raw10868step1 raw10868step1Labels = mixedMoment B raw10868step2 raw10868step2Labels := by
      have ha : raw10868step2 = (fun i j => raw10868step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10868step2 raw10868step1; decide +kernel
      have hl : raw10868step2Labels = raw10868step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10868step1 raw10868step1Labels permutation11 permutation7
    mixedMoment B raw10868step2 raw10868step2Labels = mixedMoment B raw10868step3 raw10868step3Labels := by
      have ha : raw10868step3 = -raw10868step2 := by apply Matrix.ext; change ∀ i j, raw10868step3 i j = -(raw10868step2 i j); unfold raw10868step3 raw10868step2; decide +kernel
      have hl : raw10868step3Labels = raw10868step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10868step3 raw10868step3Labels = mixedMoment B raw10868step4 raw10868step4Labels := by
      have ha : raw10868step4 = raw10868step3 := by apply Matrix.ext; unfold raw10868step4 raw10868step3; decide +kernel
      have hl : raw10868step3Labels = labelEmbedding1 ∘ raw10868step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10868step3 raw10868step3Labels raw10868step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2265 node2265Labels := by rfl

def raw10869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10869Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10869step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10869step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10869step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10869step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10869step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10869step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10869 raw10869Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw10869 raw10869Labels = mixedMoment B raw10869step0 raw10869step0Labels := by
      have hz : ∀ j, raw10869 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10869step0 = (fun i j => raw10869 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10869step0 raw10869; decide +kernel
      have hl : raw10869step0Labels = raw10869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10869 raw10869Labels permutation434 hz
    mixedMoment B raw10869step0 raw10869step0Labels = mixedMoment B raw10869step1 raw10869step1Labels := by
      have ha : raw10869step1 = (fun i j => raw10869step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10869step1 raw10869step0; decide +kernel
      have hl : raw10869step1Labels = raw10869step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10869step0 raw10869step0Labels permutation41 permutation7
    mixedMoment B raw10869step1 raw10869step1Labels = mixedMoment B raw10869step2 raw10869step2Labels := by
      have ha : raw10869step2 = -raw10869step1 := by apply Matrix.ext; change ∀ i j, raw10869step2 i j = -(raw10869step1 i j); unfold raw10869step2 raw10869step1; decide +kernel
      have hl : raw10869step2Labels = raw10869step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10869step2 raw10869step2Labels = mixedMoment B raw10869step3 raw10869step3Labels := by
      have ha : raw10869step3 = raw10869step2 := by apply Matrix.ext; unfold raw10869step3 raw10869step2; decide +kernel
      have hl : raw10869step2Labels = labelEmbedding1 ∘ raw10869step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10869step2 raw10869step2Labels raw10869step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1709 node1709Labels := by rfl

def raw10870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10870Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10870step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw10870step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10870step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10870step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10870step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10870step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10870 raw10870Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw10870 raw10870Labels = mixedMoment B raw10870step0 raw10870step0Labels := by
      have hz : ∀ j, raw10870 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10870step0 = (fun i j => raw10870 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10870step0 raw10870; decide +kernel
      have hl : raw10870step0Labels = raw10870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10870 raw10870Labels permutation434 hz
    mixedMoment B raw10870step0 raw10870step0Labels = mixedMoment B raw10870step1 raw10870step1Labels := by
      have ha : raw10870step1 = (fun i j => raw10870step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10870step1 raw10870step0; decide +kernel
      have hl : raw10870step1Labels = raw10870step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10870step0 raw10870step0Labels permutation41 permutation7
    mixedMoment B raw10870step1 raw10870step1Labels = mixedMoment B raw10870step2 raw10870step2Labels := by
      have ha : raw10870step2 = -raw10870step1 := by apply Matrix.ext; change ∀ i j, raw10870step2 i j = -(raw10870step1 i j); unfold raw10870step2 raw10870step1; decide +kernel
      have hl : raw10870step2Labels = raw10870step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10870step2 raw10870step2Labels = mixedMoment B raw10870step3 raw10870step3Labels := by
      have ha : raw10870step3 = raw10870step2 := by apply Matrix.ext; unfold raw10870step3 raw10870step2; decide +kernel
      have hl : raw10870step2Labels = labelEmbedding1 ∘ raw10870step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10870step2 raw10870step2Labels raw10870step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2246 node2246Labels := by rfl

def raw10871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10871Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10871step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10871step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10871step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10871 raw10871Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw10871 raw10871Labels = mixedMoment B raw10871step0 raw10871step0Labels := by
      have ha : raw10871step0 = (fun i j => raw10871 (permutation209 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10871step0 raw10871; decide +kernel
      have hl : raw10871step0Labels = raw10871Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10871 raw10871Labels permutation209 permutation7
    mixedMoment B raw10871step0 raw10871step0Labels = mixedMoment B raw10871step1 raw10871step1Labels := by
      have ha : raw10871step1 = -raw10871step0 := by apply Matrix.ext; change ∀ i j, raw10871step1 i j = -(raw10871step0 i j); unfold raw10871step1 raw10871step0; decide +kernel
      have hl : raw10871step1Labels = raw10871step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10871step1 raw10871step1Labels = mixedMoment B raw10871step2 raw10871step2Labels := by
      have ha : raw10871step2 = raw10871step1 := by apply Matrix.ext; unfold raw10871step2 raw10871step1; decide +kernel
      have hl : raw10871step1Labels = labelEmbedding1 ∘ raw10871step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10871step1 raw10871step1Labels raw10871step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2192 node2192Labels := by rfl

def raw10872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10872Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10872step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10872step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10872step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10872step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10872step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10872step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10872step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10872step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10872step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10872 raw10872Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw10872 raw10872Labels = mixedMoment B raw10872step0 raw10872step0Labels := by
      have hz : ∀ j, raw10872 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10872step0 = (fun i j => raw10872 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10872step0 raw10872; decide +kernel
      have hl : raw10872step0Labels = raw10872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10872 raw10872Labels permutation520 hz
    mixedMoment B raw10872step0 raw10872step0Labels = mixedMoment B raw10872step1 raw10872step1Labels := by
      have hz : ∀ j, raw10872step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10872step1 = (fun i j => raw10872step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10872step1 raw10872step0; decide +kernel
      have hl : raw10872step1Labels = raw10872step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10872step0 raw10872step0Labels permutation104 hz
    mixedMoment B raw10872step1 raw10872step1Labels = mixedMoment B raw10872step2 raw10872step2Labels := by
      have ha : raw10872step2 = (fun i j => raw10872step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10872step2 raw10872step1; decide +kernel
      have hl : raw10872step2Labels = raw10872step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10872step1 raw10872step1Labels permutation11 permutation7
    mixedMoment B raw10872step2 raw10872step2Labels = mixedMoment B raw10872step3 raw10872step3Labels := by
      have ha : raw10872step3 = -raw10872step2 := by apply Matrix.ext; change ∀ i j, raw10872step3 i j = -(raw10872step2 i j); unfold raw10872step3 raw10872step2; decide +kernel
      have hl : raw10872step3Labels = raw10872step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10872step3 raw10872step3Labels = mixedMoment B raw10872step4 raw10872step4Labels := by
      have ha : raw10872step4 = raw10872step3 := by apply Matrix.ext; unfold raw10872step4 raw10872step3; decide +kernel
      have hl : raw10872step3Labels = labelEmbedding1 ∘ raw10872step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10872step3 raw10872step3Labels raw10872step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw10873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10873Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10873step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10873step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10873step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10873step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10873step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10873 raw10873Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw10873 raw10873Labels = mixedMoment B raw10873step0 raw10873step0Labels := by
      have hz : ∀ j, raw10873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10873step0 = (fun i j => raw10873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10873step0 raw10873; decide +kernel
      have hl : raw10873step0Labels = raw10873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10873 raw10873Labels permutation434 hz
    mixedMoment B raw10873step0 raw10873step0Labels = mixedMoment B raw10873step1 raw10873step1Labels := by
      have ha : raw10873step1 = (fun i j => raw10873step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10873step1 raw10873step0; decide +kernel
      have hl : raw10873step1Labels = raw10873step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10873step0 raw10873step0Labels permutation41 permutation7
    mixedMoment B raw10873step1 raw10873step1Labels = mixedMoment B raw10873step2 raw10873step2Labels := by
      have ha : raw10873step2 = -raw10873step1 := by apply Matrix.ext; change ∀ i j, raw10873step2 i j = -(raw10873step1 i j); unfold raw10873step2 raw10873step1; decide +kernel
      have hl : raw10873step2Labels = raw10873step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10873step2 raw10873step2Labels = mixedMoment B raw10873step3 raw10873step3Labels := by
      have ha : raw10873step3 = raw10873step2 := by apply Matrix.ext; unfold raw10873step3 raw10873step2; decide +kernel
      have hl : raw10873step2Labels = labelEmbedding1 ∘ raw10873step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10873step2 raw10873step2Labels raw10873step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw10874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10874Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10874step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10874step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10874step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10874step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10874step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10874step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10874 raw10874Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw10874 raw10874Labels = mixedMoment B raw10874step0 raw10874step0Labels := by
      have hz : ∀ j, raw10874 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10874step0 = (fun i j => raw10874 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10874step0 raw10874; decide +kernel
      have hl : raw10874step0Labels = raw10874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10874 raw10874Labels permutation346 hz
    mixedMoment B raw10874step0 raw10874step0Labels = mixedMoment B raw10874step1 raw10874step1Labels := by
      have ha : raw10874step1 = (fun i j => raw10874step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10874step1 raw10874step0; decide +kernel
      have hl : raw10874step1Labels = raw10874step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10874step0 raw10874step0Labels permutation41 permutation7
    mixedMoment B raw10874step1 raw10874step1Labels = mixedMoment B raw10874step2 raw10874step2Labels := by
      have ha : raw10874step2 = -raw10874step1 := by apply Matrix.ext; change ∀ i j, raw10874step2 i j = -(raw10874step1 i j); unfold raw10874step2 raw10874step1; decide +kernel
      have hl : raw10874step2Labels = raw10874step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10874step2 raw10874step2Labels = mixedMoment B raw10874step3 raw10874step3Labels := by
      have ha : raw10874step3 = raw10874step2 := by apply Matrix.ext; unfold raw10874step3 raw10874step2; decide +kernel
      have hl : raw10874step2Labels = labelEmbedding1 ∘ raw10874step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10874step2 raw10874step2Labels raw10874step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1709 node1709Labels := by rfl

def raw10875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10875Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10875step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw10875step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10875step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10875step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10875step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10875step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10875 raw10875Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw10875 raw10875Labels = mixedMoment B raw10875step0 raw10875step0Labels := by
      have hz : ∀ j, raw10875 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10875step0 = (fun i j => raw10875 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10875step0 raw10875; decide +kernel
      have hl : raw10875step0Labels = raw10875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10875 raw10875Labels permutation346 hz
    mixedMoment B raw10875step0 raw10875step0Labels = mixedMoment B raw10875step1 raw10875step1Labels := by
      have ha : raw10875step1 = (fun i j => raw10875step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10875step1 raw10875step0; decide +kernel
      have hl : raw10875step1Labels = raw10875step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10875step0 raw10875step0Labels permutation41 permutation7
    mixedMoment B raw10875step1 raw10875step1Labels = mixedMoment B raw10875step2 raw10875step2Labels := by
      have ha : raw10875step2 = -raw10875step1 := by apply Matrix.ext; change ∀ i j, raw10875step2 i j = -(raw10875step1 i j); unfold raw10875step2 raw10875step1; decide +kernel
      have hl : raw10875step2Labels = raw10875step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10875step2 raw10875step2Labels = mixedMoment B raw10875step3 raw10875step3Labels := by
      have ha : raw10875step3 = raw10875step2 := by apply Matrix.ext; unfold raw10875step3 raw10875step2; decide +kernel
      have hl : raw10875step2Labels = labelEmbedding1 ∘ raw10875step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10875step2 raw10875step2Labels raw10875step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2246 node2246Labels := by rfl

def raw10876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10876Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10876step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10876step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10876step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10876step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10876step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10876 raw10876Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw10876 raw10876Labels = mixedMoment B raw10876step0 raw10876step0Labels := by
      have ha : raw10876step0 = (fun i j => raw10876 (permutation185 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10876step0 raw10876; decide +kernel
      have hl : raw10876step0Labels = raw10876Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10876 raw10876Labels permutation185 permutation7
    mixedMoment B raw10876step0 raw10876step0Labels = mixedMoment B raw10876step1 raw10876step1Labels := by
      have ha : raw10876step1 = -raw10876step0 := by apply Matrix.ext; change ∀ i j, raw10876step1 i j = -(raw10876step0 i j); unfold raw10876step1 raw10876step0; decide +kernel
      have hl : raw10876step1Labels = raw10876step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10876step1 raw10876step1Labels = mixedMoment B raw10876step2 raw10876step2Labels := by
      have ha : raw10876step2 = raw10876step1 := by apply Matrix.ext; unfold raw10876step2 raw10876step1; decide +kernel
      have hl : raw10876step1Labels = labelEmbedding1 ∘ raw10876step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10876step1 raw10876step1Labels raw10876step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2192 node2192Labels := by rfl

def raw10877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10877Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10877step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10877step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10877step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10877step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10877step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10877step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10877step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10877step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10877step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10877 raw10877Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw10877 raw10877Labels = mixedMoment B raw10877step0 raw10877step0Labels := by
      have hz : ∀ j, raw10877 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10877step0 = (fun i j => raw10877 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10877step0 raw10877; decide +kernel
      have hl : raw10877step0Labels = raw10877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10877 raw10877Labels permutation520 hz
    mixedMoment B raw10877step0 raw10877step0Labels = mixedMoment B raw10877step1 raw10877step1Labels := by
      have hz : ∀ j, raw10877step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10877step1 = (fun i j => raw10877step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10877step1 raw10877step0; decide +kernel
      have hl : raw10877step1Labels = raw10877step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10877step0 raw10877step0Labels permutation80 hz
    mixedMoment B raw10877step1 raw10877step1Labels = mixedMoment B raw10877step2 raw10877step2Labels := by
      have ha : raw10877step2 = (fun i j => raw10877step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10877step2 raw10877step1; decide +kernel
      have hl : raw10877step2Labels = raw10877step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10877step1 raw10877step1Labels permutation11 permutation7
    mixedMoment B raw10877step2 raw10877step2Labels = mixedMoment B raw10877step3 raw10877step3Labels := by
      have ha : raw10877step3 = -raw10877step2 := by apply Matrix.ext; change ∀ i j, raw10877step3 i j = -(raw10877step2 i j); unfold raw10877step3 raw10877step2; decide +kernel
      have hl : raw10877step3Labels = raw10877step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10877step3 raw10877step3Labels = mixedMoment B raw10877step4 raw10877step4Labels := by
      have ha : raw10877step4 = raw10877step3 := by apply Matrix.ext; unfold raw10877step4 raw10877step3; decide +kernel
      have hl : raw10877step3Labels = labelEmbedding1 ∘ raw10877step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10877step3 raw10877step3Labels raw10877step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw10878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10878Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10878step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10878step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10878step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10878step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10878step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10878 raw10878Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw10878 raw10878Labels = mixedMoment B raw10878step0 raw10878step0Labels := by
      have hz : ∀ j, raw10878 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10878step0 = (fun i j => raw10878 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10878step0 raw10878; decide +kernel
      have hl : raw10878step0Labels = raw10878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10878 raw10878Labels permutation346 hz
    mixedMoment B raw10878step0 raw10878step0Labels = mixedMoment B raw10878step1 raw10878step1Labels := by
      have ha : raw10878step1 = (fun i j => raw10878step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10878step1 raw10878step0; decide +kernel
      have hl : raw10878step1Labels = raw10878step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10878step0 raw10878step0Labels permutation41 permutation7
    mixedMoment B raw10878step1 raw10878step1Labels = mixedMoment B raw10878step2 raw10878step2Labels := by
      have ha : raw10878step2 = -raw10878step1 := by apply Matrix.ext; change ∀ i j, raw10878step2 i j = -(raw10878step1 i j); unfold raw10878step2 raw10878step1; decide +kernel
      have hl : raw10878step2Labels = raw10878step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10878step2 raw10878step2Labels = mixedMoment B raw10878step3 raw10878step3Labels := by
      have ha : raw10878step3 = raw10878step2 := by apply Matrix.ext; unfold raw10878step3 raw10878step2; decide +kernel
      have hl : raw10878step2Labels = labelEmbedding1 ∘ raw10878step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10878step2 raw10878step2Labels raw10878step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw10879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10879Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10879step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10879step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw10879step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10879step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10879step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10879step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10879step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10879 raw10879Labels = mixedMoment B node1740 node1740Labels := by
  calc
    mixedMoment B raw10879 raw10879Labels = mixedMoment B raw10879step0 raw10879step0Labels := by
      have hz : ∀ j, raw10879 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10879step0 = (fun i j => raw10879 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10879step0 raw10879; decide +kernel
      have hl : raw10879step0Labels = raw10879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10879 raw10879Labels permutation434 hz
    mixedMoment B raw10879step0 raw10879step0Labels = mixedMoment B raw10879step1 raw10879step1Labels := by
      have hz : ∀ j, raw10879step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10879step1 = (fun i j => raw10879step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10879step1 raw10879step0; decide +kernel
      have hl : raw10879step1Labels = raw10879step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10879step0 raw10879step0Labels permutation80 hz
    mixedMoment B raw10879step1 raw10879step1Labels = mixedMoment B raw10879step2 raw10879step2Labels := by
      have ha : raw10879step2 = (fun i j => raw10879step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10879step2 raw10879step1; decide +kernel
      have hl : raw10879step2Labels = raw10879step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10879step1 raw10879step1Labels permutation11 permutation7
    mixedMoment B raw10879step2 raw10879step2Labels = mixedMoment B raw10879step3 raw10879step3Labels := by
      have ha : raw10879step3 = -raw10879step2 := by apply Matrix.ext; change ∀ i j, raw10879step3 i j = -(raw10879step2 i j); unfold raw10879step3 raw10879step2; decide +kernel
      have hl : raw10879step3Labels = raw10879step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10879step3 raw10879step3Labels = mixedMoment B raw10879step4 raw10879step4Labels := by
      have ha : raw10879step4 = raw10879step3 := by apply Matrix.ext; unfold raw10879step4 raw10879step3; decide +kernel
      have hl : raw10879step3Labels = labelEmbedding1 ∘ raw10879step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10879step3 raw10879step3Labels raw10879step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1740 node1740Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
