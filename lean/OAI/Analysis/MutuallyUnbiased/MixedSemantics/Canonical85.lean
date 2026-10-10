import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
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

def raw10880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10880Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10880step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10880step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10880step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, -1, 2], ![-2, 3, -1]]
def raw10880step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10880step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw10880step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10880step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw10880step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10880 raw10880Labels = mixedMoment B node2280 node2280Labels := by
  calc
    mixedMoment B raw10880 raw10880Labels = mixedMoment B raw10880step0 raw10880step0Labels := by
      have hz : ∀ j, raw10880 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10880step0 = (fun i j => raw10880 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10880step0 raw10880; decide +kernel
      have hl : raw10880step0Labels = raw10880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10880 raw10880Labels permutation434 hz
    mixedMoment B raw10880step0 raw10880step0Labels = mixedMoment B raw10880step1 raw10880step1Labels := by
      have hz : ∀ j, raw10880step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10880step1 = (fun i j => raw10880step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10880step1 raw10880step0; decide +kernel
      have hl : raw10880step1Labels = raw10880step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10880step0 raw10880step0Labels permutation80 hz
    mixedMoment B raw10880step1 raw10880step1Labels = mixedMoment B raw10880step2 raw10880step2Labels := by
      have ha : raw10880step2 = (fun i j => raw10880step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10880step2 raw10880step1; decide +kernel
      have hl : raw10880step2Labels = raw10880step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10880step1 raw10880step1Labels permutation11 permutation7
    mixedMoment B raw10880step2 raw10880step2Labels = mixedMoment B raw10880step3 raw10880step3Labels := by
      have ha : raw10880step3 = -raw10880step2 := by apply Matrix.ext; change ∀ i j, raw10880step3 i j = -(raw10880step2 i j); unfold raw10880step3 raw10880step2; decide +kernel
      have hl : raw10880step3Labels = raw10880step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10880step3 raw10880step3Labels = mixedMoment B raw10880step4 raw10880step4Labels := by
      have ha : raw10880step4 = raw10880step3 := by apply Matrix.ext; unfold raw10880step4 raw10880step3; decide +kernel
      have hl : raw10880step3Labels = labelEmbedding1 ∘ raw10880step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10880step3 raw10880step3Labels raw10880step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2280 node2280Labels := by rfl

def raw10881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10881Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10881step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw10881step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10881step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10881step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10881step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10881step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10881 raw10881Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw10881 raw10881Labels = mixedMoment B raw10881step0 raw10881step0Labels := by
      have hz : ∀ j, raw10881 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10881step0 = (fun i j => raw10881 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10881step0 raw10881; decide +kernel
      have hl : raw10881step0Labels = raw10881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10881 raw10881Labels permutation434 hz
    mixedMoment B raw10881step0 raw10881step0Labels = mixedMoment B raw10881step1 raw10881step1Labels := by
      have ha : raw10881step1 = (fun i j => raw10881step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10881step1 raw10881step0; decide +kernel
      have hl : raw10881step1Labels = raw10881step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10881step0 raw10881step0Labels permutation41 permutation7
    mixedMoment B raw10881step1 raw10881step1Labels = mixedMoment B raw10881step2 raw10881step2Labels := by
      have ha : raw10881step2 = -raw10881step1 := by apply Matrix.ext; change ∀ i j, raw10881step2 i j = -(raw10881step1 i j); unfold raw10881step2 raw10881step1; decide +kernel
      have hl : raw10881step2Labels = raw10881step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10881step2 raw10881step2Labels = mixedMoment B raw10881step3 raw10881step3Labels := by
      have ha : raw10881step3 = raw10881step2 := by apply Matrix.ext; unfold raw10881step3 raw10881step2; decide +kernel
      have hl : raw10881step2Labels = labelEmbedding1 ∘ raw10881step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10881step2 raw10881step2Labels raw10881step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2217 node2217Labels := by rfl

def raw10882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10882Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10882step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw10882step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10882step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10882step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw10882step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10882 raw10882Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw10882 raw10882Labels = mixedMoment B raw10882step0 raw10882step0Labels := by
      have hz : ∀ j, raw10882 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10882step0 = (fun i j => raw10882 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10882step0 raw10882; decide +kernel
      have hl : raw10882step0Labels = raw10882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10882 raw10882Labels permutation346 hz
    mixedMoment B raw10882step0 raw10882step0Labels = mixedMoment B raw10882step1 raw10882step1Labels := by
      have ha : raw10882step1 = (fun i j => raw10882step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10882step1 raw10882step0; decide +kernel
      have hl : raw10882step1Labels = raw10882step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10882step0 raw10882step0Labels permutation41 permutation7
    mixedMoment B raw10882step1 raw10882step1Labels = mixedMoment B raw10882step2 raw10882step2Labels := by
      have ha : raw10882step2 = -raw10882step1 := by apply Matrix.ext; change ∀ i j, raw10882step2 i j = -(raw10882step1 i j); unfold raw10882step2 raw10882step1; decide +kernel
      have hl : raw10882step2Labels = raw10882step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10882step2 raw10882step2Labels = mixedMoment B raw10882step3 raw10882step3Labels := by
      have ha : raw10882step3 = raw10882step2 := by apply Matrix.ext; unfold raw10882step3 raw10882step2; decide +kernel
      have hl : raw10882step2Labels = labelEmbedding1 ∘ raw10882step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10882step2 raw10882step2Labels raw10882step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2217 node2217Labels := by rfl

def raw10883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw10883Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw10883step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw10883step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10883step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw10883step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10883step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10883step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10883step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10883step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10883 raw10883Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw10883 raw10883Labels = mixedMoment B raw10883step0 raw10883step0Labels := by
      have hz : ∀ j, raw10883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10883step0 = (fun i j => raw10883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10883step0 raw10883; decide +kernel
      have hl : raw10883step0Labels = raw10883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10883 raw10883Labels permutation434 hz
    mixedMoment B raw10883step0 raw10883step0Labels = mixedMoment B raw10883step1 raw10883step1Labels := by
      have hz : ∀ j, raw10883step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10883step1 = (fun i j => raw10883step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10883step1 raw10883step0; decide +kernel
      have hl : raw10883step1Labels = raw10883step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10883step0 raw10883step0Labels permutation80 hz
    mixedMoment B raw10883step1 raw10883step1Labels = mixedMoment B raw10883step2 raw10883step2Labels := by
      have ha : raw10883step2 = (fun i j => raw10883step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10883step2 raw10883step1; decide +kernel
      have hl : raw10883step2Labels = raw10883step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10883step1 raw10883step1Labels permutation11 permutation7
    mixedMoment B raw10883step2 raw10883step2Labels = mixedMoment B raw10883step3 raw10883step3Labels := by
      have ha : raw10883step3 = -raw10883step2 := by apply Matrix.ext; change ∀ i j, raw10883step3 i j = -(raw10883step2 i j); unfold raw10883step3 raw10883step2; decide +kernel
      have hl : raw10883step3Labels = raw10883step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10883step3 raw10883step3Labels = mixedMoment B raw10883step4 raw10883step4Labels := by
      have ha : raw10883step4 = raw10883step3 := by apply Matrix.ext; unfold raw10883step4 raw10883step3; decide +kernel
      have hl : raw10883step3Labels = labelEmbedding1 ∘ raw10883step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10883step3 raw10883step3Labels raw10883step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw10884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10884Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10884step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10884step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw10884step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10884step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw10884step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10884step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw10884step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10884step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw10884step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10884 raw10884Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw10884 raw10884Labels = mixedMoment B raw10884step0 raw10884step0Labels := by
      have hz : ∀ j, raw10884 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10884step0 = (fun i j => raw10884 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10884step0 raw10884; decide +kernel
      have hl : raw10884step0Labels = raw10884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10884 raw10884Labels permutation434 hz
    mixedMoment B raw10884step0 raw10884step0Labels = mixedMoment B raw10884step1 raw10884step1Labels := by
      have hz : ∀ j, raw10884step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10884step1 = (fun i j => raw10884step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10884step1 raw10884step0; decide +kernel
      have hl : raw10884step1Labels = raw10884step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10884step0 raw10884step0Labels permutation80 hz
    mixedMoment B raw10884step1 raw10884step1Labels = mixedMoment B raw10884step2 raw10884step2Labels := by
      have ha : raw10884step2 = (fun i j => raw10884step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10884step2 raw10884step1; decide +kernel
      have hl : raw10884step2Labels = raw10884step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10884step1 raw10884step1Labels permutation11 permutation7
    mixedMoment B raw10884step2 raw10884step2Labels = mixedMoment B raw10884step3 raw10884step3Labels := by
      have ha : raw10884step3 = -raw10884step2 := by apply Matrix.ext; change ∀ i j, raw10884step3 i j = -(raw10884step2 i j); unfold raw10884step3 raw10884step2; decide +kernel
      have hl : raw10884step3Labels = raw10884step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10884step3 raw10884step3Labels = mixedMoment B raw10884step4 raw10884step4Labels := by
      have ha : raw10884step4 = raw10884step3 := by apply Matrix.ext; unfold raw10884step4 raw10884step3; decide +kernel
      have hl : raw10884step3Labels = labelEmbedding1 ∘ raw10884step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10884step3 raw10884step3Labels raw10884step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

def raw10885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10885Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10885step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10885step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw10885step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10885step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -2, 3], ![-2, 3, -1]]
def raw10885step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10885step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw10885step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10885step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw10885step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10885 raw10885Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw10885 raw10885Labels = mixedMoment B raw10885step0 raw10885step0Labels := by
      have hz : ∀ j, raw10885 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10885step0 = (fun i j => raw10885 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10885step0 raw10885; decide +kernel
      have hl : raw10885step0Labels = raw10885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10885 raw10885Labels permutation434 hz
    mixedMoment B raw10885step0 raw10885step0Labels = mixedMoment B raw10885step1 raw10885step1Labels := by
      have hz : ∀ j, raw10885step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10885step1 = (fun i j => raw10885step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10885step1 raw10885step0; decide +kernel
      have hl : raw10885step1Labels = raw10885step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10885step0 raw10885step0Labels permutation80 hz
    mixedMoment B raw10885step1 raw10885step1Labels = mixedMoment B raw10885step2 raw10885step2Labels := by
      have ha : raw10885step2 = (fun i j => raw10885step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10885step2 raw10885step1; decide +kernel
      have hl : raw10885step2Labels = raw10885step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10885step1 raw10885step1Labels permutation11 permutation7
    mixedMoment B raw10885step2 raw10885step2Labels = mixedMoment B raw10885step3 raw10885step3Labels := by
      have ha : raw10885step3 = -raw10885step2 := by apply Matrix.ext; change ∀ i j, raw10885step3 i j = -(raw10885step2 i j); unfold raw10885step3 raw10885step2; decide +kernel
      have hl : raw10885step3Labels = raw10885step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10885step3 raw10885step3Labels = mixedMoment B raw10885step4 raw10885step4Labels := by
      have ha : raw10885step4 = raw10885step3 := by apply Matrix.ext; unfold raw10885step4 raw10885step3; decide +kernel
      have hl : raw10885step3Labels = labelEmbedding1 ∘ raw10885step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10885step3 raw10885step3Labels raw10885step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2267 node2267Labels := by rfl

def raw10886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10886Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10886step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw10886step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10886step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw10886step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10886step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw10886step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10886 raw10886Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw10886 raw10886Labels = mixedMoment B raw10886step0 raw10886step0Labels := by
      have hz : ∀ j, raw10886 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10886step0 = (fun i j => raw10886 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10886step0 raw10886; decide +kernel
      have hl : raw10886step0Labels = raw10886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10886 raw10886Labels permutation434 hz
    mixedMoment B raw10886step0 raw10886step0Labels = mixedMoment B raw10886step1 raw10886step1Labels := by
      have ha : raw10886step1 = (fun i j => raw10886step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10886step1 raw10886step0; decide +kernel
      have hl : raw10886step1Labels = raw10886step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10886step0 raw10886step0Labels permutation41 permutation7
    mixedMoment B raw10886step1 raw10886step1Labels = mixedMoment B raw10886step2 raw10886step2Labels := by
      have ha : raw10886step2 = -raw10886step1 := by apply Matrix.ext; change ∀ i j, raw10886step2 i j = -(raw10886step1 i j); unfold raw10886step2 raw10886step1; decide +kernel
      have hl : raw10886step2Labels = raw10886step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10886step2 raw10886step2Labels = mixedMoment B raw10886step3 raw10886step3Labels := by
      have ha : raw10886step3 = raw10886step2 := by apply Matrix.ext; unfold raw10886step3 raw10886step2; decide +kernel
      have hl : raw10886step2Labels = labelEmbedding1 ∘ raw10886step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10886step2 raw10886step2Labels raw10886step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw10887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10887Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10887step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw10887step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw10887step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10887step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw10887step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10887 raw10887Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw10887 raw10887Labels = mixedMoment B raw10887step0 raw10887step0Labels := by
      have hz : ∀ j, raw10887 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10887step0 = (fun i j => raw10887 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10887step0 raw10887; decide +kernel
      have hl : raw10887step0Labels = raw10887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10887 raw10887Labels permutation346 hz
    mixedMoment B raw10887step0 raw10887step0Labels = mixedMoment B raw10887step1 raw10887step1Labels := by
      have ha : raw10887step1 = (fun i j => raw10887step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10887step1 raw10887step0; decide +kernel
      have hl : raw10887step1Labels = raw10887step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10887step0 raw10887step0Labels permutation41 permutation7
    mixedMoment B raw10887step1 raw10887step1Labels = mixedMoment B raw10887step2 raw10887step2Labels := by
      have ha : raw10887step2 = -raw10887step1 := by apply Matrix.ext; change ∀ i j, raw10887step2 i j = -(raw10887step1 i j); unfold raw10887step2 raw10887step1; decide +kernel
      have hl : raw10887step2Labels = raw10887step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10887step2 raw10887step2Labels = mixedMoment B raw10887step3 raw10887step3Labels := by
      have ha : raw10887step3 = raw10887step2 := by apply Matrix.ext; unfold raw10887step3 raw10887step2; decide +kernel
      have hl : raw10887step2Labels = labelEmbedding1 ∘ raw10887step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10887step2 raw10887step2Labels raw10887step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw10888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw10888Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw10888step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw10888step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10888step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw10888step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10888step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]
def raw10888step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10888step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw10888step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10888step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw10888step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10888 raw10888Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw10888 raw10888Labels = mixedMoment B raw10888step0 raw10888step0Labels := by
      have hz : ∀ j, raw10888 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10888step0 = (fun i j => raw10888 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10888step0 raw10888; decide +kernel
      have hl : raw10888step0Labels = raw10888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10888 raw10888Labels permutation520 hz
    mixedMoment B raw10888step0 raw10888step0Labels = mixedMoment B raw10888step1 raw10888step1Labels := by
      have hz : ∀ j, raw10888step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10888step1 = (fun i j => raw10888step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10888step1 raw10888step0; decide +kernel
      have hl : raw10888step1Labels = raw10888step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10888step0 raw10888step0Labels permutation104 hz
    mixedMoment B raw10888step1 raw10888step1Labels = mixedMoment B raw10888step2 raw10888step2Labels := by
      have hz : ∀ j, raw10888step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10888step2 = (fun i j => raw10888step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10888step2 raw10888step1; decide +kernel
      have hl : raw10888step2Labels = raw10888step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10888step1 raw10888step1Labels permutation20 hz
    mixedMoment B raw10888step2 raw10888step2Labels = mixedMoment B raw10888step3 raw10888step3Labels := by
      have ha : raw10888step3 = (fun i j => raw10888step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10888step3 raw10888step2; decide +kernel
      have hl : raw10888step3Labels = raw10888step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10888step2 raw10888step2Labels permutation3 permutation7
    mixedMoment B raw10888step3 raw10888step3Labels = mixedMoment B raw10888step4 raw10888step4Labels := by
      have ha : raw10888step4 = -raw10888step3 := by apply Matrix.ext; change ∀ i j, raw10888step4 i j = -(raw10888step3 i j); unfold raw10888step4 raw10888step3; decide +kernel
      have hl : raw10888step4Labels = raw10888step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10888step4 raw10888step4Labels = mixedMoment B raw10888step5 raw10888step5Labels := by
      have ha : raw10888step5 = raw10888step4 := by apply Matrix.ext; unfold raw10888step5 raw10888step4; decide +kernel
      have hl : raw10888step4Labels = labelEmbedding1 ∘ raw10888step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10888step4 raw10888step4Labels raw10888step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2294 node2294Labels := by rfl

def raw10889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10889step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10889 raw10889Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw10889 raw10889Labels = mixedMoment B raw10889step0 raw10889step0Labels := by
      have hz : ∀ j, raw10889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10889step0 = (fun i j => raw10889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10889step0 raw10889; decide +kernel
      have hl : raw10889step0Labels = raw10889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10889 raw10889Labels permutation434 hz
    mixedMoment B raw10889step0 raw10889step0Labels = mixedMoment B raw10889step1 raw10889step1Labels := by
      have hz : ∀ j, raw10889step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10889step1 = (fun i j => raw10889step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10889step1 raw10889step0; decide +kernel
      have hl : raw10889step1Labels = raw10889step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10889step0 raw10889step0Labels permutation80 hz
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw10890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10890step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10890 raw10890Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw10890 raw10890Labels = mixedMoment B raw10890step0 raw10890step0Labels := by
      have hz : ∀ j, raw10890 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10890step0 = (fun i j => raw10890 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10890step0 raw10890; decide +kernel
      have hl : raw10890step0Labels = raw10890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10890 raw10890Labels permutation434 hz
    mixedMoment B raw10890step0 raw10890step0Labels = mixedMoment B raw10890step1 raw10890step1Labels := by
      have hz : ∀ j, raw10890step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10890step1 = (fun i j => raw10890step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10890step1 raw10890step0; decide +kernel
      have hl : raw10890step1Labels = raw10890step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10890step0 raw10890step0Labels permutation80 hz
    mixedMoment B raw10890step1 raw10890step1Labels = mixedMoment B raw10890step2 raw10890step2Labels := by
      have ha : raw10890step2 = (fun i j => raw10890step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10890step2 raw10890step1; decide +kernel
      have hl : raw10890step2Labels = raw10890step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10890step1 raw10890step1Labels permutation10 permutation2
    _ = mixedMoment B node1083 node1083Labels := by rfl

def raw10891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10891 raw10891Labels = mixedMoment B node1057 node1057Labels := by
  calc
    mixedMoment B raw10891 raw10891Labels = mixedMoment B raw10891step0 raw10891step0Labels := by
      have hz : ∀ j, raw10891 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10891step0 = (fun i j => raw10891 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10891step0 raw10891; decide +kernel
      have hl : raw10891step0Labels = raw10891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10891 raw10891Labels permutation434 hz
    _ = mixedMoment B node1057 node1057Labels := by rfl

def raw10892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10892 raw10892Labels = mixedMoment B node1057 node1057Labels := by
  calc
    mixedMoment B raw10892 raw10892Labels = mixedMoment B raw10892step0 raw10892step0Labels := by
      have hz : ∀ j, raw10892 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10892step0 = (fun i j => raw10892 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10892step0 raw10892; decide +kernel
      have hl : raw10892step0Labels = raw10892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10892 raw10892Labels permutation346 hz
    _ = mixedMoment B node1057 node1057Labels := by rfl

def raw10893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw10893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw10893step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10893 raw10893Labels = mixedMoment B node1063 node1063Labels := by
  calc
    mixedMoment B raw10893 raw10893Labels = mixedMoment B raw10893step0 raw10893step0Labels := by
      have hz : ∀ j, raw10893 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10893step0 = (fun i j => raw10893 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10893step0 raw10893; decide +kernel
      have hl : raw10893step0Labels = raw10893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10893 raw10893Labels permutation434 hz
    mixedMoment B raw10893step0 raw10893step0Labels = mixedMoment B raw10893step1 raw10893step1Labels := by
      have hz : ∀ j, raw10893step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10893step1 = (fun i j => raw10893step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10893step1 raw10893step0; decide +kernel
      have hl : raw10893step1Labels = raw10893step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10893step0 raw10893step0Labels permutation80 hz
    _ = mixedMoment B node1063 node1063Labels := by rfl

def raw10894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw10894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw10894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10894 raw10894Labels = mixedMoment B node1059 node1059Labels := by
  calc
    mixedMoment B raw10894 raw10894Labels = mixedMoment B raw10894step0 raw10894step0Labels := by
      have hz : ∀ j, raw10894 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10894step0 = (fun i j => raw10894 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10894step0 raw10894; decide +kernel
      have hl : raw10894step0Labels = raw10894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10894 raw10894Labels permutation434 hz
    mixedMoment B raw10894step0 raw10894step0Labels = mixedMoment B raw10894step1 raw10894step1Labels := by
      have hz : ∀ j, raw10894step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10894step1 = (fun i j => raw10894step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10894step1 raw10894step0; decide +kernel
      have hl : raw10894step1Labels = raw10894step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10894step0 raw10894step0Labels permutation80 hz
    _ = mixedMoment B node1059 node1059Labels := by rfl

def raw10895 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![0, 0], ![0, 0], ![1, -1]]
def raw10895Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10895step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![0, 0], ![1, -1]]
def raw10895step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10895step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![1, -1]]
def raw10895step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10895step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw10895step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10895step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw10895step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical10895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10895 raw10895Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw10895 raw10895Labels = mixedMoment B raw10895step0 raw10895step0Labels := by
      have hz : ∀ j, raw10895 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10895step0 = (fun i j => raw10895 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10895step0 raw10895; decide +kernel
      have hl : raw10895step0Labels = raw10895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10895 raw10895Labels permutation520 hz
    mixedMoment B raw10895step0 raw10895step0Labels = mixedMoment B raw10895step1 raw10895step1Labels := by
      have hz : ∀ j, raw10895step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10895step1 = (fun i j => raw10895step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10895step1 raw10895step0; decide +kernel
      have hl : raw10895step1Labels = raw10895step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10895step0 raw10895step0Labels permutation104 hz
    mixedMoment B raw10895step1 raw10895step1Labels = mixedMoment B raw10895step2 raw10895step2Labels := by
      have hz : ∀ j, raw10895step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10895step2 = (fun i j => raw10895step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10895step2 raw10895step1; decide +kernel
      have hl : raw10895step2Labels = raw10895step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10895step1 raw10895step1Labels permutation20 hz
    mixedMoment B raw10895step2 raw10895step2Labels = mixedMoment B raw10895step3 raw10895step3Labels := by
      have ha : raw10895step3 = (fun i j => raw10895step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw10895step3 raw10895step2; decide +kernel
      have hl : raw10895step3Labels = raw10895step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10895step2 raw10895step2Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw10896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10896step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10896 raw10896Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw10896 raw10896Labels = mixedMoment B raw10896step0 raw10896step0Labels := by
      have hz : ∀ j, raw10896 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10896step0 = (fun i j => raw10896 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10896step0 raw10896; decide +kernel
      have hl : raw10896step0Labels = raw10896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10896 raw10896Labels permutation434 hz
    mixedMoment B raw10896step0 raw10896step0Labels = mixedMoment B raw10896step1 raw10896step1Labels := by
      have ha : raw10896step1 = (fun i j => raw10896step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10896step1 raw10896step0; decide +kernel
      have hl : raw10896step1Labels = raw10896step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10896step0 raw10896step0Labels permutation40 permutation2
    _ = mixedMoment B node2054 node2054Labels := by rfl

def raw10897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw10897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10897step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10897 raw10897Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw10897 raw10897Labels = mixedMoment B raw10897step0 raw10897step0Labels := by
      have hz : ∀ j, raw10897 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10897step0 = (fun i j => raw10897 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10897step0 raw10897; decide +kernel
      have hl : raw10897step0Labels = raw10897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10897 raw10897Labels permutation346 hz
    mixedMoment B raw10897step0 raw10897step0Labels = mixedMoment B raw10897step1 raw10897step1Labels := by
      have ha : raw10897step1 = (fun i j => raw10897step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10897step1 raw10897step0; decide +kernel
      have hl : raw10897step1Labels = raw10897step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10897step0 raw10897step0Labels permutation40 permutation2
    _ = mixedMoment B node2054 node2054Labels := by rfl

def raw10898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw10898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw10898step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10898step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw10898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10898 raw10898Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw10898 raw10898Labels = mixedMoment B raw10898step0 raw10898step0Labels := by
      have hz : ∀ j, raw10898 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10898step0 = (fun i j => raw10898 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10898step0 raw10898; decide +kernel
      have hl : raw10898step0Labels = raw10898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10898 raw10898Labels permutation520 hz
    mixedMoment B raw10898step0 raw10898step0Labels = mixedMoment B raw10898step1 raw10898step1Labels := by
      have hz : ∀ j, raw10898step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10898step1 = (fun i j => raw10898step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10898step1 raw10898step0; decide +kernel
      have hl : raw10898step1Labels = raw10898step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10898step0 raw10898step0Labels permutation104 hz
    mixedMoment B raw10898step1 raw10898step1Labels = mixedMoment B raw10898step2 raw10898step2Labels := by
      have hz : ∀ j, raw10898step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10898step2 = (fun i j => raw10898step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10898step2 raw10898step1; decide +kernel
      have hl : raw10898step2Labels = raw10898step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10898step1 raw10898step1Labels permutation20 hz
    _ = mixedMoment B node2293 node2293Labels := by rfl

def raw10899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw10899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10899step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10899step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10899 raw10899Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw10899 raw10899Labels = mixedMoment B raw10899step0 raw10899step0Labels := by
      have hz : ∀ j, raw10899 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10899step0 = (fun i j => raw10899 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10899step0 raw10899; decide +kernel
      have hl : raw10899step0Labels = raw10899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10899 raw10899Labels permutation434 hz
    mixedMoment B raw10899step0 raw10899step0Labels = mixedMoment B raw10899step1 raw10899step1Labels := by
      have hz : ∀ j, raw10899step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10899step1 = (fun i j => raw10899step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10899step1 raw10899step0; decide +kernel
      have hl : raw10899step1Labels = raw10899step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10899step0 raw10899step0Labels permutation80 hz
    mixedMoment B raw10899step1 raw10899step1Labels = mixedMoment B raw10899step2 raw10899step2Labels := by
      have ha : raw10899step2 = (fun i j => raw10899step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10899step2 raw10899step1; decide +kernel
      have hl : raw10899step2Labels = raw10899step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10899step1 raw10899step1Labels permutation11 permutation2
    _ = mixedMoment B node2291 node2291Labels := by rfl

def raw10900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw10900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10900step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10900step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10900step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10900 raw10900Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw10900 raw10900Labels = mixedMoment B raw10900step0 raw10900step0Labels := by
      have hz : ∀ j, raw10900 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10900step0 = (fun i j => raw10900 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10900step0 raw10900; decide +kernel
      have hl : raw10900step0Labels = raw10900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10900 raw10900Labels permutation434 hz
    mixedMoment B raw10900step0 raw10900step0Labels = mixedMoment B raw10900step1 raw10900step1Labels := by
      have hz : ∀ j, raw10900step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10900step1 = (fun i j => raw10900step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10900step1 raw10900step0; decide +kernel
      have hl : raw10900step1Labels = raw10900step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10900step0 raw10900step0Labels permutation80 hz
    mixedMoment B raw10900step1 raw10900step1Labels = mixedMoment B raw10900step2 raw10900step2Labels := by
      have ha : raw10900step2 = (fun i j => raw10900step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10900step2 raw10900step1; decide +kernel
      have hl : raw10900step2Labels = raw10900step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10900step1 raw10900step1Labels permutation8 permutation3
    mixedMoment B raw10900step2 raw10900step2Labels = mixedMoment B raw10900step3 raw10900step3Labels := by
      have ha : raw10900step3 = raw10900step2 := by apply Matrix.ext; unfold raw10900step3 raw10900step2; decide +kernel
      have hl : raw10900step2Labels = labelEmbedding6 ∘ raw10900step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10900step2 raw10900step2Labels raw10900step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw10901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10901step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10901step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10901step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10901step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10901step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10901 raw10901Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw10901 raw10901Labels = mixedMoment B raw10901step0 raw10901step0Labels := by
      have hz : ∀ j, raw10901 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10901step0 = (fun i j => raw10901 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10901step0 raw10901; decide +kernel
      have hl : raw10901step0Labels = raw10901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10901 raw10901Labels permutation434 hz
    mixedMoment B raw10901step0 raw10901step0Labels = mixedMoment B raw10901step1 raw10901step1Labels := by
      have ha : raw10901step1 = (fun i j => raw10901step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10901step1 raw10901step0; decide +kernel
      have hl : raw10901step1Labels = raw10901step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10901step0 raw10901step0Labels permutation41 permutation5
    mixedMoment B raw10901step1 raw10901step1Labels = mixedMoment B raw10901step2 raw10901step2Labels := by
      have ha : raw10901step2 = -raw10901step1 := by apply Matrix.ext; change ∀ i j, raw10901step2 i j = -(raw10901step1 i j); unfold raw10901step2 raw10901step1; decide +kernel
      have hl : raw10901step2Labels = raw10901step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10901step2 raw10901step2Labels = mixedMoment B raw10901step3 raw10901step3Labels := by
      have ha : raw10901step3 = raw10901step2 := by apply Matrix.ext; unfold raw10901step3 raw10901step2; decide +kernel
      have hl : raw10901step2Labels = labelEmbedding8 ∘ raw10901step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10901step2 raw10901step2Labels raw10901step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw10902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10902step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10902step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10902step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10902step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10902 raw10902Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw10902 raw10902Labels = mixedMoment B raw10902step0 raw10902step0Labels := by
      have hz : ∀ j, raw10902 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10902step0 = (fun i j => raw10902 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10902step0 raw10902; decide +kernel
      have hl : raw10902step0Labels = raw10902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10902 raw10902Labels permutation346 hz
    mixedMoment B raw10902step0 raw10902step0Labels = mixedMoment B raw10902step1 raw10902step1Labels := by
      have ha : raw10902step1 = (fun i j => raw10902step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10902step1 raw10902step0; decide +kernel
      have hl : raw10902step1Labels = raw10902step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10902step0 raw10902step0Labels permutation41 permutation5
    mixedMoment B raw10902step1 raw10902step1Labels = mixedMoment B raw10902step2 raw10902step2Labels := by
      have ha : raw10902step2 = -raw10902step1 := by apply Matrix.ext; change ∀ i j, raw10902step2 i j = -(raw10902step1 i j); unfold raw10902step2 raw10902step1; decide +kernel
      have hl : raw10902step2Labels = raw10902step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10902step2 raw10902step2Labels = mixedMoment B raw10902step3 raw10902step3Labels := by
      have ha : raw10902step3 = raw10902step2 := by apply Matrix.ext; unfold raw10902step3 raw10902step2; decide +kernel
      have hl : raw10902step2Labels = labelEmbedding8 ∘ raw10902step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10902step2 raw10902step2Labels raw10902step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw10903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw10903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10903step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw10903step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10903step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10903step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10903step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10903step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10903 raw10903Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw10903 raw10903Labels = mixedMoment B raw10903step0 raw10903step0Labels := by
      have hz : ∀ j, raw10903 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10903step0 = (fun i j => raw10903 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10903step0 raw10903; decide +kernel
      have hl : raw10903step0Labels = raw10903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10903 raw10903Labels permutation434 hz
    mixedMoment B raw10903step0 raw10903step0Labels = mixedMoment B raw10903step1 raw10903step1Labels := by
      have hz : ∀ j, raw10903step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10903step1 = (fun i j => raw10903step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10903step1 raw10903step0; decide +kernel
      have hl : raw10903step1Labels = raw10903step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10903step0 raw10903step0Labels permutation80 hz
    mixedMoment B raw10903step1 raw10903step1Labels = mixedMoment B raw10903step2 raw10903step2Labels := by
      have ha : raw10903step2 = (fun i j => raw10903step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10903step2 raw10903step1; decide +kernel
      have hl : raw10903step2Labels = raw10903step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10903step1 raw10903step1Labels permutation11 permutation5
    mixedMoment B raw10903step2 raw10903step2Labels = mixedMoment B raw10903step3 raw10903step3Labels := by
      have ha : raw10903step3 = -raw10903step2 := by apply Matrix.ext; change ∀ i j, raw10903step3 i j = -(raw10903step2 i j); unfold raw10903step3 raw10903step2; decide +kernel
      have hl : raw10903step3Labels = raw10903step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10903step3 raw10903step3Labels = mixedMoment B raw10903step4 raw10903step4Labels := by
      have ha : raw10903step4 = raw10903step3 := by apply Matrix.ext; unfold raw10903step4 raw10903step3; decide +kernel
      have hl : raw10903step3Labels = labelEmbedding8 ∘ raw10903step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10903step3 raw10903step3Labels raw10903step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw10904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw10904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10904step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10904step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10904step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10904step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10904 raw10904Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw10904 raw10904Labels = mixedMoment B raw10904step0 raw10904step0Labels := by
      have hz : ∀ j, raw10904 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10904step0 = (fun i j => raw10904 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10904step0 raw10904; decide +kernel
      have hl : raw10904step0Labels = raw10904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10904 raw10904Labels permutation434 hz
    mixedMoment B raw10904step0 raw10904step0Labels = mixedMoment B raw10904step1 raw10904step1Labels := by
      have hz : ∀ j, raw10904step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10904step1 = (fun i j => raw10904step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10904step1 raw10904step0; decide +kernel
      have hl : raw10904step1Labels = raw10904step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10904step0 raw10904step0Labels permutation80 hz
    mixedMoment B raw10904step1 raw10904step1Labels = mixedMoment B raw10904step2 raw10904step2Labels := by
      have ha : raw10904step2 = (fun i j => raw10904step1 (permutation17 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10904step2 raw10904step1; decide +kernel
      have hl : raw10904step2Labels = raw10904step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10904step1 raw10904step1Labels permutation17 permutation4
    mixedMoment B raw10904step2 raw10904step2Labels = mixedMoment B raw10904step3 raw10904step3Labels := by
      have ha : raw10904step3 = raw10904step2 := by apply Matrix.ext; unfold raw10904step3 raw10904step2; decide +kernel
      have hl : raw10904step2Labels = labelEmbedding7 ∘ raw10904step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10904step2 raw10904step2Labels raw10904step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw10905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10905step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw10905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10905step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw10905step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10905step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw10905step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10905step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw10905step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10905 raw10905Labels = mixedMoment B node4270 node4270Labels := by
  calc
    mixedMoment B raw10905 raw10905Labels = mixedMoment B raw10905step0 raw10905step0Labels := by
      have hz : ∀ j, raw10905 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10905step0 = (fun i j => raw10905 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10905step0 raw10905; decide +kernel
      have hl : raw10905step0Labels = raw10905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10905 raw10905Labels permutation434 hz
    mixedMoment B raw10905step0 raw10905step0Labels = mixedMoment B raw10905step1 raw10905step1Labels := by
      have hz : ∀ j, raw10905step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10905step1 = (fun i j => raw10905step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10905step1 raw10905step0; decide +kernel
      have hl : raw10905step1Labels = raw10905step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10905step0 raw10905step0Labels permutation80 hz
    mixedMoment B raw10905step1 raw10905step1Labels = mixedMoment B raw10905step2 raw10905step2Labels := by
      have ha : raw10905step2 = (fun i j => raw10905step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10905step2 raw10905step1; decide +kernel
      have hl : raw10905step2Labels = raw10905step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10905step1 raw10905step1Labels permutation11 permutation5
    mixedMoment B raw10905step2 raw10905step2Labels = mixedMoment B raw10905step3 raw10905step3Labels := by
      have ha : raw10905step3 = -raw10905step2 := by apply Matrix.ext; change ∀ i j, raw10905step3 i j = -(raw10905step2 i j); unfold raw10905step3 raw10905step2; decide +kernel
      have hl : raw10905step3Labels = raw10905step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10905step3 raw10905step3Labels = mixedMoment B raw10905step4 raw10905step4Labels := by
      have ha : raw10905step4 = raw10905step3 := by apply Matrix.ext; unfold raw10905step4 raw10905step3; decide +kernel
      have hl : raw10905step3Labels = labelEmbedding8 ∘ raw10905step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10905step3 raw10905step3Labels raw10905step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4270 node4270Labels := by rfl

def raw10906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw10906step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10906step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw10906step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10906step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw10906step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10906 raw10906Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw10906 raw10906Labels = mixedMoment B raw10906step0 raw10906step0Labels := by
      have hz : ∀ j, raw10906 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10906step0 = (fun i j => raw10906 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10906step0 raw10906; decide +kernel
      have hl : raw10906step0Labels = raw10906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10906 raw10906Labels permutation434 hz
    mixedMoment B raw10906step0 raw10906step0Labels = mixedMoment B raw10906step1 raw10906step1Labels := by
      have ha : raw10906step1 = (fun i j => raw10906step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10906step1 raw10906step0; decide +kernel
      have hl : raw10906step1Labels = raw10906step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10906step0 raw10906step0Labels permutation41 permutation5
    mixedMoment B raw10906step1 raw10906step1Labels = mixedMoment B raw10906step2 raw10906step2Labels := by
      have ha : raw10906step2 = -raw10906step1 := by apply Matrix.ext; change ∀ i j, raw10906step2 i j = -(raw10906step1 i j); unfold raw10906step2 raw10906step1; decide +kernel
      have hl : raw10906step2Labels = raw10906step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10906step2 raw10906step2Labels = mixedMoment B raw10906step3 raw10906step3Labels := by
      have ha : raw10906step3 = raw10906step2 := by apply Matrix.ext; unfold raw10906step3 raw10906step2; decide +kernel
      have hl : raw10906step2Labels = labelEmbedding8 ∘ raw10906step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10906step2 raw10906step2Labels raw10906step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

def raw10907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10907step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw10907step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw10907step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10907step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw10907step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10907 raw10907Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw10907 raw10907Labels = mixedMoment B raw10907step0 raw10907step0Labels := by
      have hz : ∀ j, raw10907 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10907step0 = (fun i j => raw10907 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10907step0 raw10907; decide +kernel
      have hl : raw10907step0Labels = raw10907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10907 raw10907Labels permutation346 hz
    mixedMoment B raw10907step0 raw10907step0Labels = mixedMoment B raw10907step1 raw10907step1Labels := by
      have ha : raw10907step1 = (fun i j => raw10907step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10907step1 raw10907step0; decide +kernel
      have hl : raw10907step1Labels = raw10907step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10907step0 raw10907step0Labels permutation41 permutation5
    mixedMoment B raw10907step1 raw10907step1Labels = mixedMoment B raw10907step2 raw10907step2Labels := by
      have ha : raw10907step2 = -raw10907step1 := by apply Matrix.ext; change ∀ i j, raw10907step2 i j = -(raw10907step1 i j); unfold raw10907step2 raw10907step1; decide +kernel
      have hl : raw10907step2Labels = raw10907step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10907step2 raw10907step2Labels = mixedMoment B raw10907step3 raw10907step3Labels := by
      have ha : raw10907step3 = raw10907step2 := by apply Matrix.ext; unfold raw10907step3 raw10907step2; decide +kernel
      have hl : raw10907step2Labels = labelEmbedding8 ∘ raw10907step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10907step2 raw10907step2Labels raw10907step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

def raw10908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 1, -1], ![2, -1, -1]]
def raw10908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10908step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw10908step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10908step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw10908step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10908step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw10908step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10908 raw10908Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw10908 raw10908Labels = mixedMoment B raw10908step0 raw10908step0Labels := by
      have hz : ∀ j, raw10908 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10908step0 = (fun i j => raw10908 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10908step0 raw10908; decide +kernel
      have hl : raw10908step0Labels = raw10908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10908 raw10908Labels permutation434 hz
    mixedMoment B raw10908step0 raw10908step0Labels = mixedMoment B raw10908step1 raw10908step1Labels := by
      have hz : ∀ j, raw10908step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10908step1 = (fun i j => raw10908step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10908step1 raw10908step0; decide +kernel
      have hl : raw10908step1Labels = raw10908step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10908step0 raw10908step0Labels permutation80 hz
    mixedMoment B raw10908step1 raw10908step1Labels = mixedMoment B raw10908step2 raw10908step2Labels := by
      have ha : raw10908step2 = (fun i j => raw10908step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10908step2 raw10908step1; decide +kernel
      have hl : raw10908step2Labels = raw10908step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10908step1 raw10908step1Labels permutation11 permutation5
    mixedMoment B raw10908step2 raw10908step2Labels = mixedMoment B raw10908step3 raw10908step3Labels := by
      have ha : raw10908step3 = -raw10908step2 := by apply Matrix.ext; change ∀ i j, raw10908step3 i j = -(raw10908step2 i j); unfold raw10908step3 raw10908step2; decide +kernel
      have hl : raw10908step3Labels = raw10908step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10908step3 raw10908step3Labels = mixedMoment B raw10908step4 raw10908step4Labels := by
      have ha : raw10908step4 = raw10908step3 := by apply Matrix.ext; unfold raw10908step4 raw10908step3; decide +kernel
      have hl : raw10908step3Labels = labelEmbedding8 ∘ raw10908step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10908step3 raw10908step3Labels raw10908step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw10909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10909step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw10909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10909step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw10909step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10909step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw10909step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10909step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw10909step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10909 raw10909Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw10909 raw10909Labels = mixedMoment B raw10909step0 raw10909step0Labels := by
      have hz : ∀ j, raw10909 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10909step0 = (fun i j => raw10909 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10909step0 raw10909; decide +kernel
      have hl : raw10909step0Labels = raw10909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10909 raw10909Labels permutation434 hz
    mixedMoment B raw10909step0 raw10909step0Labels = mixedMoment B raw10909step1 raw10909step1Labels := by
      have hz : ∀ j, raw10909step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10909step1 = (fun i j => raw10909step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10909step1 raw10909step0; decide +kernel
      have hl : raw10909step1Labels = raw10909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10909step0 raw10909step0Labels permutation80 hz
    mixedMoment B raw10909step1 raw10909step1Labels = mixedMoment B raw10909step2 raw10909step2Labels := by
      have ha : raw10909step2 = (fun i j => raw10909step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10909step2 raw10909step1; decide +kernel
      have hl : raw10909step2Labels = raw10909step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10909step1 raw10909step1Labels permutation11 permutation5
    mixedMoment B raw10909step2 raw10909step2Labels = mixedMoment B raw10909step3 raw10909step3Labels := by
      have ha : raw10909step3 = -raw10909step2 := by apply Matrix.ext; change ∀ i j, raw10909step3 i j = -(raw10909step2 i j); unfold raw10909step3 raw10909step2; decide +kernel
      have hl : raw10909step3Labels = raw10909step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10909step3 raw10909step3Labels = mixedMoment B raw10909step4 raw10909step4Labels := by
      have ha : raw10909step4 = raw10909step3 := by apply Matrix.ext; unfold raw10909step4 raw10909step3; decide +kernel
      have hl : raw10909step3Labels = labelEmbedding8 ∘ raw10909step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10909step3 raw10909step3Labels raw10909step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw10910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10910step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10910step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10910step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10910step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10910step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10910 raw10910Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw10910 raw10910Labels = mixedMoment B raw10910step0 raw10910step0Labels := by
      have hz : ∀ j, raw10910 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10910step0 = (fun i j => raw10910 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10910step0 raw10910; decide +kernel
      have hl : raw10910step0Labels = raw10910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10910 raw10910Labels permutation434 hz
    mixedMoment B raw10910step0 raw10910step0Labels = mixedMoment B raw10910step1 raw10910step1Labels := by
      have ha : raw10910step1 = (fun i j => raw10910step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10910step1 raw10910step0; decide +kernel
      have hl : raw10910step1Labels = raw10910step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10910step0 raw10910step0Labels permutation47 permutation5
    mixedMoment B raw10910step1 raw10910step1Labels = mixedMoment B raw10910step2 raw10910step2Labels := by
      have ha : raw10910step2 = -raw10910step1 := by apply Matrix.ext; change ∀ i j, raw10910step2 i j = -(raw10910step1 i j); unfold raw10910step2 raw10910step1; decide +kernel
      have hl : raw10910step2Labels = raw10910step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10910step2 raw10910step2Labels = mixedMoment B raw10910step3 raw10910step3Labels := by
      have ha : raw10910step3 = raw10910step2 := by apply Matrix.ext; unfold raw10910step3 raw10910step2; decide +kernel
      have hl : raw10910step2Labels = labelEmbedding8 ∘ raw10910step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10910step2 raw10910step2Labels raw10910step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

def raw10911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10911step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10911step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10911step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10911step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10911 raw10911Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw10911 raw10911Labels = mixedMoment B raw10911step0 raw10911step0Labels := by
      have hz : ∀ j, raw10911 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10911step0 = (fun i j => raw10911 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10911step0 raw10911; decide +kernel
      have hl : raw10911step0Labels = raw10911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10911 raw10911Labels permutation434 hz
    mixedMoment B raw10911step0 raw10911step0Labels = mixedMoment B raw10911step1 raw10911step1Labels := by
      have ha : raw10911step1 = (fun i j => raw10911step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10911step1 raw10911step0; decide +kernel
      have hl : raw10911step1Labels = raw10911step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10911step0 raw10911step0Labels permutation34 permutation3
    mixedMoment B raw10911step1 raw10911step1Labels = mixedMoment B raw10911step2 raw10911step2Labels := by
      have ha : raw10911step2 = raw10911step1 := by apply Matrix.ext; unfold raw10911step2 raw10911step1; decide +kernel
      have hl : raw10911step1Labels = labelEmbedding6 ∘ raw10911step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10911step1 raw10911step1Labels raw10911step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw10912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10912step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10912step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10912step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10912step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10912 raw10912Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw10912 raw10912Labels = mixedMoment B raw10912step0 raw10912step0Labels := by
      have ha : raw10912step0 = (fun i j => raw10912 (permutation215 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10912step0 raw10912; decide +kernel
      have hl : raw10912step0Labels = raw10912Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10912 raw10912Labels permutation215 permutation5
    mixedMoment B raw10912step0 raw10912step0Labels = mixedMoment B raw10912step1 raw10912step1Labels := by
      have ha : raw10912step1 = -raw10912step0 := by apply Matrix.ext; change ∀ i j, raw10912step1 i j = -(raw10912step0 i j); unfold raw10912step1 raw10912step0; decide +kernel
      have hl : raw10912step1Labels = raw10912step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10912step1 raw10912step1Labels = mixedMoment B raw10912step2 raw10912step2Labels := by
      have ha : raw10912step2 = raw10912step1 := by apply Matrix.ext; unfold raw10912step2 raw10912step1; decide +kernel
      have hl : raw10912step1Labels = labelEmbedding8 ∘ raw10912step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10912step1 raw10912step1Labels raw10912step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

def raw10913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10913step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10913step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10913step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10913step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10913step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10913step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10913 raw10913Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw10913 raw10913Labels = mixedMoment B raw10913step0 raw10913step0Labels := by
      have hz : ∀ j, raw10913 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10913step0 = (fun i j => raw10913 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10913step0 raw10913; decide +kernel
      have hl : raw10913step0Labels = raw10913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10913 raw10913Labels permutation434 hz
    mixedMoment B raw10913step0 raw10913step0Labels = mixedMoment B raw10913step1 raw10913step1Labels := by
      have ha : raw10913step1 = (fun i j => raw10913step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10913step1 raw10913step0; decide +kernel
      have hl : raw10913step1Labels = raw10913step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10913step0 raw10913step0Labels permutation47 permutation5
    mixedMoment B raw10913step1 raw10913step1Labels = mixedMoment B raw10913step2 raw10913step2Labels := by
      have ha : raw10913step2 = -raw10913step1 := by apply Matrix.ext; change ∀ i j, raw10913step2 i j = -(raw10913step1 i j); unfold raw10913step2 raw10913step1; decide +kernel
      have hl : raw10913step2Labels = raw10913step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10913step2 raw10913step2Labels = mixedMoment B raw10913step3 raw10913step3Labels := by
      have ha : raw10913step3 = raw10913step2 := by apply Matrix.ext; unfold raw10913step3 raw10913step2; decide +kernel
      have hl : raw10913step2Labels = labelEmbedding8 ∘ raw10913step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10913step2 raw10913step2Labels raw10913step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw10914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10914step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10914step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10914step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10914step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10914step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10914step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10914 raw10914Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw10914 raw10914Labels = mixedMoment B raw10914step0 raw10914step0Labels := by
      have hz : ∀ j, raw10914 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10914step0 = (fun i j => raw10914 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10914step0 raw10914; decide +kernel
      have hl : raw10914step0Labels = raw10914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10914 raw10914Labels permutation434 hz
    mixedMoment B raw10914step0 raw10914step0Labels = mixedMoment B raw10914step1 raw10914step1Labels := by
      have ha : raw10914step1 = (fun i j => raw10914step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10914step1 raw10914step0; decide +kernel
      have hl : raw10914step1Labels = raw10914step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10914step0 raw10914step0Labels permutation49 permutation5
    mixedMoment B raw10914step1 raw10914step1Labels = mixedMoment B raw10914step2 raw10914step2Labels := by
      have ha : raw10914step2 = -raw10914step1 := by apply Matrix.ext; change ∀ i j, raw10914step2 i j = -(raw10914step1 i j); unfold raw10914step2 raw10914step1; decide +kernel
      have hl : raw10914step2Labels = raw10914step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10914step2 raw10914step2Labels = mixedMoment B raw10914step3 raw10914step3Labels := by
      have ha : raw10914step3 = raw10914step2 := by apply Matrix.ext; unfold raw10914step3 raw10914step2; decide +kernel
      have hl : raw10914step2Labels = labelEmbedding8 ∘ raw10914step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10914step2 raw10914step2Labels raw10914step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw10915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10915Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10915step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10915step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10915step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10915step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10915step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10915 raw10915Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw10915 raw10915Labels = mixedMoment B raw10915step0 raw10915step0Labels := by
      have hz : ∀ j, raw10915 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10915step0 = (fun i j => raw10915 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10915step0 raw10915; decide +kernel
      have hl : raw10915step0Labels = raw10915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10915 raw10915Labels permutation346 hz
    mixedMoment B raw10915step0 raw10915step0Labels = mixedMoment B raw10915step1 raw10915step1Labels := by
      have ha : raw10915step1 = (fun i j => raw10915step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10915step1 raw10915step0; decide +kernel
      have hl : raw10915step1Labels = raw10915step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10915step0 raw10915step0Labels permutation47 permutation5
    mixedMoment B raw10915step1 raw10915step1Labels = mixedMoment B raw10915step2 raw10915step2Labels := by
      have ha : raw10915step2 = -raw10915step1 := by apply Matrix.ext; change ∀ i j, raw10915step2 i j = -(raw10915step1 i j); unfold raw10915step2 raw10915step1; decide +kernel
      have hl : raw10915step2Labels = raw10915step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10915step2 raw10915step2Labels = mixedMoment B raw10915step3 raw10915step3Labels := by
      have ha : raw10915step3 = raw10915step2 := by apply Matrix.ext; unfold raw10915step3 raw10915step2; decide +kernel
      have hl : raw10915step2Labels = labelEmbedding8 ∘ raw10915step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10915step2 raw10915step2Labels raw10915step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

def raw10916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10916Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10916step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10916step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10916step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10916step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10916 raw10916Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw10916 raw10916Labels = mixedMoment B raw10916step0 raw10916step0Labels := by
      have hz : ∀ j, raw10916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10916step0 = (fun i j => raw10916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10916step0 raw10916; decide +kernel
      have hl : raw10916step0Labels = raw10916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10916 raw10916Labels permutation346 hz
    mixedMoment B raw10916step0 raw10916step0Labels = mixedMoment B raw10916step1 raw10916step1Labels := by
      have ha : raw10916step1 = (fun i j => raw10916step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10916step1 raw10916step0; decide +kernel
      have hl : raw10916step1Labels = raw10916step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10916step0 raw10916step0Labels permutation34 permutation3
    mixedMoment B raw10916step1 raw10916step1Labels = mixedMoment B raw10916step2 raw10916step2Labels := by
      have ha : raw10916step2 = raw10916step1 := by apply Matrix.ext; unfold raw10916step2 raw10916step1; decide +kernel
      have hl : raw10916step1Labels = labelEmbedding6 ∘ raw10916step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10916step1 raw10916step1Labels raw10916step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw10917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10917Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10917step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10917step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10917step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10917step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10917 raw10917Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw10917 raw10917Labels = mixedMoment B raw10917step0 raw10917step0Labels := by
      have ha : raw10917step0 = (fun i j => raw10917 (permutation191 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10917step0 raw10917; decide +kernel
      have hl : raw10917step0Labels = raw10917Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10917 raw10917Labels permutation191 permutation5
    mixedMoment B raw10917step0 raw10917step0Labels = mixedMoment B raw10917step1 raw10917step1Labels := by
      have ha : raw10917step1 = -raw10917step0 := by apply Matrix.ext; change ∀ i j, raw10917step1 i j = -(raw10917step0 i j); unfold raw10917step1 raw10917step0; decide +kernel
      have hl : raw10917step1Labels = raw10917step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10917step1 raw10917step1Labels = mixedMoment B raw10917step2 raw10917step2Labels := by
      have ha : raw10917step2 = raw10917step1 := by apply Matrix.ext; unfold raw10917step2 raw10917step1; decide +kernel
      have hl : raw10917step1Labels = labelEmbedding8 ∘ raw10917step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10917step1 raw10917step1Labels raw10917step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

def raw10918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10918step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10918step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10918step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10918step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10918step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10918step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10918 raw10918Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw10918 raw10918Labels = mixedMoment B raw10918step0 raw10918step0Labels := by
      have hz : ∀ j, raw10918 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10918step0 = (fun i j => raw10918 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10918step0 raw10918; decide +kernel
      have hl : raw10918step0Labels = raw10918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10918 raw10918Labels permutation346 hz
    mixedMoment B raw10918step0 raw10918step0Labels = mixedMoment B raw10918step1 raw10918step1Labels := by
      have ha : raw10918step1 = (fun i j => raw10918step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10918step1 raw10918step0; decide +kernel
      have hl : raw10918step1Labels = raw10918step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10918step0 raw10918step0Labels permutation47 permutation5
    mixedMoment B raw10918step1 raw10918step1Labels = mixedMoment B raw10918step2 raw10918step2Labels := by
      have ha : raw10918step2 = -raw10918step1 := by apply Matrix.ext; change ∀ i j, raw10918step2 i j = -(raw10918step1 i j); unfold raw10918step2 raw10918step1; decide +kernel
      have hl : raw10918step2Labels = raw10918step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10918step2 raw10918step2Labels = mixedMoment B raw10918step3 raw10918step3Labels := by
      have ha : raw10918step3 = raw10918step2 := by apply Matrix.ext; unfold raw10918step3 raw10918step2; decide +kernel
      have hl : raw10918step2Labels = labelEmbedding8 ∘ raw10918step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10918step2 raw10918step2Labels raw10918step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw10919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10919step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10919step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10919step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10919step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10919step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10919 raw10919Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw10919 raw10919Labels = mixedMoment B raw10919step0 raw10919step0Labels := by
      have hz : ∀ j, raw10919 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10919step0 = (fun i j => raw10919 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10919step0 raw10919; decide +kernel
      have hl : raw10919step0Labels = raw10919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10919 raw10919Labels permutation346 hz
    mixedMoment B raw10919step0 raw10919step0Labels = mixedMoment B raw10919step1 raw10919step1Labels := by
      have ha : raw10919step1 = (fun i j => raw10919step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10919step1 raw10919step0; decide +kernel
      have hl : raw10919step1Labels = raw10919step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10919step0 raw10919step0Labels permutation49 permutation5
    mixedMoment B raw10919step1 raw10919step1Labels = mixedMoment B raw10919step2 raw10919step2Labels := by
      have ha : raw10919step2 = -raw10919step1 := by apply Matrix.ext; change ∀ i j, raw10919step2 i j = -(raw10919step1 i j); unfold raw10919step2 raw10919step1; decide +kernel
      have hl : raw10919step2Labels = raw10919step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10919step2 raw10919step2Labels = mixedMoment B raw10919step3 raw10919step3Labels := by
      have ha : raw10919step3 = raw10919step2 := by apply Matrix.ext; unfold raw10919step3 raw10919step2; decide +kernel
      have hl : raw10919step2Labels = labelEmbedding8 ∘ raw10919step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10919step2 raw10919step2Labels raw10919step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw10920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10920step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw10920step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw10920step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10920step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw10920step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10920 raw10920Labels = mixedMoment B node4279 node4279Labels := by
  calc
    mixedMoment B raw10920 raw10920Labels = mixedMoment B raw10920step0 raw10920step0Labels := by
      have hz : ∀ j, raw10920 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10920step0 = (fun i j => raw10920 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10920step0 raw10920; decide +kernel
      have hl : raw10920step0Labels = raw10920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10920 raw10920Labels permutation434 hz
    mixedMoment B raw10920step0 raw10920step0Labels = mixedMoment B raw10920step1 raw10920step1Labels := by
      have hz : ∀ j, raw10920step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10920step1 = (fun i j => raw10920step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10920step1 raw10920step0; decide +kernel
      have hl : raw10920step1Labels = raw10920step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10920step0 raw10920step0Labels permutation80 hz
    mixedMoment B raw10920step1 raw10920step1Labels = mixedMoment B raw10920step2 raw10920step2Labels := by
      have ha : raw10920step2 = (fun i j => raw10920step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10920step2 raw10920step1; decide +kernel
      have hl : raw10920step2Labels = raw10920step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10920step1 raw10920step1Labels permutation8 permutation3
    mixedMoment B raw10920step2 raw10920step2Labels = mixedMoment B raw10920step3 raw10920step3Labels := by
      have ha : raw10920step3 = raw10920step2 := by apply Matrix.ext; unfold raw10920step3 raw10920step2; decide +kernel
      have hl : raw10920step2Labels = labelEmbedding6 ∘ raw10920step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10920step2 raw10920step2Labels raw10920step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4279 node4279Labels := by rfl

def raw10921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10921step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw10921step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10921step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw10921step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10921step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw10921step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10921 raw10921Labels = mixedMoment B node4875 node4875Labels := by
  calc
    mixedMoment B raw10921 raw10921Labels = mixedMoment B raw10921step0 raw10921step0Labels := by
      have hz : ∀ j, raw10921 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10921step0 = (fun i j => raw10921 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10921step0 raw10921; decide +kernel
      have hl : raw10921step0Labels = raw10921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10921 raw10921Labels permutation434 hz
    mixedMoment B raw10921step0 raw10921step0Labels = mixedMoment B raw10921step1 raw10921step1Labels := by
      have hz : ∀ j, raw10921step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10921step1 = (fun i j => raw10921step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10921step1 raw10921step0; decide +kernel
      have hl : raw10921step1Labels = raw10921step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10921step0 raw10921step0Labels permutation80 hz
    mixedMoment B raw10921step1 raw10921step1Labels = mixedMoment B raw10921step2 raw10921step2Labels := by
      have ha : raw10921step2 = (fun i j => raw10921step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10921step2 raw10921step1; decide +kernel
      have hl : raw10921step2Labels = raw10921step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10921step1 raw10921step1Labels permutation8 permutation3
    mixedMoment B raw10921step2 raw10921step2Labels = mixedMoment B raw10921step3 raw10921step3Labels := by
      have ha : raw10921step3 = raw10921step2 := by apply Matrix.ext; unfold raw10921step3 raw10921step2; decide +kernel
      have hl : raw10921step2Labels = labelEmbedding6 ∘ raw10921step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10921step2 raw10921step2Labels raw10921step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4875 node4875Labels := by rfl

def raw10922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10922step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw10922step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10922step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw10922step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10922 raw10922Labels = mixedMoment B node4750 node4750Labels := by
  calc
    mixedMoment B raw10922 raw10922Labels = mixedMoment B raw10922step0 raw10922step0Labels := by
      have hz : ∀ j, raw10922 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10922step0 = (fun i j => raw10922 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10922step0 raw10922; decide +kernel
      have hl : raw10922step0Labels = raw10922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10922 raw10922Labels permutation434 hz
    mixedMoment B raw10922step0 raw10922step0Labels = mixedMoment B raw10922step1 raw10922step1Labels := by
      have ha : raw10922step1 = (fun i j => raw10922step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10922step1 raw10922step0; decide +kernel
      have hl : raw10922step1Labels = raw10922step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10922step0 raw10922step0Labels permutation38 permutation3
    mixedMoment B raw10922step1 raw10922step1Labels = mixedMoment B raw10922step2 raw10922step2Labels := by
      have ha : raw10922step2 = raw10922step1 := by apply Matrix.ext; unfold raw10922step2 raw10922step1; decide +kernel
      have hl : raw10922step1Labels = labelEmbedding6 ∘ raw10922step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10922step1 raw10922step1Labels raw10922step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4750 node4750Labels := by rfl

def raw10923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw10923step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw10923step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10923 raw10923Labels = mixedMoment B node4750 node4750Labels := by
  calc
    mixedMoment B raw10923 raw10923Labels = mixedMoment B raw10923step0 raw10923step0Labels := by
      have hz : ∀ j, raw10923 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10923step0 = (fun i j => raw10923 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10923step0 raw10923; decide +kernel
      have hl : raw10923step0Labels = raw10923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10923 raw10923Labels permutation346 hz
    mixedMoment B raw10923step0 raw10923step0Labels = mixedMoment B raw10923step1 raw10923step1Labels := by
      have ha : raw10923step1 = (fun i j => raw10923step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10923step1 raw10923step0; decide +kernel
      have hl : raw10923step1Labels = raw10923step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10923step0 raw10923step0Labels permutation38 permutation3
    mixedMoment B raw10923step1 raw10923step1Labels = mixedMoment B raw10923step2 raw10923step2Labels := by
      have ha : raw10923step2 = raw10923step1 := by apply Matrix.ext; unfold raw10923step2 raw10923step1; decide +kernel
      have hl : raw10923step1Labels = labelEmbedding6 ∘ raw10923step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10923step1 raw10923step1Labels raw10923step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4750 node4750Labels := by rfl

def raw10924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw10924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw10924step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10924step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw10924step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10924step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10924step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10924step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10924step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10924step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10924step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10924 raw10924Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw10924 raw10924Labels = mixedMoment B raw10924step0 raw10924step0Labels := by
      have hz : ∀ j, raw10924 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10924step0 = (fun i j => raw10924 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10924step0 raw10924; decide +kernel
      have hl : raw10924step0Labels = raw10924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10924 raw10924Labels permutation434 hz
    mixedMoment B raw10924step0 raw10924step0Labels = mixedMoment B raw10924step1 raw10924step1Labels := by
      have hz : ∀ j, raw10924step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10924step1 = (fun i j => raw10924step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10924step1 raw10924step0; decide +kernel
      have hl : raw10924step1Labels = raw10924step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10924step0 raw10924step0Labels permutation80 hz
    mixedMoment B raw10924step1 raw10924step1Labels = mixedMoment B raw10924step2 raw10924step2Labels := by
      have ha : raw10924step2 = (fun i j => raw10924step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10924step2 raw10924step1; decide +kernel
      have hl : raw10924step2Labels = raw10924step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10924step1 raw10924step1Labels permutation13 permutation5
    mixedMoment B raw10924step2 raw10924step2Labels = mixedMoment B raw10924step3 raw10924step3Labels := by
      have ha : raw10924step3 = -raw10924step2 := by apply Matrix.ext; change ∀ i j, raw10924step3 i j = -(raw10924step2 i j); unfold raw10924step3 raw10924step2; decide +kernel
      have hl : raw10924step3Labels = raw10924step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10924step3 raw10924step3Labels = mixedMoment B raw10924step4 raw10924step4Labels := by
      have ha : raw10924step4 = raw10924step3 := by apply Matrix.ext; unfold raw10924step4 raw10924step3; decide +kernel
      have hl : raw10924step3Labels = labelEmbedding8 ∘ raw10924step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10924step3 raw10924step3Labels raw10924step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw10925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10925step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw10925step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10925step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw10925step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10925step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw10925step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10925step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw10925step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10925 raw10925Labels = mixedMoment B node4272 node4272Labels := by
  calc
    mixedMoment B raw10925 raw10925Labels = mixedMoment B raw10925step0 raw10925step0Labels := by
      have hz : ∀ j, raw10925 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10925step0 = (fun i j => raw10925 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10925step0 raw10925; decide +kernel
      have hl : raw10925step0Labels = raw10925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10925 raw10925Labels permutation434 hz
    mixedMoment B raw10925step0 raw10925step0Labels = mixedMoment B raw10925step1 raw10925step1Labels := by
      have hz : ∀ j, raw10925step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10925step1 = (fun i j => raw10925step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10925step1 raw10925step0; decide +kernel
      have hl : raw10925step1Labels = raw10925step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10925step0 raw10925step0Labels permutation80 hz
    mixedMoment B raw10925step1 raw10925step1Labels = mixedMoment B raw10925step2 raw10925step2Labels := by
      have ha : raw10925step2 = (fun i j => raw10925step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10925step2 raw10925step1; decide +kernel
      have hl : raw10925step2Labels = raw10925step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10925step1 raw10925step1Labels permutation10 permutation5
    mixedMoment B raw10925step2 raw10925step2Labels = mixedMoment B raw10925step3 raw10925step3Labels := by
      have ha : raw10925step3 = -raw10925step2 := by apply Matrix.ext; change ∀ i j, raw10925step3 i j = -(raw10925step2 i j); unfold raw10925step3 raw10925step2; decide +kernel
      have hl : raw10925step3Labels = raw10925step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10925step3 raw10925step3Labels = mixedMoment B raw10925step4 raw10925step4Labels := by
      have ha : raw10925step4 = raw10925step3 := by apply Matrix.ext; unfold raw10925step4 raw10925step3; decide +kernel
      have hl : raw10925step3Labels = labelEmbedding8 ∘ raw10925step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10925step3 raw10925step3Labels raw10925step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4272 node4272Labels := by rfl

def raw10926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -2, -1]]
def raw10926step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10926step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10926step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10926step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10926step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10926 raw10926Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw10926 raw10926Labels = mixedMoment B raw10926step0 raw10926step0Labels := by
      have hz : ∀ j, raw10926 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10926step0 = (fun i j => raw10926 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10926step0 raw10926; decide +kernel
      have hl : raw10926step0Labels = raw10926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10926 raw10926Labels permutation434 hz
    mixedMoment B raw10926step0 raw10926step0Labels = mixedMoment B raw10926step1 raw10926step1Labels := by
      have hz : ∀ j, raw10926step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10926step1 = (fun i j => raw10926step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10926step1 raw10926step0; decide +kernel
      have hl : raw10926step1Labels = raw10926step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10926step0 raw10926step0Labels permutation80 hz
    mixedMoment B raw10926step1 raw10926step1Labels = mixedMoment B raw10926step2 raw10926step2Labels := by
      have ha : raw10926step2 = (fun i j => raw10926step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10926step2 raw10926step1; decide +kernel
      have hl : raw10926step2Labels = raw10926step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10926step1 raw10926step1Labels permutation8 permutation3
    mixedMoment B raw10926step2 raw10926step2Labels = mixedMoment B raw10926step3 raw10926step3Labels := by
      have ha : raw10926step3 = raw10926step2 := by apply Matrix.ext; unfold raw10926step3 raw10926step2; decide +kernel
      have hl : raw10926step2Labels = labelEmbedding6 ∘ raw10926step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10926step2 raw10926step2Labels raw10926step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4868 node4868Labels := by rfl

def raw10927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw10927step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10927step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw10927step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10927step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw10927step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10927 raw10927Labels = mixedMoment B node4744 node4744Labels := by
  calc
    mixedMoment B raw10927 raw10927Labels = mixedMoment B raw10927step0 raw10927step0Labels := by
      have hz : ∀ j, raw10927 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10927step0 = (fun i j => raw10927 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10927step0 raw10927; decide +kernel
      have hl : raw10927step0Labels = raw10927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10927 raw10927Labels permutation434 hz
    mixedMoment B raw10927step0 raw10927step0Labels = mixedMoment B raw10927step1 raw10927step1Labels := by
      have ha : raw10927step1 = (fun i j => raw10927step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10927step1 raw10927step0; decide +kernel
      have hl : raw10927step1Labels = raw10927step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10927step0 raw10927step0Labels permutation40 permutation5
    mixedMoment B raw10927step1 raw10927step1Labels = mixedMoment B raw10927step2 raw10927step2Labels := by
      have ha : raw10927step2 = -raw10927step1 := by apply Matrix.ext; change ∀ i j, raw10927step2 i j = -(raw10927step1 i j); unfold raw10927step2 raw10927step1; decide +kernel
      have hl : raw10927step2Labels = raw10927step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10927step2 raw10927step2Labels = mixedMoment B raw10927step3 raw10927step3Labels := by
      have ha : raw10927step3 = raw10927step2 := by apply Matrix.ext; unfold raw10927step3 raw10927step2; decide +kernel
      have hl : raw10927step2Labels = labelEmbedding8 ∘ raw10927step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10927step2 raw10927step2Labels raw10927step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4744 node4744Labels := by rfl

def raw10928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw10928step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10928step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw10928step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10928step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw10928step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10928 raw10928Labels = mixedMoment B node4744 node4744Labels := by
  calc
    mixedMoment B raw10928 raw10928Labels = mixedMoment B raw10928step0 raw10928step0Labels := by
      have hz : ∀ j, raw10928 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10928step0 = (fun i j => raw10928 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10928step0 raw10928; decide +kernel
      have hl : raw10928step0Labels = raw10928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10928 raw10928Labels permutation346 hz
    mixedMoment B raw10928step0 raw10928step0Labels = mixedMoment B raw10928step1 raw10928step1Labels := by
      have ha : raw10928step1 = (fun i j => raw10928step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10928step1 raw10928step0; decide +kernel
      have hl : raw10928step1Labels = raw10928step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10928step0 raw10928step0Labels permutation40 permutation5
    mixedMoment B raw10928step1 raw10928step1Labels = mixedMoment B raw10928step2 raw10928step2Labels := by
      have ha : raw10928step2 = -raw10928step1 := by apply Matrix.ext; change ∀ i j, raw10928step2 i j = -(raw10928step1 i j); unfold raw10928step2 raw10928step1; decide +kernel
      have hl : raw10928step2Labels = raw10928step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10928step2 raw10928step2Labels = mixedMoment B raw10928step3 raw10928step3Labels := by
      have ha : raw10928step3 = raw10928step2 := by apply Matrix.ext; unfold raw10928step3 raw10928step2; decide +kernel
      have hl : raw10928step2Labels = labelEmbedding8 ∘ raw10928step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10928step2 raw10928step2Labels raw10928step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4744 node4744Labels := by rfl

def raw10929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw10929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw10929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 1, -1], ![3, -2, -1]]
def raw10929step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10929step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw10929step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10929step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw10929step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10929step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw10929step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10929 raw10929Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw10929 raw10929Labels = mixedMoment B raw10929step0 raw10929step0Labels := by
      have hz : ∀ j, raw10929 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10929step0 = (fun i j => raw10929 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10929step0 raw10929; decide +kernel
      have hl : raw10929step0Labels = raw10929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10929 raw10929Labels permutation434 hz
    mixedMoment B raw10929step0 raw10929step0Labels = mixedMoment B raw10929step1 raw10929step1Labels := by
      have hz : ∀ j, raw10929step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10929step1 = (fun i j => raw10929step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10929step1 raw10929step0; decide +kernel
      have hl : raw10929step1Labels = raw10929step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10929step0 raw10929step0Labels permutation80 hz
    mixedMoment B raw10929step1 raw10929step1Labels = mixedMoment B raw10929step2 raw10929step2Labels := by
      have ha : raw10929step2 = (fun i j => raw10929step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10929step2 raw10929step1; decide +kernel
      have hl : raw10929step2Labels = raw10929step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10929step1 raw10929step1Labels permutation10 permutation5
    mixedMoment B raw10929step2 raw10929step2Labels = mixedMoment B raw10929step3 raw10929step3Labels := by
      have ha : raw10929step3 = -raw10929step2 := by apply Matrix.ext; change ∀ i j, raw10929step3 i j = -(raw10929step2 i j); unfold raw10929step3 raw10929step2; decide +kernel
      have hl : raw10929step3Labels = raw10929step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10929step3 raw10929step3Labels = mixedMoment B raw10929step4 raw10929step4Labels := by
      have ha : raw10929step4 = raw10929step3 := by apply Matrix.ext; unfold raw10929step4 raw10929step3; decide +kernel
      have hl : raw10929step3Labels = labelEmbedding8 ∘ raw10929step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10929step3 raw10929step3Labels raw10929step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw10930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10930Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10930step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw10930step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10930step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10930step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10930 raw10930Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw10930 raw10930Labels = mixedMoment B raw10930step0 raw10930step0Labels := by
      have hz : ∀ j, raw10930 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10930step0 = (fun i j => raw10930 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10930step0 raw10930; decide +kernel
      have hl : raw10930step0Labels = raw10930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10930 raw10930Labels permutation434 hz
    mixedMoment B raw10930step0 raw10930step0Labels = mixedMoment B raw10930step1 raw10930step1Labels := by
      have hz : ∀ j, raw10930step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10930step1 = (fun i j => raw10930step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10930step1 raw10930step0; decide +kernel
      have hl : raw10930step1Labels = raw10930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10930step0 raw10930step0Labels permutation80 hz
    mixedMoment B raw10930step1 raw10930step1Labels = mixedMoment B raw10930step2 raw10930step2Labels := by
      have ha : raw10930step2 = (fun i j => raw10930step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10930step2 raw10930step1; decide +kernel
      have hl : raw10930step2Labels = raw10930step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10930step1 raw10930step1Labels permutation8 permutation3
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw10931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10931step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10931 raw10931Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw10931 raw10931Labels = mixedMoment B raw10931step0 raw10931step0Labels := by
      have hz : ∀ j, raw10931 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10931step0 = (fun i j => raw10931 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10931step0 raw10931; decide +kernel
      have hl : raw10931step0Labels = raw10931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10931 raw10931Labels permutation434 hz
    mixedMoment B raw10931step0 raw10931step0Labels = mixedMoment B raw10931step1 raw10931step1Labels := by
      have ha : raw10931step1 = (fun i j => raw10931step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10931step1 raw10931step0; decide +kernel
      have hl : raw10931step1Labels = raw10931step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10931step0 raw10931step0Labels permutation38 permutation3
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw10932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10932step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10932step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10932 raw10932Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw10932 raw10932Labels = mixedMoment B raw10932step0 raw10932step0Labels := by
      have hz : ∀ j, raw10932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10932step0 = (fun i j => raw10932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10932step0 raw10932; decide +kernel
      have hl : raw10932step0Labels = raw10932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10932 raw10932Labels permutation346 hz
    mixedMoment B raw10932step0 raw10932step0Labels = mixedMoment B raw10932step1 raw10932step1Labels := by
      have ha : raw10932step1 = (fun i j => raw10932step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10932step1 raw10932step0; decide +kernel
      have hl : raw10932step1Labels = raw10932step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10932step0 raw10932step0Labels permutation38 permutation3
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw10933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10933step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw10933step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw10933step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10933 raw10933Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw10933 raw10933Labels = mixedMoment B raw10933step0 raw10933step0Labels := by
      have hz : ∀ j, raw10933 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10933step0 = (fun i j => raw10933 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10933step0 raw10933; decide +kernel
      have hl : raw10933step0Labels = raw10933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10933 raw10933Labels permutation434 hz
    mixedMoment B raw10933step0 raw10933step0Labels = mixedMoment B raw10933step1 raw10933step1Labels := by
      have hz : ∀ j, raw10933step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10933step1 = (fun i j => raw10933step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10933step1 raw10933step0; decide +kernel
      have hl : raw10933step1Labels = raw10933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10933step0 raw10933step0Labels permutation80 hz
    mixedMoment B raw10933step1 raw10933step1Labels = mixedMoment B raw10933step2 raw10933step2Labels := by
      have ha : raw10933step2 = (fun i j => raw10933step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10933step2 raw10933step1; decide +kernel
      have hl : raw10933step2Labels = raw10933step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10933step1 raw10933step1Labels permutation10 permutation3
    _ = mixedMoment B node3907 node3907Labels := by rfl

def raw10934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10934Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10934step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw10934step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw10934step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10934 raw10934Labels = mixedMoment B node3915 node3915Labels := by
  calc
    mixedMoment B raw10934 raw10934Labels = mixedMoment B raw10934step0 raw10934step0Labels := by
      have hz : ∀ j, raw10934 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10934step0 = (fun i j => raw10934 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10934step0 raw10934; decide +kernel
      have hl : raw10934step0Labels = raw10934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10934 raw10934Labels permutation434 hz
    mixedMoment B raw10934step0 raw10934step0Labels = mixedMoment B raw10934step1 raw10934step1Labels := by
      have hz : ∀ j, raw10934step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10934step1 = (fun i j => raw10934step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10934step1 raw10934step0; decide +kernel
      have hl : raw10934step1Labels = raw10934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10934step0 raw10934step0Labels permutation80 hz
    mixedMoment B raw10934step1 raw10934step1Labels = mixedMoment B raw10934step2 raw10934step2Labels := by
      have ha : raw10934step2 = (fun i j => raw10934step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10934step2 raw10934step1; decide +kernel
      have hl : raw10934step2Labels = raw10934step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10934step1 raw10934step1Labels permutation8 permutation3
    _ = mixedMoment B node3915 node3915Labels := by rfl

def raw10935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10935Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10935step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw10935step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10935step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw10935step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10935 raw10935Labels = mixedMoment B node853 node853Labels := by
  calc
    mixedMoment B raw10935 raw10935Labels = mixedMoment B raw10935step0 raw10935step0Labels := by
      have hz : ∀ j, raw10935 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10935step0 = (fun i j => raw10935 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10935step0 raw10935; decide +kernel
      have hl : raw10935step0Labels = raw10935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10935 raw10935Labels permutation434 hz
    mixedMoment B raw10935step0 raw10935step0Labels = mixedMoment B raw10935step1 raw10935step1Labels := by
      have hz : ∀ j, raw10935step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10935step1 = (fun i j => raw10935step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10935step1 raw10935step0; decide +kernel
      have hl : raw10935step1Labels = raw10935step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10935step0 raw10935step0Labels permutation80 hz
    mixedMoment B raw10935step1 raw10935step1Labels = mixedMoment B raw10935step2 raw10935step2Labels := by
      have ha : raw10935step2 = (fun i j => raw10935step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10935step2 raw10935step1; decide +kernel
      have hl : raw10935step2Labels = raw10935step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10935step1 raw10935step1Labels permutation10 permutation3
    _ = mixedMoment B node853 node853Labels := by rfl

def raw10936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10936Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10936step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw10936step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10936 raw10936Labels = mixedMoment B node1946 node1946Labels := by
  calc
    mixedMoment B raw10936 raw10936Labels = mixedMoment B raw10936step0 raw10936step0Labels := by
      have hz : ∀ j, raw10936 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10936step0 = (fun i j => raw10936 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10936step0 raw10936; decide +kernel
      have hl : raw10936step0Labels = raw10936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10936 raw10936Labels permutation434 hz
    mixedMoment B raw10936step0 raw10936step0Labels = mixedMoment B raw10936step1 raw10936step1Labels := by
      have ha : raw10936step1 = (fun i j => raw10936step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10936step1 raw10936step0; decide +kernel
      have hl : raw10936step1Labels = raw10936step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10936step0 raw10936step0Labels permutation40 permutation3
    _ = mixedMoment B node1946 node1946Labels := by rfl

def raw10937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10937Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10937step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw10937step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10937 raw10937Labels = mixedMoment B node1946 node1946Labels := by
  calc
    mixedMoment B raw10937 raw10937Labels = mixedMoment B raw10937step0 raw10937step0Labels := by
      have hz : ∀ j, raw10937 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10937step0 = (fun i j => raw10937 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10937step0 raw10937; decide +kernel
      have hl : raw10937step0Labels = raw10937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10937 raw10937Labels permutation346 hz
    mixedMoment B raw10937step0 raw10937step0Labels = mixedMoment B raw10937step1 raw10937step1Labels := by
      have ha : raw10937step1 = (fun i j => raw10937step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10937step1 raw10937step0; decide +kernel
      have hl : raw10937step1Labels = raw10937step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10937step0 raw10937step0Labels permutation40 permutation3
    _ = mixedMoment B node1946 node1946Labels := by rfl

def raw10938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10938Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10938step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 1, -1], ![2, -1, -1]]
def raw10938step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw10938step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10938 raw10938Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw10938 raw10938Labels = mixedMoment B raw10938step0 raw10938step0Labels := by
      have hz : ∀ j, raw10938 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10938step0 = (fun i j => raw10938 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10938step0 raw10938; decide +kernel
      have hl : raw10938step0Labels = raw10938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10938 raw10938Labels permutation434 hz
    mixedMoment B raw10938step0 raw10938step0Labels = mixedMoment B raw10938step1 raw10938step1Labels := by
      have hz : ∀ j, raw10938step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10938step1 = (fun i j => raw10938step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10938step1 raw10938step0; decide +kernel
      have hl : raw10938step1Labels = raw10938step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10938step0 raw10938step0Labels permutation80 hz
    mixedMoment B raw10938step1 raw10938step1Labels = mixedMoment B raw10938step2 raw10938step2Labels := by
      have ha : raw10938step2 = (fun i j => raw10938step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10938step2 raw10938step1; decide +kernel
      have hl : raw10938step2Labels = raw10938step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10938step1 raw10938step1Labels permutation10 permutation3
    _ = mixedMoment B node2230 node2230Labels := by rfl

def raw10939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10939Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10939step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw10939step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw10939step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10939 raw10939Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw10939 raw10939Labels = mixedMoment B raw10939step0 raw10939step0Labels := by
      have hz : ∀ j, raw10939 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10939step0 = (fun i j => raw10939 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10939step0 raw10939; decide +kernel
      have hl : raw10939step0Labels = raw10939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10939 raw10939Labels permutation434 hz
    mixedMoment B raw10939step0 raw10939step0Labels = mixedMoment B raw10939step1 raw10939step1Labels := by
      have hz : ∀ j, raw10939step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10939step1 = (fun i j => raw10939step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10939step1 raw10939step0; decide +kernel
      have hl : raw10939step1Labels = raw10939step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10939step0 raw10939step0Labels permutation80 hz
    mixedMoment B raw10939step1 raw10939step1Labels = mixedMoment B raw10939step2 raw10939step2Labels := by
      have ha : raw10939step2 = (fun i j => raw10939step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10939step2 raw10939step1; decide +kernel
      have hl : raw10939step2Labels = raw10939step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10939step1 raw10939step1Labels permutation11 permutation3
    _ = mixedMoment B node2290 node2290Labels := by rfl

def raw10940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10940Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10940step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10940step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10940 raw10940Labels = mixedMoment B node824 node824Labels := by
  calc
    mixedMoment B raw10940 raw10940Labels = mixedMoment B raw10940step0 raw10940step0Labels := by
      have hz : ∀ j, raw10940 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10940step0 = (fun i j => raw10940 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10940step0 raw10940; decide +kernel
      have hl : raw10940step0Labels = raw10940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10940 raw10940Labels permutation434 hz
    mixedMoment B raw10940step0 raw10940step0Labels = mixedMoment B raw10940step1 raw10940step1Labels := by
      have ha : raw10940step1 = (fun i j => raw10940step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10940step1 raw10940step0; decide +kernel
      have hl : raw10940step1Labels = raw10940step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10940step0 raw10940step0Labels permutation34 permutation3
    _ = mixedMoment B node824 node824Labels := by rfl

def raw10941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10941Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10941step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10941 raw10941Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw10941 raw10941Labels = mixedMoment B raw10941step0 raw10941step0Labels := by
      have hz : ∀ j, raw10941 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10941step0 = (fun i j => raw10941 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10941step0 raw10941; decide +kernel
      have hl : raw10941step0Labels = raw10941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10941 raw10941Labels permutation434 hz
    mixedMoment B raw10941step0 raw10941step0Labels = mixedMoment B raw10941step1 raw10941step1Labels := by
      have ha : raw10941step1 = (fun i j => raw10941step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10941step1 raw10941step0; decide +kernel
      have hl : raw10941step1Labels = raw10941step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10941step0 raw10941step0Labels permutation34 permutation3
    _ = mixedMoment B node2107 node2107Labels := by rfl

def raw10942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10942Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10942step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10942 raw10942Labels = mixedMoment B node1922 node1922Labels := by
  calc
    mixedMoment B raw10942 raw10942Labels = mixedMoment B raw10942step0 raw10942step0Labels := by
      have ha : raw10942step0 = (fun i j => raw10942 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10942step0 raw10942; decide +kernel
      have hl : raw10942step0Labels = raw10942Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10942 raw10942Labels permutation202 permutation3
    _ = mixedMoment B node1922 node1922Labels := by rfl

def raw10943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10943Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10943step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10943step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10943 raw10943Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw10943 raw10943Labels = mixedMoment B raw10943step0 raw10943step0Labels := by
      have hz : ∀ j, raw10943 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10943step0 = (fun i j => raw10943 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10943step0 raw10943; decide +kernel
      have hl : raw10943step0Labels = raw10943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10943 raw10943Labels permutation434 hz
    mixedMoment B raw10943step0 raw10943step0Labels = mixedMoment B raw10943step1 raw10943step1Labels := by
      have ha : raw10943step1 = (fun i j => raw10943step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10943step1 raw10943step0; decide +kernel
      have hl : raw10943step1Labels = raw10943step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10943step0 raw10943step0Labels permutation44 permutation3
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw10944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10944Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10944step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10944step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10944 raw10944Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw10944 raw10944Labels = mixedMoment B raw10944step0 raw10944step0Labels := by
      have hz : ∀ j, raw10944 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10944step0 = (fun i j => raw10944 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10944step0 raw10944; decide +kernel
      have hl : raw10944step0Labels = raw10944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10944 raw10944Labels permutation434 hz
    mixedMoment B raw10944step0 raw10944step0Labels = mixedMoment B raw10944step1 raw10944step1Labels := by
      have ha : raw10944step1 = (fun i j => raw10944step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10944step1 raw10944step0; decide +kernel
      have hl : raw10944step1Labels = raw10944step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10944step0 raw10944step0Labels permutation35 permutation3
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw10945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10945Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10945step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10945step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10945 raw10945Labels = mixedMoment B node824 node824Labels := by
  calc
    mixedMoment B raw10945 raw10945Labels = mixedMoment B raw10945step0 raw10945step0Labels := by
      have hz : ∀ j, raw10945 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10945step0 = (fun i j => raw10945 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10945step0 raw10945; decide +kernel
      have hl : raw10945step0Labels = raw10945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10945 raw10945Labels permutation346 hz
    mixedMoment B raw10945step0 raw10945step0Labels = mixedMoment B raw10945step1 raw10945step1Labels := by
      have ha : raw10945step1 = (fun i j => raw10945step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10945step1 raw10945step0; decide +kernel
      have hl : raw10945step1Labels = raw10945step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10945step0 raw10945step0Labels permutation34 permutation3
    _ = mixedMoment B node824 node824Labels := by rfl

def raw10946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10946Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10946step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10946step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10946 raw10946Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw10946 raw10946Labels = mixedMoment B raw10946step0 raw10946step0Labels := by
      have hz : ∀ j, raw10946 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10946step0 = (fun i j => raw10946 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10946step0 raw10946; decide +kernel
      have hl : raw10946step0Labels = raw10946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10946 raw10946Labels permutation346 hz
    mixedMoment B raw10946step0 raw10946step0Labels = mixedMoment B raw10946step1 raw10946step1Labels := by
      have ha : raw10946step1 = (fun i j => raw10946step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10946step1 raw10946step0; decide +kernel
      have hl : raw10946step1Labels = raw10946step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10946step0 raw10946step0Labels permutation34 permutation3
    _ = mixedMoment B node2107 node2107Labels := by rfl

def raw10947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10947Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10947step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10947 raw10947Labels = mixedMoment B node1922 node1922Labels := by
  calc
    mixedMoment B raw10947 raw10947Labels = mixedMoment B raw10947step0 raw10947step0Labels := by
      have ha : raw10947step0 = (fun i j => raw10947 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10947step0 raw10947; decide +kernel
      have hl : raw10947step0Labels = raw10947Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10947 raw10947Labels permutation178 permutation3
    _ = mixedMoment B node1922 node1922Labels := by rfl

def raw10948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10948Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw10948step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10948 raw10948Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw10948 raw10948Labels = mixedMoment B raw10948step0 raw10948step0Labels := by
      have hz : ∀ j, raw10948 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10948step0 = (fun i j => raw10948 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10948step0 raw10948; decide +kernel
      have hl : raw10948step0Labels = raw10948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10948 raw10948Labels permutation346 hz
    mixedMoment B raw10948step0 raw10948step0Labels = mixedMoment B raw10948step1 raw10948step1Labels := by
      have ha : raw10948step1 = (fun i j => raw10948step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10948step1 raw10948step0; decide +kernel
      have hl : raw10948step1Labels = raw10948step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10948step0 raw10948step0Labels permutation44 permutation3
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw10949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10949Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10949step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10949 raw10949Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw10949 raw10949Labels = mixedMoment B raw10949step0 raw10949step0Labels := by
      have hz : ∀ j, raw10949 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10949step0 = (fun i j => raw10949 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10949step0 raw10949; decide +kernel
      have hl : raw10949step0Labels = raw10949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10949 raw10949Labels permutation346 hz
    mixedMoment B raw10949step0 raw10949step0Labels = mixedMoment B raw10949step1 raw10949step1Labels := by
      have ha : raw10949step1 = (fun i j => raw10949step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10949step1 raw10949step0; decide +kernel
      have hl : raw10949step1Labels = raw10949step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10949step0 raw10949step0Labels permutation35 permutation3
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw10950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10950Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10950step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw10950step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10950step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw10950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10950 raw10950Labels = mixedMoment B node831 node831Labels := by
  calc
    mixedMoment B raw10950 raw10950Labels = mixedMoment B raw10950step0 raw10950step0Labels := by
      have hz : ∀ j, raw10950 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10950step0 = (fun i j => raw10950 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10950step0 raw10950; decide +kernel
      have hl : raw10950step0Labels = raw10950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10950 raw10950Labels permutation434 hz
    mixedMoment B raw10950step0 raw10950step0Labels = mixedMoment B raw10950step1 raw10950step1Labels := by
      have hz : ∀ j, raw10950step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10950step1 = (fun i j => raw10950step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10950step1 raw10950step0; decide +kernel
      have hl : raw10950step1Labels = raw10950step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10950step0 raw10950step0Labels permutation80 hz
    mixedMoment B raw10950step1 raw10950step1Labels = mixedMoment B raw10950step2 raw10950step2Labels := by
      have ha : raw10950step2 = (fun i j => raw10950step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10950step2 raw10950step1; decide +kernel
      have hl : raw10950step2Labels = raw10950step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10950step1 raw10950step1Labels permutation8 permutation3
    _ = mixedMoment B node831 node831Labels := by rfl

def raw10951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10951Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10951step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw10951step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw10951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10951 raw10951Labels = mixedMoment B node2116 node2116Labels := by
  calc
    mixedMoment B raw10951 raw10951Labels = mixedMoment B raw10951step0 raw10951step0Labels := by
      have hz : ∀ j, raw10951 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10951step0 = (fun i j => raw10951 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10951step0 raw10951; decide +kernel
      have hl : raw10951step0Labels = raw10951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10951 raw10951Labels permutation434 hz
    mixedMoment B raw10951step0 raw10951step0Labels = mixedMoment B raw10951step1 raw10951step1Labels := by
      have hz : ∀ j, raw10951step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10951step1 = (fun i j => raw10951step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10951step1 raw10951step0; decide +kernel
      have hl : raw10951step1Labels = raw10951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10951step0 raw10951step0Labels permutation80 hz
    mixedMoment B raw10951step1 raw10951step1Labels = mixedMoment B raw10951step2 raw10951step2Labels := by
      have ha : raw10951step2 = (fun i j => raw10951step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10951step2 raw10951step1; decide +kernel
      have hl : raw10951step2Labels = raw10951step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10951step1 raw10951step1Labels permutation8 permutation3
    _ = mixedMoment B node2116 node2116Labels := by rfl

def raw10952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10952Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10952step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw10952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10952 raw10952Labels = mixedMoment B node1929 node1929Labels := by
  calc
    mixedMoment B raw10952 raw10952Labels = mixedMoment B raw10952step0 raw10952step0Labels := by
      have hz : ∀ j, raw10952 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10952step0 = (fun i j => raw10952 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10952step0 raw10952; decide +kernel
      have hl : raw10952step0Labels = raw10952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10952 raw10952Labels permutation434 hz
    mixedMoment B raw10952step0 raw10952step0Labels = mixedMoment B raw10952step1 raw10952step1Labels := by
      have ha : raw10952step1 = (fun i j => raw10952step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10952step1 raw10952step0; decide +kernel
      have hl : raw10952step1Labels = raw10952step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10952step0 raw10952step0Labels permutation38 permutation3
    _ = mixedMoment B node1929 node1929Labels := by rfl

def raw10953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10953Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10953step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw10953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10953 raw10953Labels = mixedMoment B node1929 node1929Labels := by
  calc
    mixedMoment B raw10953 raw10953Labels = mixedMoment B raw10953step0 raw10953step0Labels := by
      have hz : ∀ j, raw10953 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10953step0 = (fun i j => raw10953 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10953step0 raw10953; decide +kernel
      have hl : raw10953step0Labels = raw10953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10953 raw10953Labels permutation346 hz
    mixedMoment B raw10953step0 raw10953step0Labels = mixedMoment B raw10953step1 raw10953step1Labels := by
      have ha : raw10953step1 = (fun i j => raw10953step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10953step1 raw10953step0; decide +kernel
      have hl : raw10953step1Labels = raw10953step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10953step0 raw10953step0Labels permutation38 permutation3
    _ = mixedMoment B node1929 node1929Labels := by rfl

def raw10954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw10954Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw10954step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10954step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw10954step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10954step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10954 raw10954Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw10954 raw10954Labels = mixedMoment B raw10954step0 raw10954step0Labels := by
      have hz : ∀ j, raw10954 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10954step0 = (fun i j => raw10954 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10954step0 raw10954; decide +kernel
      have hl : raw10954step0Labels = raw10954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10954 raw10954Labels permutation434 hz
    mixedMoment B raw10954step0 raw10954step0Labels = mixedMoment B raw10954step1 raw10954step1Labels := by
      have hz : ∀ j, raw10954step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10954step1 = (fun i j => raw10954step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10954step1 raw10954step0; decide +kernel
      have hl : raw10954step1Labels = raw10954step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10954step0 raw10954step0Labels permutation80 hz
    mixedMoment B raw10954step1 raw10954step1Labels = mixedMoment B raw10954step2 raw10954step2Labels := by
      have ha : raw10954step2 = (fun i j => raw10954step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10954step2 raw10954step1; decide +kernel
      have hl : raw10954step2Labels = raw10954step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10954step1 raw10954step1Labels permutation9 permutation3
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw10955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10955Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10955step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw10955step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10955step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw10955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10955 raw10955Labels = mixedMoment B node826 node826Labels := by
  calc
    mixedMoment B raw10955 raw10955Labels = mixedMoment B raw10955step0 raw10955step0Labels := by
      have hz : ∀ j, raw10955 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10955step0 = (fun i j => raw10955 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10955step0 raw10955; decide +kernel
      have hl : raw10955step0Labels = raw10955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10955 raw10955Labels permutation434 hz
    mixedMoment B raw10955step0 raw10955step0Labels = mixedMoment B raw10955step1 raw10955step1Labels := by
      have hz : ∀ j, raw10955step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10955step1 = (fun i j => raw10955step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10955step1 raw10955step0; decide +kernel
      have hl : raw10955step1Labels = raw10955step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10955step0 raw10955step0Labels permutation80 hz
    mixedMoment B raw10955step1 raw10955step1Labels = mixedMoment B raw10955step2 raw10955step2Labels := by
      have ha : raw10955step2 = (fun i j => raw10955step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10955step2 raw10955step1; decide +kernel
      have hl : raw10955step2Labels = raw10955step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10955step1 raw10955step1Labels permutation8 permutation3
    _ = mixedMoment B node826 node826Labels := by rfl

def raw10956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10956Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10956step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -2, -1]]
def raw10956step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10956step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10956 raw10956Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw10956 raw10956Labels = mixedMoment B raw10956step0 raw10956step0Labels := by
      have hz : ∀ j, raw10956 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10956step0 = (fun i j => raw10956 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10956step0 raw10956; decide +kernel
      have hl : raw10956step0Labels = raw10956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10956 raw10956Labels permutation434 hz
    mixedMoment B raw10956step0 raw10956step0Labels = mixedMoment B raw10956step1 raw10956step1Labels := by
      have hz : ∀ j, raw10956step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10956step1 = (fun i j => raw10956step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10956step1 raw10956step0; decide +kernel
      have hl : raw10956step1Labels = raw10956step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10956step0 raw10956step0Labels permutation80 hz
    mixedMoment B raw10956step1 raw10956step1Labels = mixedMoment B raw10956step2 raw10956step2Labels := by
      have ha : raw10956step2 = (fun i j => raw10956step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10956step2 raw10956step1; decide +kernel
      have hl : raw10956step2Labels = raw10956step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10956step1 raw10956step1Labels permutation8 permutation3
    _ = mixedMoment B node2109 node2109Labels := by rfl

def raw10957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10957step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw10957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10957 raw10957Labels = mixedMoment B node1924 node1924Labels := by
  calc
    mixedMoment B raw10957 raw10957Labels = mixedMoment B raw10957step0 raw10957step0Labels := by
      have hz : ∀ j, raw10957 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10957step0 = (fun i j => raw10957 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10957step0 raw10957; decide +kernel
      have hl : raw10957step0Labels = raw10957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10957 raw10957Labels permutation434 hz
    mixedMoment B raw10957step0 raw10957step0Labels = mixedMoment B raw10957step1 raw10957step1Labels := by
      have ha : raw10957step1 = (fun i j => raw10957step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10957step1 raw10957step0; decide +kernel
      have hl : raw10957step1Labels = raw10957step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10957step0 raw10957step0Labels permutation38 permutation3
    _ = mixedMoment B node1924 node1924Labels := by rfl

def raw10958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw10958step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw10958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10958 raw10958Labels = mixedMoment B node1924 node1924Labels := by
  calc
    mixedMoment B raw10958 raw10958Labels = mixedMoment B raw10958step0 raw10958step0Labels := by
      have hz : ∀ j, raw10958 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10958step0 = (fun i j => raw10958 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10958step0 raw10958; decide +kernel
      have hl : raw10958step0Labels = raw10958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10958 raw10958Labels permutation346 hz
    mixedMoment B raw10958step0 raw10958step0Labels = mixedMoment B raw10958step1 raw10958step1Labels := by
      have ha : raw10958step1 = (fun i j => raw10958step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10958step1 raw10958step0; decide +kernel
      have hl : raw10958step1Labels = raw10958step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10958step0 raw10958step0Labels permutation38 permutation3
    _ = mixedMoment B node1924 node1924Labels := by rfl

def raw10959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw10959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw10959step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 1, -1], ![3, -2, -1]]
def raw10959step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10959step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw10959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10959 raw10959Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw10959 raw10959Labels = mixedMoment B raw10959step0 raw10959step0Labels := by
      have hz : ∀ j, raw10959 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10959step0 = (fun i j => raw10959 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10959step0 raw10959; decide +kernel
      have hl : raw10959step0Labels = raw10959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10959 raw10959Labels permutation434 hz
    mixedMoment B raw10959step0 raw10959step0Labels = mixedMoment B raw10959step1 raw10959step1Labels := by
      have hz : ∀ j, raw10959step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10959step1 = (fun i j => raw10959step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10959step1 raw10959step0; decide +kernel
      have hl : raw10959step1Labels = raw10959step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10959step0 raw10959step0Labels permutation80 hz
    mixedMoment B raw10959step1 raw10959step1Labels = mixedMoment B raw10959step2 raw10959step2Labels := by
      have ha : raw10959step2 = (fun i j => raw10959step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10959step2 raw10959step1; decide +kernel
      have hl : raw10959step2Labels = raw10959step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10959step1 raw10959step1Labels permutation10 permutation3
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw10960 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10960step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10960step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10960step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10960step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10960 raw10960Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw10960 raw10960Labels = mixedMoment B raw10960step0 raw10960step0Labels := by
      have hz : ∀ j, raw10960 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10960step0 = (fun i j => raw10960 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10960step0 raw10960; decide +kernel
      have hl : raw10960step0Labels = raw10960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10960 raw10960Labels permutation434 hz
    mixedMoment B raw10960step0 raw10960step0Labels = mixedMoment B raw10960step1 raw10960step1Labels := by
      have ha : raw10960step1 = (fun i j => raw10960step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10960step1 raw10960step0; decide +kernel
      have hl : raw10960step1Labels = raw10960step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10960step0 raw10960step0Labels permutation38 permutation6
    mixedMoment B raw10960step1 raw10960step1Labels = mixedMoment B raw10960step2 raw10960step2Labels := by
      have ha : raw10960step2 = raw10960step1 := by apply Matrix.ext; unfold raw10960step2 raw10960step1; decide +kernel
      have hl : raw10960step1Labels = labelEmbedding9 ∘ raw10960step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10960step1 raw10960step1Labels raw10960step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw10961 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10961Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10961step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10961step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10961step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10961step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10961step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10961 raw10961Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw10961 raw10961Labels = mixedMoment B raw10961step0 raw10961step0Labels := by
      have hz : ∀ j, raw10961 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10961step0 = (fun i j => raw10961 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10961step0 raw10961; decide +kernel
      have hl : raw10961step0Labels = raw10961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10961 raw10961Labels permutation434 hz
    mixedMoment B raw10961step0 raw10961step0Labels = mixedMoment B raw10961step1 raw10961step1Labels := by
      have hz : ∀ j, raw10961step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10961step1 = (fun i j => raw10961step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10961step1 raw10961step0; decide +kernel
      have hl : raw10961step1Labels = raw10961step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10961step0 raw10961step0Labels permutation80 hz
    mixedMoment B raw10961step1 raw10961step1Labels = mixedMoment B raw10961step2 raw10961step2Labels := by
      have ha : raw10961step2 = (fun i j => raw10961step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10961step2 raw10961step1; decide +kernel
      have hl : raw10961step2Labels = raw10961step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10961step1 raw10961step1Labels permutation8 permutation6
    mixedMoment B raw10961step2 raw10961step2Labels = mixedMoment B raw10961step3 raw10961step3Labels := by
      have ha : raw10961step3 = raw10961step2 := by apply Matrix.ext; unfold raw10961step3 raw10961step2; decide +kernel
      have hl : raw10961step2Labels = labelEmbedding9 ∘ raw10961step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10961step2 raw10961step2Labels raw10961step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw10962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10962step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10962step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw10962step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10962step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw10962step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10962step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw10962step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10962 raw10962Labels = mixedMoment B node4464 node4464Labels := by
  calc
    mixedMoment B raw10962 raw10962Labels = mixedMoment B raw10962step0 raw10962step0Labels := by
      have hz : ∀ j, raw10962 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10962step0 = (fun i j => raw10962 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10962step0 raw10962; decide +kernel
      have hl : raw10962step0Labels = raw10962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10962 raw10962Labels permutation434 hz
    mixedMoment B raw10962step0 raw10962step0Labels = mixedMoment B raw10962step1 raw10962step1Labels := by
      have hz : ∀ j, raw10962step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10962step1 = (fun i j => raw10962step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10962step1 raw10962step0; decide +kernel
      have hl : raw10962step1Labels = raw10962step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10962step0 raw10962step0Labels permutation80 hz
    mixedMoment B raw10962step1 raw10962step1Labels = mixedMoment B raw10962step2 raw10962step2Labels := by
      have ha : raw10962step2 = (fun i j => raw10962step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10962step2 raw10962step1; decide +kernel
      have hl : raw10962step2Labels = raw10962step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10962step1 raw10962step1Labels permutation11 permutation4
    mixedMoment B raw10962step2 raw10962step2Labels = mixedMoment B raw10962step3 raw10962step3Labels := by
      have ha : raw10962step3 = -raw10962step2 := by apply Matrix.ext; change ∀ i j, raw10962step3 i j = -(raw10962step2 i j); unfold raw10962step3 raw10962step2; decide +kernel
      have hl : raw10962step3Labels = raw10962step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10962step3 raw10962step3Labels = mixedMoment B raw10962step4 raw10962step4Labels := by
      have ha : raw10962step4 = raw10962step3 := by apply Matrix.ext; unfold raw10962step4 raw10962step3; decide +kernel
      have hl : raw10962step3Labels = labelEmbedding7 ∘ raw10962step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10962step3 raw10962step3Labels raw10962step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4464 node4464Labels := by rfl

def raw10963 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10963Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10963step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw10963step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10963step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw10963step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10963step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw10963step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10963 raw10963Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw10963 raw10963Labels = mixedMoment B raw10963step0 raw10963step0Labels := by
      have hz : ∀ j, raw10963 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10963step0 = (fun i j => raw10963 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10963step0 raw10963; decide +kernel
      have hl : raw10963step0Labels = raw10963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10963 raw10963Labels permutation434 hz
    mixedMoment B raw10963step0 raw10963step0Labels = mixedMoment B raw10963step1 raw10963step1Labels := by
      have ha : raw10963step1 = (fun i j => raw10963step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10963step1 raw10963step0; decide +kernel
      have hl : raw10963step1Labels = raw10963step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10963step0 raw10963step0Labels permutation41 permutation4
    mixedMoment B raw10963step1 raw10963step1Labels = mixedMoment B raw10963step2 raw10963step2Labels := by
      have ha : raw10963step2 = -raw10963step1 := by apply Matrix.ext; change ∀ i j, raw10963step2 i j = -(raw10963step1 i j); unfold raw10963step2 raw10963step1; decide +kernel
      have hl : raw10963step2Labels = raw10963step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10963step2 raw10963step2Labels = mixedMoment B raw10963step3 raw10963step3Labels := by
      have ha : raw10963step3 = raw10963step2 := by apply Matrix.ext; unfold raw10963step3 raw10963step2; decide +kernel
      have hl : raw10963step2Labels = labelEmbedding7 ∘ raw10963step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10963step2 raw10963step2Labels raw10963step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw10964 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10964Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10964step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw10964step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw10964step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10964step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw10964step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10964 raw10964Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw10964 raw10964Labels = mixedMoment B raw10964step0 raw10964step0Labels := by
      have hz : ∀ j, raw10964 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10964step0 = (fun i j => raw10964 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10964step0 raw10964; decide +kernel
      have hl : raw10964step0Labels = raw10964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10964 raw10964Labels permutation346 hz
    mixedMoment B raw10964step0 raw10964step0Labels = mixedMoment B raw10964step1 raw10964step1Labels := by
      have ha : raw10964step1 = (fun i j => raw10964step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10964step1 raw10964step0; decide +kernel
      have hl : raw10964step1Labels = raw10964step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10964step0 raw10964step0Labels permutation41 permutation4
    mixedMoment B raw10964step1 raw10964step1Labels = mixedMoment B raw10964step2 raw10964step2Labels := by
      have ha : raw10964step2 = -raw10964step1 := by apply Matrix.ext; change ∀ i j, raw10964step2 i j = -(raw10964step1 i j); unfold raw10964step2 raw10964step1; decide +kernel
      have hl : raw10964step2Labels = raw10964step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10964step2 raw10964step2Labels = mixedMoment B raw10964step3 raw10964step3Labels := by
      have ha : raw10964step3 = raw10964step2 := by apply Matrix.ext; unfold raw10964step3 raw10964step2; decide +kernel
      have hl : raw10964step2Labels = labelEmbedding7 ∘ raw10964step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10964step2 raw10964step2Labels raw10964step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw10965 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10965Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10965step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10965step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10965step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10965step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw10965step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10965step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw10965step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10965step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw10965step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10965 raw10965Labels = mixedMoment B node4872 node4872Labels := by
  calc
    mixedMoment B raw10965 raw10965Labels = mixedMoment B raw10965step0 raw10965step0Labels := by
      have hz : ∀ j, raw10965 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10965step0 = (fun i j => raw10965 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10965step0 raw10965; decide +kernel
      have hl : raw10965step0Labels = raw10965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10965 raw10965Labels permutation434 hz
    mixedMoment B raw10965step0 raw10965step0Labels = mixedMoment B raw10965step1 raw10965step1Labels := by
      have hz : ∀ j, raw10965step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10965step1 = (fun i j => raw10965step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10965step1 raw10965step0; decide +kernel
      have hl : raw10965step1Labels = raw10965step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10965step0 raw10965step0Labels permutation80 hz
    mixedMoment B raw10965step1 raw10965step1Labels = mixedMoment B raw10965step2 raw10965step2Labels := by
      have ha : raw10965step2 = (fun i j => raw10965step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10965step2 raw10965step1; decide +kernel
      have hl : raw10965step2Labels = raw10965step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10965step1 raw10965step1Labels permutation11 permutation4
    mixedMoment B raw10965step2 raw10965step2Labels = mixedMoment B raw10965step3 raw10965step3Labels := by
      have ha : raw10965step3 = -raw10965step2 := by apply Matrix.ext; change ∀ i j, raw10965step3 i j = -(raw10965step2 i j); unfold raw10965step3 raw10965step2; decide +kernel
      have hl : raw10965step3Labels = raw10965step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10965step3 raw10965step3Labels = mixedMoment B raw10965step4 raw10965step4Labels := by
      have ha : raw10965step4 = raw10965step3 := by apply Matrix.ext; unfold raw10965step4 raw10965step3; decide +kernel
      have hl : raw10965step3Labels = labelEmbedding7 ∘ raw10965step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10965step3 raw10965step3Labels raw10965step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4872 node4872Labels := by rfl

def raw10966 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10966step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10966step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10966step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw10966step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10966step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw10966step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10966step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw10966step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10966 raw10966Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw10966 raw10966Labels = mixedMoment B raw10966step0 raw10966step0Labels := by
      have hz : ∀ j, raw10966 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10966step0 = (fun i j => raw10966 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10966step0 raw10966; decide +kernel
      have hl : raw10966step0Labels = raw10966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10966 raw10966Labels permutation434 hz
    mixedMoment B raw10966step0 raw10966step0Labels = mixedMoment B raw10966step1 raw10966step1Labels := by
      have hz : ∀ j, raw10966step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10966step1 = (fun i j => raw10966step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10966step1 raw10966step0; decide +kernel
      have hl : raw10966step1Labels = raw10966step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10966step0 raw10966step0Labels permutation80 hz
    mixedMoment B raw10966step1 raw10966step1Labels = mixedMoment B raw10966step2 raw10966step2Labels := by
      have ha : raw10966step2 = (fun i j => raw10966step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10966step2 raw10966step1; decide +kernel
      have hl : raw10966step2Labels = raw10966step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10966step1 raw10966step1Labels permutation11 permutation4
    mixedMoment B raw10966step2 raw10966step2Labels = mixedMoment B raw10966step3 raw10966step3Labels := by
      have ha : raw10966step3 = -raw10966step2 := by apply Matrix.ext; change ∀ i j, raw10966step3 i j = -(raw10966step2 i j); unfold raw10966step3 raw10966step2; decide +kernel
      have hl : raw10966step3Labels = raw10966step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10966step3 raw10966step3Labels = mixedMoment B raw10966step4 raw10966step4Labels := by
      have ha : raw10966step4 = raw10966step3 := by apply Matrix.ext; unfold raw10966step4 raw10966step3; decide +kernel
      have hl : raw10966step3Labels = labelEmbedding7 ∘ raw10966step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10966step3 raw10966step3Labels raw10966step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4892 node4892Labels := by rfl

def raw10967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10967step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw10967step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10967step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10967step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10967step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10967 raw10967Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw10967 raw10967Labels = mixedMoment B raw10967step0 raw10967step0Labels := by
      have hz : ∀ j, raw10967 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10967step0 = (fun i j => raw10967 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10967step0 raw10967; decide +kernel
      have hl : raw10967step0Labels = raw10967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10967 raw10967Labels permutation434 hz
    mixedMoment B raw10967step0 raw10967step0Labels = mixedMoment B raw10967step1 raw10967step1Labels := by
      have ha : raw10967step1 = (fun i j => raw10967step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10967step1 raw10967step0; decide +kernel
      have hl : raw10967step1Labels = raw10967step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10967step0 raw10967step0Labels permutation47 permutation4
    mixedMoment B raw10967step1 raw10967step1Labels = mixedMoment B raw10967step2 raw10967step2Labels := by
      have ha : raw10967step2 = -raw10967step1 := by apply Matrix.ext; change ∀ i j, raw10967step2 i j = -(raw10967step1 i j); unfold raw10967step2 raw10967step1; decide +kernel
      have hl : raw10967step2Labels = raw10967step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10967step2 raw10967step2Labels = mixedMoment B raw10967step3 raw10967step3Labels := by
      have ha : raw10967step3 = raw10967step2 := by apply Matrix.ext; unfold raw10967step3 raw10967step2; decide +kernel
      have hl : raw10967step2Labels = labelEmbedding7 ∘ raw10967step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10967step2 raw10967step2Labels raw10967step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw10968 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw10968step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10968step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10968step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10968step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10968step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10968 raw10968Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw10968 raw10968Labels = mixedMoment B raw10968step0 raw10968step0Labels := by
      have ha : raw10968step0 = (fun i j => raw10968 (permutation215 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10968step0 raw10968; decide +kernel
      have hl : raw10968step0Labels = raw10968Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10968 raw10968Labels permutation215 permutation4
    mixedMoment B raw10968step0 raw10968step0Labels = mixedMoment B raw10968step1 raw10968step1Labels := by
      have ha : raw10968step1 = -raw10968step0 := by apply Matrix.ext; change ∀ i j, raw10968step1 i j = -(raw10968step0 i j); unfold raw10968step1 raw10968step0; decide +kernel
      have hl : raw10968step1Labels = raw10968step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10968step1 raw10968step1Labels = mixedMoment B raw10968step2 raw10968step2Labels := by
      have ha : raw10968step2 = raw10968step1 := by apply Matrix.ext; unfold raw10968step2 raw10968step1; decide +kernel
      have hl : raw10968step1Labels = labelEmbedding7 ∘ raw10968step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10968step1 raw10968step1Labels raw10968step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw10969 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw10969step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10969step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10969step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10969step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10969 raw10969Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw10969 raw10969Labels = mixedMoment B raw10969step0 raw10969step0Labels := by
      have hz : ∀ j, raw10969 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10969step0 = (fun i j => raw10969 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10969step0 raw10969; decide +kernel
      have hl : raw10969step0Labels = raw10969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10969 raw10969Labels permutation434 hz
    mixedMoment B raw10969step0 raw10969step0Labels = mixedMoment B raw10969step1 raw10969step1Labels := by
      have ha : raw10969step1 = (fun i j => raw10969step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10969step1 raw10969step0; decide +kernel
      have hl : raw10969step1Labels = raw10969step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10969step0 raw10969step0Labels permutation47 permutation4
    mixedMoment B raw10969step1 raw10969step1Labels = mixedMoment B raw10969step2 raw10969step2Labels := by
      have ha : raw10969step2 = -raw10969step1 := by apply Matrix.ext; change ∀ i j, raw10969step2 i j = -(raw10969step1 i j); unfold raw10969step2 raw10969step1; decide +kernel
      have hl : raw10969step2Labels = raw10969step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10969step2 raw10969step2Labels = mixedMoment B raw10969step3 raw10969step3Labels := by
      have ha : raw10969step3 = raw10969step2 := by apply Matrix.ext; unfold raw10969step3 raw10969step2; decide +kernel
      have hl : raw10969step2Labels = labelEmbedding7 ∘ raw10969step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10969step2 raw10969step2Labels raw10969step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw10970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw10970step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10970step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10970step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10970step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10970 raw10970Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw10970 raw10970Labels = mixedMoment B raw10970step0 raw10970step0Labels := by
      have hz : ∀ j, raw10970 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10970step0 = (fun i j => raw10970 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10970step0 raw10970; decide +kernel
      have hl : raw10970step0Labels = raw10970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10970 raw10970Labels permutation346 hz
    mixedMoment B raw10970step0 raw10970step0Labels = mixedMoment B raw10970step1 raw10970step1Labels := by
      have ha : raw10970step1 = (fun i j => raw10970step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10970step1 raw10970step0; decide +kernel
      have hl : raw10970step1Labels = raw10970step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10970step0 raw10970step0Labels permutation47 permutation4
    mixedMoment B raw10970step1 raw10970step1Labels = mixedMoment B raw10970step2 raw10970step2Labels := by
      have ha : raw10970step2 = -raw10970step1 := by apply Matrix.ext; change ∀ i j, raw10970step2 i j = -(raw10970step1 i j); unfold raw10970step2 raw10970step1; decide +kernel
      have hl : raw10970step2Labels = raw10970step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10970step2 raw10970step2Labels = mixedMoment B raw10970step3 raw10970step3Labels := by
      have ha : raw10970step3 = raw10970step2 := by apply Matrix.ext; unfold raw10970step3 raw10970step2; decide +kernel
      have hl : raw10970step2Labels = labelEmbedding7 ∘ raw10970step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10970step2 raw10970step2Labels raw10970step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw10971 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw10971step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10971step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10971step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10971step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10971 raw10971Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw10971 raw10971Labels = mixedMoment B raw10971step0 raw10971step0Labels := by
      have ha : raw10971step0 = (fun i j => raw10971 (permutation191 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10971step0 raw10971; decide +kernel
      have hl : raw10971step0Labels = raw10971Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10971 raw10971Labels permutation191 permutation4
    mixedMoment B raw10971step0 raw10971step0Labels = mixedMoment B raw10971step1 raw10971step1Labels := by
      have ha : raw10971step1 = -raw10971step0 := by apply Matrix.ext; change ∀ i j, raw10971step1 i j = -(raw10971step0 i j); unfold raw10971step1 raw10971step0; decide +kernel
      have hl : raw10971step1Labels = raw10971step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10971step1 raw10971step1Labels = mixedMoment B raw10971step2 raw10971step2Labels := by
      have ha : raw10971step2 = raw10971step1 := by apply Matrix.ext; unfold raw10971step2 raw10971step1; decide +kernel
      have hl : raw10971step1Labels = labelEmbedding7 ∘ raw10971step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10971step1 raw10971step1Labels raw10971step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw10972 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10972step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw10972step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10972step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10972step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw10972step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10972 raw10972Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw10972 raw10972Labels = mixedMoment B raw10972step0 raw10972step0Labels := by
      have hz : ∀ j, raw10972 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10972step0 = (fun i j => raw10972 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10972step0 raw10972; decide +kernel
      have hl : raw10972step0Labels = raw10972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10972 raw10972Labels permutation346 hz
    mixedMoment B raw10972step0 raw10972step0Labels = mixedMoment B raw10972step1 raw10972step1Labels := by
      have ha : raw10972step1 = (fun i j => raw10972step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10972step1 raw10972step0; decide +kernel
      have hl : raw10972step1Labels = raw10972step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10972step0 raw10972step0Labels permutation47 permutation4
    mixedMoment B raw10972step1 raw10972step1Labels = mixedMoment B raw10972step2 raw10972step2Labels := by
      have ha : raw10972step2 = -raw10972step1 := by apply Matrix.ext; change ∀ i j, raw10972step2 i j = -(raw10972step1 i j); unfold raw10972step2 raw10972step1; decide +kernel
      have hl : raw10972step2Labels = raw10972step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10972step2 raw10972step2Labels = mixedMoment B raw10972step3 raw10972step3Labels := by
      have ha : raw10972step3 = raw10972step2 := by apply Matrix.ext; unfold raw10972step3 raw10972step2; decide +kernel
      have hl : raw10972step2Labels = labelEmbedding7 ∘ raw10972step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10972step2 raw10972step2Labels raw10972step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw10973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10973step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10973step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10973step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10973step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10973step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10973step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10973step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10973 raw10973Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw10973 raw10973Labels = mixedMoment B raw10973step0 raw10973step0Labels := by
      have hz : ∀ j, raw10973 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10973step0 = (fun i j => raw10973 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10973step0 raw10973; decide +kernel
      have hl : raw10973step0Labels = raw10973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10973 raw10973Labels permutation434 hz
    mixedMoment B raw10973step0 raw10973step0Labels = mixedMoment B raw10973step1 raw10973step1Labels := by
      have hz : ∀ j, raw10973step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10973step1 = (fun i j => raw10973step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10973step1 raw10973step0; decide +kernel
      have hl : raw10973step1Labels = raw10973step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10973step0 raw10973step0Labels permutation80 hz
    mixedMoment B raw10973step1 raw10973step1Labels = mixedMoment B raw10973step2 raw10973step2Labels := by
      have ha : raw10973step2 = (fun i j => raw10973step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10973step2 raw10973step1; decide +kernel
      have hl : raw10973step2Labels = raw10973step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10973step1 raw10973step1Labels permutation11 permutation4
    mixedMoment B raw10973step2 raw10973step2Labels = mixedMoment B raw10973step3 raw10973step3Labels := by
      have ha : raw10973step3 = -raw10973step2 := by apply Matrix.ext; change ∀ i j, raw10973step3 i j = -(raw10973step2 i j); unfold raw10973step3 raw10973step2; decide +kernel
      have hl : raw10973step3Labels = raw10973step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10973step3 raw10973step3Labels = mixedMoment B raw10973step4 raw10973step4Labels := by
      have ha : raw10973step4 = raw10973step3 := by apply Matrix.ext; unfold raw10973step4 raw10973step3; decide +kernel
      have hl : raw10973step3Labels = labelEmbedding7 ∘ raw10973step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10973step3 raw10973step3Labels raw10973step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw10974 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10974step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw10974step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10974step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10974step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10974step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10974 raw10974Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw10974 raw10974Labels = mixedMoment B raw10974step0 raw10974step0Labels := by
      have hz : ∀ j, raw10974 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10974step0 = (fun i j => raw10974 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10974step0 raw10974; decide +kernel
      have hl : raw10974step0Labels = raw10974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10974 raw10974Labels permutation434 hz
    mixedMoment B raw10974step0 raw10974step0Labels = mixedMoment B raw10974step1 raw10974step1Labels := by
      have ha : raw10974step1 = (fun i j => raw10974step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10974step1 raw10974step0; decide +kernel
      have hl : raw10974step1Labels = raw10974step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10974step0 raw10974step0Labels permutation41 permutation4
    mixedMoment B raw10974step1 raw10974step1Labels = mixedMoment B raw10974step2 raw10974step2Labels := by
      have ha : raw10974step2 = -raw10974step1 := by apply Matrix.ext; change ∀ i j, raw10974step2 i j = -(raw10974step1 i j); unfold raw10974step2 raw10974step1; decide +kernel
      have hl : raw10974step2Labels = raw10974step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10974step2 raw10974step2Labels = mixedMoment B raw10974step3 raw10974step3Labels := by
      have ha : raw10974step3 = raw10974step2 := by apply Matrix.ext; unfold raw10974step3 raw10974step2; decide +kernel
      have hl : raw10974step2Labels = labelEmbedding7 ∘ raw10974step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10974step2 raw10974step2Labels raw10974step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw10975 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw10975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw10975step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw10975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10975step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw10975step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10975step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10975step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10975step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10975step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10975 raw10975Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw10975 raw10975Labels = mixedMoment B raw10975step0 raw10975step0Labels := by
      have hz : ∀ j, raw10975 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10975step0 = (fun i j => raw10975 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10975step0 raw10975; decide +kernel
      have hl : raw10975step0Labels = raw10975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10975 raw10975Labels permutation434 hz
    mixedMoment B raw10975step0 raw10975step0Labels = mixedMoment B raw10975step1 raw10975step1Labels := by
      have hz : ∀ j, raw10975step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10975step1 = (fun i j => raw10975step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10975step1 raw10975step0; decide +kernel
      have hl : raw10975step1Labels = raw10975step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10975step0 raw10975step0Labels permutation80 hz
    mixedMoment B raw10975step1 raw10975step1Labels = mixedMoment B raw10975step2 raw10975step2Labels := by
      have ha : raw10975step2 = (fun i j => raw10975step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10975step2 raw10975step1; decide +kernel
      have hl : raw10975step2Labels = raw10975step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10975step1 raw10975step1Labels permutation13 permutation4
    mixedMoment B raw10975step2 raw10975step2Labels = mixedMoment B raw10975step3 raw10975step3Labels := by
      have ha : raw10975step3 = -raw10975step2 := by apply Matrix.ext; change ∀ i j, raw10975step3 i j = -(raw10975step2 i j); unfold raw10975step3 raw10975step2; decide +kernel
      have hl : raw10975step3Labels = raw10975step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10975step3 raw10975step3Labels = mixedMoment B raw10975step4 raw10975step4Labels := by
      have ha : raw10975step4 = raw10975step3 := by apply Matrix.ext; unfold raw10975step4 raw10975step3; decide +kernel
      have hl : raw10975step3Labels = labelEmbedding7 ∘ raw10975step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10975step3 raw10975step3Labels raw10975step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

def raw10976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10976step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10976step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw10976step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10976step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10976step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10976step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10976 raw10976Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw10976 raw10976Labels = mixedMoment B raw10976step0 raw10976step0Labels := by
      have hz : ∀ j, raw10976 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10976step0 = (fun i j => raw10976 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10976step0 raw10976; decide +kernel
      have hl : raw10976step0Labels = raw10976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10976 raw10976Labels permutation434 hz
    mixedMoment B raw10976step0 raw10976step0Labels = mixedMoment B raw10976step1 raw10976step1Labels := by
      have hz : ∀ j, raw10976step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10976step1 = (fun i j => raw10976step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10976step1 raw10976step0; decide +kernel
      have hl : raw10976step1Labels = raw10976step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10976step0 raw10976step0Labels permutation80 hz
    mixedMoment B raw10976step1 raw10976step1Labels = mixedMoment B raw10976step2 raw10976step2Labels := by
      have ha : raw10976step2 = (fun i j => raw10976step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10976step2 raw10976step1; decide +kernel
      have hl : raw10976step2Labels = raw10976step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10976step1 raw10976step1Labels permutation10 permutation4
    mixedMoment B raw10976step2 raw10976step2Labels = mixedMoment B raw10976step3 raw10976step3Labels := by
      have ha : raw10976step3 = -raw10976step2 := by apply Matrix.ext; change ∀ i j, raw10976step3 i j = -(raw10976step2 i j); unfold raw10976step3 raw10976step2; decide +kernel
      have hl : raw10976step3Labels = raw10976step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10976step3 raw10976step3Labels = mixedMoment B raw10976step4 raw10976step4Labels := by
      have ha : raw10976step4 = raw10976step3 := by apply Matrix.ext; unfold raw10976step4 raw10976step3; decide +kernel
      have hl : raw10976step3Labels = labelEmbedding7 ∘ raw10976step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10976step3 raw10976step3Labels raw10976step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw10977 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw10977step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10977step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10977step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10977step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10977 raw10977Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw10977 raw10977Labels = mixedMoment B raw10977step0 raw10977step0Labels := by
      have hz : ∀ j, raw10977 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10977step0 = (fun i j => raw10977 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10977step0 raw10977; decide +kernel
      have hl : raw10977step0Labels = raw10977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10977 raw10977Labels permutation434 hz
    mixedMoment B raw10977step0 raw10977step0Labels = mixedMoment B raw10977step1 raw10977step1Labels := by
      have ha : raw10977step1 = (fun i j => raw10977step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10977step1 raw10977step0; decide +kernel
      have hl : raw10977step1Labels = raw10977step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10977step0 raw10977step0Labels permutation40 permutation4
    mixedMoment B raw10977step1 raw10977step1Labels = mixedMoment B raw10977step2 raw10977step2Labels := by
      have ha : raw10977step2 = -raw10977step1 := by apply Matrix.ext; change ∀ i j, raw10977step2 i j = -(raw10977step1 i j); unfold raw10977step2 raw10977step1; decide +kernel
      have hl : raw10977step2Labels = raw10977step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10977step2 raw10977step2Labels = mixedMoment B raw10977step3 raw10977step3Labels := by
      have ha : raw10977step3 = raw10977step2 := by apply Matrix.ext; unfold raw10977step3 raw10977step2; decide +kernel
      have hl : raw10977step2Labels = labelEmbedding7 ∘ raw10977step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10977step2 raw10977step2Labels raw10977step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw10978 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10978step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10978 raw10978Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw10978 raw10978Labels = mixedMoment B raw10978step0 raw10978step0Labels := by
      have hz : ∀ j, raw10978 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10978step0 = (fun i j => raw10978 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10978step0 raw10978; decide +kernel
      have hl : raw10978step0Labels = raw10978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10978 raw10978Labels permutation434 hz
    mixedMoment B raw10978step0 raw10978step0Labels = mixedMoment B raw10978step1 raw10978step1Labels := by
      have ha : raw10978step1 = (fun i j => raw10978step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10978step1 raw10978step0; decide +kernel
      have hl : raw10978step1Labels = raw10978step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10978step0 raw10978step0Labels permutation38 permutation6
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw10979 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10979step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10979step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10979step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10979 raw10979Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw10979 raw10979Labels = mixedMoment B raw10979step0 raw10979step0Labels := by
      have hz : ∀ j, raw10979 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10979step0 = (fun i j => raw10979 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10979step0 raw10979; decide +kernel
      have hl : raw10979step0Labels = raw10979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10979 raw10979Labels permutation434 hz
    mixedMoment B raw10979step0 raw10979step0Labels = mixedMoment B raw10979step1 raw10979step1Labels := by
      have hz : ∀ j, raw10979step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10979step1 = (fun i j => raw10979step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10979step1 raw10979step0; decide +kernel
      have hl : raw10979step1Labels = raw10979step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10979step0 raw10979step0Labels permutation80 hz
    mixedMoment B raw10979step1 raw10979step1Labels = mixedMoment B raw10979step2 raw10979step2Labels := by
      have ha : raw10979step2 = (fun i j => raw10979step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10979step2 raw10979step1; decide +kernel
      have hl : raw10979step2Labels = raw10979step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10979step1 raw10979step1Labels permutation8 permutation6
    _ = mixedMoment B node2776 node2776Labels := by rfl

def raw10980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10980Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10980step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10980step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10980step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw10980step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10980 raw10980Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw10980 raw10980Labels = mixedMoment B raw10980step0 raw10980step0Labels := by
      have hz : ∀ j, raw10980 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10980step0 = (fun i j => raw10980 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10980step0 raw10980; decide +kernel
      have hl : raw10980step0Labels = raw10980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10980 raw10980Labels permutation434 hz
    mixedMoment B raw10980step0 raw10980step0Labels = mixedMoment B raw10980step1 raw10980step1Labels := by
      have hz : ∀ j, raw10980step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10980step1 = (fun i j => raw10980step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10980step1 raw10980step0; decide +kernel
      have hl : raw10980step1Labels = raw10980step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10980step0 raw10980step0Labels permutation80 hz
    mixedMoment B raw10980step1 raw10980step1Labels = mixedMoment B raw10980step2 raw10980step2Labels := by
      have ha : raw10980step2 = (fun i j => raw10980step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10980step2 raw10980step1; decide +kernel
      have hl : raw10980step2Labels = raw10980step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10980step1 raw10980step1Labels permutation8 permutation6
    _ = mixedMoment B node1745 node1745Labels := by rfl

def raw10981 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10981Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10981step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw10981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10981 raw10981Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw10981 raw10981Labels = mixedMoment B raw10981step0 raw10981step0Labels := by
      have hz : ∀ j, raw10981 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10981step0 = (fun i j => raw10981 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10981step0 raw10981; decide +kernel
      have hl : raw10981step0Labels = raw10981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10981 raw10981Labels permutation434 hz
    mixedMoment B raw10981step0 raw10981step0Labels = mixedMoment B raw10981step1 raw10981step1Labels := by
      have ha : raw10981step1 = (fun i j => raw10981step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10981step1 raw10981step0; decide +kernel
      have hl : raw10981step1Labels = raw10981step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10981step0 raw10981step0Labels permutation38 permutation6
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw10982 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10982Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10982step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw10982step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10982 raw10982Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw10982 raw10982Labels = mixedMoment B raw10982step0 raw10982step0Labels := by
      have hz : ∀ j, raw10982 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10982step0 = (fun i j => raw10982 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10982step0 raw10982; decide +kernel
      have hl : raw10982step0Labels = raw10982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10982 raw10982Labels permutation346 hz
    mixedMoment B raw10982step0 raw10982step0Labels = mixedMoment B raw10982step1 raw10982step1Labels := by
      have ha : raw10982step1 = (fun i j => raw10982step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10982step1 raw10982step0; decide +kernel
      have hl : raw10982step1Labels = raw10982step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10982step0 raw10982step0Labels permutation38 permutation6
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw10983 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10983Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10983step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10983step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-1, 2, -1], ![-2, 1, 1]]
def raw10983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10983step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw10983step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10983 raw10983Labels = mixedMoment B node2282 node2282Labels := by
  calc
    mixedMoment B raw10983 raw10983Labels = mixedMoment B raw10983step0 raw10983step0Labels := by
      have hz : ∀ j, raw10983 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10983step0 = (fun i j => raw10983 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10983step0 raw10983; decide +kernel
      have hl : raw10983step0Labels = raw10983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10983 raw10983Labels permutation434 hz
    mixedMoment B raw10983step0 raw10983step0Labels = mixedMoment B raw10983step1 raw10983step1Labels := by
      have hz : ∀ j, raw10983step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10983step1 = (fun i j => raw10983step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10983step1 raw10983step0; decide +kernel
      have hl : raw10983step1Labels = raw10983step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10983step0 raw10983step0Labels permutation80 hz
    mixedMoment B raw10983step1 raw10983step1Labels = mixedMoment B raw10983step2 raw10983step2Labels := by
      have ha : raw10983step2 = (fun i j => raw10983step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10983step2 raw10983step1; decide +kernel
      have hl : raw10983step2Labels = raw10983step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10983step1 raw10983step1Labels permutation15 permutation3
    mixedMoment B raw10983step2 raw10983step2Labels = mixedMoment B raw10983step3 raw10983step3Labels := by
      have ha : raw10983step3 = -raw10983step2 := by apply Matrix.ext; change ∀ i j, raw10983step3 i j = -(raw10983step2 i j); unfold raw10983step3 raw10983step2; decide +kernel
      have hl : raw10983step3Labels = raw10983step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2282 node2282Labels := by rfl

def raw10984 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10984Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10984step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10984step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10984step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10984step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-1, 1, 0], ![-2, 2, 0]]
def raw10984step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10984step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw10984step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10984 raw10984Labels = mixedMoment B node2284 node2284Labels := by
  calc
    mixedMoment B raw10984 raw10984Labels = mixedMoment B raw10984step0 raw10984step0Labels := by
      have hz : ∀ j, raw10984 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10984step0 = (fun i j => raw10984 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10984step0 raw10984; decide +kernel
      have hl : raw10984step0Labels = raw10984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10984 raw10984Labels permutation434 hz
    mixedMoment B raw10984step0 raw10984step0Labels = mixedMoment B raw10984step1 raw10984step1Labels := by
      have hz : ∀ j, raw10984step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10984step1 = (fun i j => raw10984step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10984step1 raw10984step0; decide +kernel
      have hl : raw10984step1Labels = raw10984step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10984step0 raw10984step0Labels permutation80 hz
    mixedMoment B raw10984step1 raw10984step1Labels = mixedMoment B raw10984step2 raw10984step2Labels := by
      have ha : raw10984step2 = (fun i j => raw10984step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10984step2 raw10984step1; decide +kernel
      have hl : raw10984step2Labels = raw10984step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10984step1 raw10984step1Labels permutation14 permutation3
    mixedMoment B raw10984step2 raw10984step2Labels = mixedMoment B raw10984step3 raw10984step3Labels := by
      have ha : raw10984step3 = -raw10984step2 := by apply Matrix.ext; change ∀ i j, raw10984step3 i j = -(raw10984step2 i j); unfold raw10984step3 raw10984step2; decide +kernel
      have hl : raw10984step3Labels = raw10984step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2284 node2284Labels := by rfl

def raw10985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10985Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10985step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10985 raw10985Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw10985 raw10985Labels = mixedMoment B raw10985step0 raw10985step0Labels := by
      have hz : ∀ j, raw10985 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10985step0 = (fun i j => raw10985 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10985step0 raw10985; decide +kernel
      have hl : raw10985step0Labels = raw10985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10985 raw10985Labels permutation434 hz
    mixedMoment B raw10985step0 raw10985step0Labels = mixedMoment B raw10985step1 raw10985step1Labels := by
      have ha : raw10985step1 = (fun i j => raw10985step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10985step1 raw10985step0; decide +kernel
      have hl : raw10985step1Labels = raw10985step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10985step0 raw10985step0Labels permutation38 permutation6
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw10986 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10986Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10986step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10986 raw10986Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw10986 raw10986Labels = mixedMoment B raw10986step0 raw10986step0Labels := by
      have ha : raw10986step0 = (fun i j => raw10986 (permutation206 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10986step0 raw10986; decide +kernel
      have hl : raw10986step0Labels = raw10986Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10986 raw10986Labels permutation206 permutation6
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw10987 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10987Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10987step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw10987step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10987 raw10987Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw10987 raw10987Labels = mixedMoment B raw10987step0 raw10987step0Labels := by
      have hz : ∀ j, raw10987 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10987step0 = (fun i j => raw10987 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10987step0 raw10987; decide +kernel
      have hl : raw10987step0Labels = raw10987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10987 raw10987Labels permutation434 hz
    mixedMoment B raw10987step0 raw10987step0Labels = mixedMoment B raw10987step1 raw10987step1Labels := by
      have ha : raw10987step1 = (fun i j => raw10987step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10987step1 raw10987step0; decide +kernel
      have hl : raw10987step1Labels = raw10987step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10987step0 raw10987step0Labels permutation38 permutation6
    _ = mixedMoment B node2251 node2251Labels := by rfl

def raw10988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10988Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10988step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10988step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10988 raw10988Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw10988 raw10988Labels = mixedMoment B raw10988step0 raw10988step0Labels := by
      have hz : ∀ j, raw10988 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10988step0 = (fun i j => raw10988 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10988step0 raw10988; decide +kernel
      have hl : raw10988step0Labels = raw10988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10988 raw10988Labels permutation346 hz
    mixedMoment B raw10988step0 raw10988step0Labels = mixedMoment B raw10988step1 raw10988step1Labels := by
      have ha : raw10988step1 = (fun i j => raw10988step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10988step1 raw10988step0; decide +kernel
      have hl : raw10988step1Labels = raw10988step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10988step0 raw10988step0Labels permutation38 permutation6
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw10989 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10989Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10989step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10989 raw10989Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw10989 raw10989Labels = mixedMoment B raw10989step0 raw10989step0Labels := by
      have ha : raw10989step0 = (fun i j => raw10989 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10989step0 raw10989; decide +kernel
      have hl : raw10989step0Labels = raw10989Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10989 raw10989Labels permutation182 permutation6
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw10990 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10990Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw10990step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw10990step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10990 raw10990Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw10990 raw10990Labels = mixedMoment B raw10990step0 raw10990step0Labels := by
      have hz : ∀ j, raw10990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10990step0 = (fun i j => raw10990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10990step0 raw10990; decide +kernel
      have hl : raw10990step0Labels = raw10990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10990 raw10990Labels permutation346 hz
    mixedMoment B raw10990step0 raw10990step0Labels = mixedMoment B raw10990step1 raw10990step1Labels := by
      have ha : raw10990step1 = (fun i j => raw10990step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10990step1 raw10990step0; decide +kernel
      have hl : raw10990step1Labels = raw10990step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10990step0 raw10990step0Labels permutation38 permutation6
    _ = mixedMoment B node2251 node2251Labels := by rfl

def raw10991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10991Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10991step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10991step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10991step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10991step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10991step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10991 raw10991Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw10991 raw10991Labels = mixedMoment B raw10991step0 raw10991step0Labels := by
      have hz : ∀ j, raw10991 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10991step0 = (fun i j => raw10991 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10991step0 raw10991; decide +kernel
      have hl : raw10991step0Labels = raw10991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10991 raw10991Labels permutation434 hz
    mixedMoment B raw10991step0 raw10991step0Labels = mixedMoment B raw10991step1 raw10991step1Labels := by
      have hz : ∀ j, raw10991step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10991step1 = (fun i j => raw10991step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10991step1 raw10991step0; decide +kernel
      have hl : raw10991step1Labels = raw10991step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10991step0 raw10991step0Labels permutation80 hz
    mixedMoment B raw10991step1 raw10991step1Labels = mixedMoment B raw10991step2 raw10991step2Labels := by
      have ha : raw10991step2 = (fun i j => raw10991step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10991step2 raw10991step1; decide +kernel
      have hl : raw10991step2Labels = raw10991step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10991step1 raw10991step1Labels permutation8 permutation6
    _ = mixedMoment B node1739 node1739Labels := by rfl

def raw10992 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10992Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10992step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10992 raw10992Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw10992 raw10992Labels = mixedMoment B raw10992step0 raw10992step0Labels := by
      have hz : ∀ j, raw10992 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10992step0 = (fun i j => raw10992 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10992step0 raw10992; decide +kernel
      have hl : raw10992step0Labels = raw10992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10992 raw10992Labels permutation434 hz
    mixedMoment B raw10992step0 raw10992step0Labels = mixedMoment B raw10992step1 raw10992step1Labels := by
      have ha : raw10992step1 = (fun i j => raw10992step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10992step1 raw10992step0; decide +kernel
      have hl : raw10992step1Labels = raw10992step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10992step0 raw10992step0Labels permutation38 permutation6
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw10993 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw10993Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw10993step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw10993step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10993step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10993 raw10993Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw10993 raw10993Labels = mixedMoment B raw10993step0 raw10993step0Labels := by
      have hz : ∀ j, raw10993 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10993step0 = (fun i j => raw10993 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10993step0 raw10993; decide +kernel
      have hl : raw10993step0Labels = raw10993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10993 raw10993Labels permutation434 hz
    mixedMoment B raw10993step0 raw10993step0Labels = mixedMoment B raw10993step1 raw10993step1Labels := by
      have hz : ∀ j, raw10993step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10993step1 = (fun i j => raw10993step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10993step1 raw10993step0; decide +kernel
      have hl : raw10993step1Labels = raw10993step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10993step0 raw10993step0Labels permutation80 hz
    mixedMoment B raw10993step1 raw10993step1Labels = mixedMoment B raw10993step2 raw10993step2Labels := by
      have ha : raw10993step2 = (fun i j => raw10993step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10993step2 raw10993step1; decide +kernel
      have hl : raw10993step2Labels = raw10993step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10993step1 raw10993step1Labels permutation8 permutation6
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw10994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10994Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10994step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10994step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10994step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10994 raw10994Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw10994 raw10994Labels = mixedMoment B raw10994step0 raw10994step0Labels := by
      have hz : ∀ j, raw10994 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10994step0 = (fun i j => raw10994 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10994step0 raw10994; decide +kernel
      have hl : raw10994step0Labels = raw10994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10994 raw10994Labels permutation434 hz
    mixedMoment B raw10994step0 raw10994step0Labels = mixedMoment B raw10994step1 raw10994step1Labels := by
      have hz : ∀ j, raw10994step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10994step1 = (fun i j => raw10994step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10994step1 raw10994step0; decide +kernel
      have hl : raw10994step1Labels = raw10994step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10994step0 raw10994step0Labels permutation80 hz
    mixedMoment B raw10994step1 raw10994step1Labels = mixedMoment B raw10994step2 raw10994step2Labels := by
      have ha : raw10994step2 = (fun i j => raw10994step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10994step2 raw10994step1; decide +kernel
      have hl : raw10994step2Labels = raw10994step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10994step1 raw10994step1Labels permutation8 permutation6
    _ = mixedMoment B node1738 node1738Labels := by rfl

def raw10995 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10995Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10995step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10995 raw10995Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw10995 raw10995Labels = mixedMoment B raw10995step0 raw10995step0Labels := by
      have hz : ∀ j, raw10995 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10995step0 = (fun i j => raw10995 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10995step0 raw10995; decide +kernel
      have hl : raw10995step0Labels = raw10995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10995 raw10995Labels permutation434 hz
    mixedMoment B raw10995step0 raw10995step0Labels = mixedMoment B raw10995step1 raw10995step1Labels := by
      have ha : raw10995step1 = (fun i j => raw10995step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10995step1 raw10995step0; decide +kernel
      have hl : raw10995step1Labels = raw10995step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10995step0 raw10995step0Labels permutation38 permutation6
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw10996 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10996step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10996step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10996step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10996 raw10996Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw10996 raw10996Labels = mixedMoment B raw10996step0 raw10996step0Labels := by
      have hz : ∀ j, raw10996 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10996step0 = (fun i j => raw10996 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10996step0 raw10996; decide +kernel
      have hl : raw10996step0Labels = raw10996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10996 raw10996Labels permutation434 hz
    mixedMoment B raw10996step0 raw10996step0Labels = mixedMoment B raw10996step1 raw10996step1Labels := by
      have ha : raw10996step1 = (fun i j => raw10996step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10996step1 raw10996step0; decide +kernel
      have hl : raw10996step1Labels = raw10996step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10996step0 raw10996step0Labels permutation32 permutation7
    mixedMoment B raw10996step1 raw10996step1Labels = mixedMoment B raw10996step2 raw10996step2Labels := by
      have ha : raw10996step2 = raw10996step1 := by apply Matrix.ext; unfold raw10996step2 raw10996step1; decide +kernel
      have hl : raw10996step1Labels = labelEmbedding1 ∘ raw10996step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10996step1 raw10996step1Labels raw10996step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw10997 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10997step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10997step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw10997step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10997step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw10997step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10997 raw10997Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw10997 raw10997Labels = mixedMoment B raw10997step0 raw10997step0Labels := by
      have hz : ∀ j, raw10997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10997step0 = (fun i j => raw10997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10997step0 raw10997; decide +kernel
      have hl : raw10997step0Labels = raw10997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10997 raw10997Labels permutation434 hz
    mixedMoment B raw10997step0 raw10997step0Labels = mixedMoment B raw10997step1 raw10997step1Labels := by
      have hz : ∀ j, raw10997step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10997step1 = (fun i j => raw10997step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10997step1 raw10997step0; decide +kernel
      have hl : raw10997step1Labels = raw10997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10997step0 raw10997step0Labels permutation80 hz
    mixedMoment B raw10997step1 raw10997step1Labels = mixedMoment B raw10997step2 raw10997step2Labels := by
      have ha : raw10997step2 = (fun i j => raw10997step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10997step2 raw10997step1; decide +kernel
      have hl : raw10997step2Labels = raw10997step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10997step1 raw10997step1Labels permutation8 permutation7
    mixedMoment B raw10997step2 raw10997step2Labels = mixedMoment B raw10997step3 raw10997step3Labels := by
      have ha : raw10997step3 = raw10997step2 := by apply Matrix.ext; unfold raw10997step3 raw10997step2; decide +kernel
      have hl : raw10997step2Labels = labelEmbedding1 ∘ raw10997step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10997step2 raw10997step2Labels raw10997step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw10998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10998step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10998step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 2, -1], ![-3, 0, 3]]
def raw10998step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw10998step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10998step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw10998step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10998 raw10998Labels = mixedMoment B node1408 node1408Labels := by
  calc
    mixedMoment B raw10998 raw10998Labels = mixedMoment B raw10998step0 raw10998step0Labels := by
      have hz : ∀ j, raw10998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10998step0 = (fun i j => raw10998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10998step0 raw10998; decide +kernel
      have hl : raw10998step0Labels = raw10998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10998 raw10998Labels permutation434 hz
    mixedMoment B raw10998step0 raw10998step0Labels = mixedMoment B raw10998step1 raw10998step1Labels := by
      have hz : ∀ j, raw10998step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10998step1 = (fun i j => raw10998step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10998step1 raw10998step0; decide +kernel
      have hl : raw10998step1Labels = raw10998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10998step0 raw10998step0Labels permutation80 hz
    mixedMoment B raw10998step1 raw10998step1Labels = mixedMoment B raw10998step2 raw10998step2Labels := by
      have ha : raw10998step2 = (fun i j => raw10998step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10998step2 raw10998step1; decide +kernel
      have hl : raw10998step2Labels = raw10998step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10998step1 raw10998step1Labels permutation11 permutation5
    mixedMoment B raw10998step2 raw10998step2Labels = mixedMoment B raw10998step3 raw10998step3Labels := by
      have ha : raw10998step3 = -raw10998step2 := by apply Matrix.ext; change ∀ i j, raw10998step3 i j = -(raw10998step2 i j); unfold raw10998step3 raw10998step2; decide +kernel
      have hl : raw10998step3Labels = raw10998step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10998step3 raw10998step3Labels = mixedMoment B raw10998step4 raw10998step4Labels := by
      have ha : raw10998step4 = raw10998step3 := by apply Matrix.ext; unfold raw10998step4 raw10998step3; decide +kernel
      have hl : raw10998step3Labels = labelEmbedding1 ∘ raw10998step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10998step3 raw10998step3Labels raw10998step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1408 node1408Labels := by rfl

def raw10999 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw10999step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10999 raw10999Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw10999 raw10999Labels = mixedMoment B raw10999step0 raw10999step0Labels := by
      have hz : ∀ j, raw10999 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10999step0 = (fun i j => raw10999 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10999step0 raw10999; decide +kernel
      have hl : raw10999step0Labels = raw10999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10999 raw10999Labels permutation434 hz
    mixedMoment B raw10999step0 raw10999step0Labels = mixedMoment B raw10999step1 raw10999step1Labels := by
      have ha : raw10999step1 = (fun i j => raw10999step0 (permutation79 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10999step1 raw10999step0; decide +kernel
      have hl : raw10999step1Labels = raw10999step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10999step0 raw10999step0Labels permutation79 permutation5
    mixedMoment B raw10999step1 raw10999step1Labels = mixedMoment B raw10999step2 raw10999step2Labels := by
      have ha : raw10999step2 = raw10999step1 := by apply Matrix.ext; unfold raw10999step2 raw10999step1; decide +kernel
      have hl : raw10999step1Labels = labelEmbedding1 ∘ raw10999step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10999step1 raw10999step1Labels raw10999step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2092 node2092Labels := by rfl

def raw11000 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11000step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11000 raw11000Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw11000 raw11000Labels = mixedMoment B raw11000step0 raw11000step0Labels := by
      have hz : ∀ j, raw11000 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11000step0 = (fun i j => raw11000 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11000step0 raw11000; decide +kernel
      have hl : raw11000step0Labels = raw11000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11000 raw11000Labels permutation346 hz
    mixedMoment B raw11000step0 raw11000step0Labels = mixedMoment B raw11000step1 raw11000step1Labels := by
      have ha : raw11000step1 = (fun i j => raw11000step0 (permutation79 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11000step1 raw11000step0; decide +kernel
      have hl : raw11000step1Labels = raw11000step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11000step0 raw11000step0Labels permutation79 permutation5
    mixedMoment B raw11000step1 raw11000step1Labels = mixedMoment B raw11000step2 raw11000step2Labels := by
      have ha : raw11000step2 = raw11000step1 := by apply Matrix.ext; unfold raw11000step2 raw11000step1; decide +kernel
      have hl : raw11000step1Labels = labelEmbedding1 ∘ raw11000step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11000step1 raw11000step1Labels raw11000step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2092 node2092Labels := by rfl

def raw11001 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11001step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw11001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11001step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw11001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11001 raw11001Labels = mixedMoment B node2113 node2113Labels := by
  calc
    mixedMoment B raw11001 raw11001Labels = mixedMoment B raw11001step0 raw11001step0Labels := by
      have hz : ∀ j, raw11001 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11001step0 = (fun i j => raw11001 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11001step0 raw11001; decide +kernel
      have hl : raw11001step0Labels = raw11001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11001 raw11001Labels permutation434 hz
    mixedMoment B raw11001step0 raw11001step0Labels = mixedMoment B raw11001step1 raw11001step1Labels := by
      have hz : ∀ j, raw11001step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11001step1 = (fun i j => raw11001step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11001step1 raw11001step0; decide +kernel
      have hl : raw11001step1Labels = raw11001step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11001step0 raw11001step0Labels permutation80 hz
    mixedMoment B raw11001step1 raw11001step1Labels = mixedMoment B raw11001step2 raw11001step2Labels := by
      have ha : raw11001step2 = (fun i j => raw11001step1 (permutation19 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11001step2 raw11001step1; decide +kernel
      have hl : raw11001step2Labels = raw11001step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11001step1 raw11001step1Labels permutation19 permutation5
    mixedMoment B raw11001step2 raw11001step2Labels = mixedMoment B raw11001step3 raw11001step3Labels := by
      have ha : raw11001step3 = raw11001step2 := by apply Matrix.ext; unfold raw11001step3 raw11001step2; decide +kernel
      have hl : raw11001step2Labels = labelEmbedding1 ∘ raw11001step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11001step2 raw11001step2Labels raw11001step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2113 node2113Labels := by rfl

def raw11002 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11002step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw11002step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw11002step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11002step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw11002step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11002 raw11002Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw11002 raw11002Labels = mixedMoment B raw11002step0 raw11002step0Labels := by
      have hz : ∀ j, raw11002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11002step0 = (fun i j => raw11002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11002step0 raw11002; decide +kernel
      have hl : raw11002step0Labels = raw11002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11002 raw11002Labels permutation434 hz
    mixedMoment B raw11002step0 raw11002step0Labels = mixedMoment B raw11002step1 raw11002step1Labels := by
      have hz : ∀ j, raw11002step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw11002step1 = (fun i j => raw11002step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw11002step1 raw11002step0; decide +kernel
      have hl : raw11002step1Labels = raw11002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11002step0 raw11002step0Labels permutation80 hz
    mixedMoment B raw11002step1 raw11002step1Labels = mixedMoment B raw11002step2 raw11002step2Labels := by
      have ha : raw11002step2 = (fun i j => raw11002step1 (permutation17 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11002step2 raw11002step1; decide +kernel
      have hl : raw11002step2Labels = raw11002step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11002step1 raw11002step1Labels permutation17 permutation5
    mixedMoment B raw11002step2 raw11002step2Labels = mixedMoment B raw11002step3 raw11002step3Labels := by
      have ha : raw11002step3 = raw11002step2 := by apply Matrix.ext; unfold raw11002step3 raw11002step2; decide +kernel
      have hl : raw11002step2Labels = labelEmbedding1 ∘ raw11002step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11002step2 raw11002step2Labels raw11002step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw11003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11003step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw11003step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11003step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11003step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11003 raw11003Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw11003 raw11003Labels = mixedMoment B raw11003step0 raw11003step0Labels := by
      have hz : ∀ j, raw11003 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11003step0 = (fun i j => raw11003 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11003step0 raw11003; decide +kernel
      have hl : raw11003step0Labels = raw11003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11003 raw11003Labels permutation434 hz
    mixedMoment B raw11003step0 raw11003step0Labels = mixedMoment B raw11003step1 raw11003step1Labels := by
      have ha : raw11003step1 = (fun i j => raw11003step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11003step1 raw11003step0; decide +kernel
      have hl : raw11003step1Labels = raw11003step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11003step0 raw11003step0Labels permutation49 permutation5
    mixedMoment B raw11003step1 raw11003step1Labels = mixedMoment B raw11003step2 raw11003step2Labels := by
      have ha : raw11003step2 = -raw11003step1 := by apply Matrix.ext; change ∀ i j, raw11003step2 i j = -(raw11003step1 i j); unfold raw11003step2 raw11003step1; decide +kernel
      have hl : raw11003step2Labels = raw11003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11003step2 raw11003step2Labels = mixedMoment B raw11003step3 raw11003step3Labels := by
      have ha : raw11003step3 = raw11003step2 := by apply Matrix.ext; unfold raw11003step3 raw11003step2; decide +kernel
      have hl : raw11003step2Labels = labelEmbedding1 ∘ raw11003step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11003step2 raw11003step2Labels raw11003step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1406 node1406Labels := by rfl

def raw11004 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw11004step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11004step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11004 raw11004Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw11004 raw11004Labels = mixedMoment B raw11004step0 raw11004step0Labels := by
      have ha : raw11004step0 = (fun i j => raw11004 (permutation217 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11004step0 raw11004; decide +kernel
      have hl : raw11004step0Labels = raw11004Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11004 raw11004Labels permutation217 permutation5
    mixedMoment B raw11004step0 raw11004step0Labels = mixedMoment B raw11004step1 raw11004step1Labels := by
      have ha : raw11004step1 = -raw11004step0 := by apply Matrix.ext; change ∀ i j, raw11004step1 i j = -(raw11004step0 i j); unfold raw11004step1 raw11004step0; decide +kernel
      have hl : raw11004step1Labels = raw11004step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11004step1 raw11004step1Labels = mixedMoment B raw11004step2 raw11004step2Labels := by
      have ha : raw11004step2 = raw11004step1 := by apply Matrix.ext; unfold raw11004step2 raw11004step1; decide +kernel
      have hl : raw11004step1Labels = labelEmbedding1 ∘ raw11004step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11004step1 raw11004step1Labels raw11004step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3202 node3202Labels := by rfl

def raw11005 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11005Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw11005step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw11005step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11005step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11005step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11005step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11005 raw11005Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw11005 raw11005Labels = mixedMoment B raw11005step0 raw11005step0Labels := by
      have hz : ∀ j, raw11005 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11005step0 = (fun i j => raw11005 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11005step0 raw11005; decide +kernel
      have hl : raw11005step0Labels = raw11005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11005 raw11005Labels permutation434 hz
    mixedMoment B raw11005step0 raw11005step0Labels = mixedMoment B raw11005step1 raw11005step1Labels := by
      have ha : raw11005step1 = (fun i j => raw11005step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11005step1 raw11005step0; decide +kernel
      have hl : raw11005step1Labels = raw11005step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11005step0 raw11005step0Labels permutation49 permutation5
    mixedMoment B raw11005step1 raw11005step1Labels = mixedMoment B raw11005step2 raw11005step2Labels := by
      have ha : raw11005step2 = -raw11005step1 := by apply Matrix.ext; change ∀ i j, raw11005step2 i j = -(raw11005step1 i j); unfold raw11005step2 raw11005step1; decide +kernel
      have hl : raw11005step2Labels = raw11005step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11005step2 raw11005step2Labels = mixedMoment B raw11005step3 raw11005step3Labels := by
      have ha : raw11005step3 = raw11005step2 := by apply Matrix.ext; unfold raw11005step3 raw11005step2; decide +kernel
      have hl : raw11005step2Labels = labelEmbedding1 ∘ raw11005step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11005step2 raw11005step2Labels raw11005step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3180 node3180Labels := by rfl

def raw11006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11006Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11006step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw11006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11006step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11006step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11006step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11006 raw11006Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw11006 raw11006Labels = mixedMoment B raw11006step0 raw11006step0Labels := by
      have hz : ∀ j, raw11006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11006step0 = (fun i j => raw11006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11006step0 raw11006; decide +kernel
      have hl : raw11006step0Labels = raw11006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11006 raw11006Labels permutation346 hz
    mixedMoment B raw11006step0 raw11006step0Labels = mixedMoment B raw11006step1 raw11006step1Labels := by
      have ha : raw11006step1 = (fun i j => raw11006step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11006step1 raw11006step0; decide +kernel
      have hl : raw11006step1Labels = raw11006step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11006step0 raw11006step0Labels permutation49 permutation5
    mixedMoment B raw11006step1 raw11006step1Labels = mixedMoment B raw11006step2 raw11006step2Labels := by
      have ha : raw11006step2 = -raw11006step1 := by apply Matrix.ext; change ∀ i j, raw11006step2 i j = -(raw11006step1 i j); unfold raw11006step2 raw11006step1; decide +kernel
      have hl : raw11006step2Labels = raw11006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11006step2 raw11006step2Labels = mixedMoment B raw11006step3 raw11006step3Labels := by
      have ha : raw11006step3 = raw11006step2 := by apply Matrix.ext; unfold raw11006step3 raw11006step2; decide +kernel
      have hl : raw11006step2Labels = labelEmbedding1 ∘ raw11006step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11006step2 raw11006step2Labels raw11006step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1406 node1406Labels := by rfl

def raw11007 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw11007Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw11007step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11007step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11007step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11007step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw11007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11007 raw11007Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw11007 raw11007Labels = mixedMoment B raw11007step0 raw11007step0Labels := by
      have ha : raw11007step0 = (fun i j => raw11007 (permutation193 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11007step0 raw11007; decide +kernel
      have hl : raw11007step0Labels = raw11007Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11007 raw11007Labels permutation193 permutation5
    mixedMoment B raw11007step0 raw11007step0Labels = mixedMoment B raw11007step1 raw11007step1Labels := by
      have ha : raw11007step1 = -raw11007step0 := by apply Matrix.ext; change ∀ i j, raw11007step1 i j = -(raw11007step0 i j); unfold raw11007step1 raw11007step0; decide +kernel
      have hl : raw11007step1Labels = raw11007step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11007step1 raw11007step1Labels = mixedMoment B raw11007step2 raw11007step2Labels := by
      have ha : raw11007step2 = raw11007step1 := by apply Matrix.ext; unfold raw11007step2 raw11007step1; decide +kernel
      have hl : raw11007step1Labels = labelEmbedding1 ∘ raw11007step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11007step1 raw11007step1Labels raw11007step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3202 node3202Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
