import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw32896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw32896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw32896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw32896step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32896step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32896step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32896step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32896 raw32896Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw32896 raw32896Labels = mixedMoment B raw32896step0 raw32896step0Labels := by
      have hz : ∀ j, raw32896 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32896step0 = (fun i j => raw32896 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32896step0 raw32896; decide +kernel
      have hl : raw32896step0Labels = raw32896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32896 raw32896Labels permutation434 hz
    mixedMoment B raw32896step0 raw32896step0Labels = mixedMoment B raw32896step1 raw32896step1Labels := by
      have ha : raw32896step1 = (fun i j => raw32896step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32896step1 raw32896step0; decide +kernel
      have hl : raw32896step1Labels = raw32896step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32896step0 raw32896step0Labels permutation151 permutation3
    mixedMoment B raw32896step1 raw32896step1Labels = mixedMoment B raw32896step2 raw32896step2Labels := by
      have ha : raw32896step2 = -raw32896step1 := by apply Matrix.ext; change ∀ i j, raw32896step2 i j = -(raw32896step1 i j); unfold raw32896step2 raw32896step1; decide +kernel
      have hl : raw32896step2Labels = raw32896step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32896step2 raw32896step2Labels = mixedMoment B raw32896step3 raw32896step3Labels := by
      have ha : raw32896step3 = raw32896step2 := by apply Matrix.ext; unfold raw32896step3 raw32896step2; decide +kernel
      have hl : raw32896step2Labels = labelEmbedding6 ∘ raw32896step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32896step2 raw32896step2Labels raw32896step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw32897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -2, -1]]
def raw32897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw32897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw32897step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32897step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32897step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32897step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32897 raw32897Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw32897 raw32897Labels = mixedMoment B raw32897step0 raw32897step0Labels := by
      have hz : ∀ j, raw32897 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32897step0 = (fun i j => raw32897 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32897step0 raw32897; decide +kernel
      have hl : raw32897step0Labels = raw32897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32897 raw32897Labels permutation520 hz
    mixedMoment B raw32897step0 raw32897step0Labels = mixedMoment B raw32897step1 raw32897step1Labels := by
      have ha : raw32897step1 = (fun i j => raw32897step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32897step1 raw32897step0; decide +kernel
      have hl : raw32897step1Labels = raw32897step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32897step0 raw32897step0Labels permutation151 permutation3
    mixedMoment B raw32897step1 raw32897step1Labels = mixedMoment B raw32897step2 raw32897step2Labels := by
      have ha : raw32897step2 = -raw32897step1 := by apply Matrix.ext; change ∀ i j, raw32897step2 i j = -(raw32897step1 i j); unfold raw32897step2 raw32897step1; decide +kernel
      have hl : raw32897step2Labels = raw32897step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32897step2 raw32897step2Labels = mixedMoment B raw32897step3 raw32897step3Labels := by
      have ha : raw32897step3 = raw32897step2 := by apply Matrix.ext; unfold raw32897step3 raw32897step2; decide +kernel
      have hl : raw32897step2Labels = labelEmbedding6 ∘ raw32897step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32897step2 raw32897step2Labels raw32897step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw32898 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32898step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32898step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32898 raw32898Labels = mixedMoment B node5148 node5148Labels := by
  calc
    mixedMoment B raw32898 raw32898Labels = mixedMoment B raw32898step0 raw32898step0Labels := by
      have ha : raw32898step0 = (fun i j => raw32898 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32898step0 raw32898; decide +kernel
      have hl : raw32898step0Labels = raw32898Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32898 raw32898Labels permutation152 permutation7
    mixedMoment B raw32898step0 raw32898step0Labels = mixedMoment B raw32898step1 raw32898step1Labels := by
      have ha : raw32898step1 = raw32898step0 := by apply Matrix.ext; unfold raw32898step1 raw32898step0; decide +kernel
      have hl : raw32898step0Labels = labelEmbedding10 ∘ raw32898step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32898step0 raw32898step0Labels raw32898step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5148 node5148Labels := by rfl

def raw32899 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32899step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32899step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32899 raw32899Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw32899 raw32899Labels = mixedMoment B raw32899step0 raw32899step0Labels := by
      have ha : raw32899step0 = (fun i j => raw32899 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32899step0 raw32899; decide +kernel
      have hl : raw32899step0Labels = raw32899Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32899 raw32899Labels permutation152 permutation7
    mixedMoment B raw32899step0 raw32899step0Labels = mixedMoment B raw32899step1 raw32899step1Labels := by
      have ha : raw32899step1 = raw32899step0 := by apply Matrix.ext; unfold raw32899step1 raw32899step0; decide +kernel
      have hl : raw32899step0Labels = labelEmbedding10 ∘ raw32899step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32899step0 raw32899step0Labels raw32899step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5085 node5085Labels := by rfl

def raw32900 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32900step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32900 raw32900Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw32900 raw32900Labels = mixedMoment B raw32900step0 raw32900step0Labels := by
      have ha : raw32900step0 = (fun i j => raw32900 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32900step0 raw32900; decide +kernel
      have hl : raw32900step0Labels = raw32900Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32900 raw32900Labels permutation154 permutation7
    mixedMoment B raw32900step0 raw32900step0Labels = mixedMoment B raw32900step1 raw32900step1Labels := by
      have ha : raw32900step1 = raw32900step0 := by apply Matrix.ext; unfold raw32900step1 raw32900step0; decide +kernel
      have hl : raw32900step0Labels = labelEmbedding10 ∘ raw32900step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32900step0 raw32900step0Labels raw32900step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw32901 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32901step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32901step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32901step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32901 raw32901Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw32901 raw32901Labels = mixedMoment B raw32901step0 raw32901step0Labels := by
      have ha : raw32901step0 = (fun i j => raw32901 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32901step0 raw32901; decide +kernel
      have hl : raw32901step0Labels = raw32901Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32901 raw32901Labels permutation152 permutation7
    mixedMoment B raw32901step0 raw32901step0Labels = mixedMoment B raw32901step1 raw32901step1Labels := by
      have ha : raw32901step1 = raw32901step0 := by apply Matrix.ext; unfold raw32901step1 raw32901step0; decide +kernel
      have hl : raw32901step0Labels = labelEmbedding10 ∘ raw32901step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32901step0 raw32901step0Labels raw32901step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw32902 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32902step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32902step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32902step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32902step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32902 raw32902Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw32902 raw32902Labels = mixedMoment B raw32902step0 raw32902step0Labels := by
      have ha : raw32902step0 = (fun i j => raw32902 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32902step0 raw32902; decide +kernel
      have hl : raw32902step0Labels = raw32902Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32902 raw32902Labels permutation176 permutation4
    mixedMoment B raw32902step0 raw32902step0Labels = mixedMoment B raw32902step1 raw32902step1Labels := by
      have ha : raw32902step1 = -raw32902step0 := by apply Matrix.ext; change ∀ i j, raw32902step1 i j = -(raw32902step0 i j); unfold raw32902step1 raw32902step0; decide +kernel
      have hl : raw32902step1Labels = raw32902step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32902step1 raw32902step1Labels = mixedMoment B raw32902step2 raw32902step2Labels := by
      have ha : raw32902step2 = raw32902step1 := by apply Matrix.ext; unfold raw32902step2 raw32902step1; decide +kernel
      have hl : raw32902step1Labels = labelEmbedding7 ∘ raw32902step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32902step1 raw32902step1Labels raw32902step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

def raw32903 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32903step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32903 raw32903Labels = mixedMoment B node5179 node5179Labels := by
  calc
    mixedMoment B raw32903 raw32903Labels = mixedMoment B raw32903step0 raw32903step0Labels := by
      have ha : raw32903step0 = (fun i j => raw32903 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32903step0 raw32903; decide +kernel
      have hl : raw32903step0Labels = raw32903Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32903 raw32903Labels permutation152 permutation6
    mixedMoment B raw32903step0 raw32903step0Labels = mixedMoment B raw32903step1 raw32903step1Labels := by
      have ha : raw32903step1 = raw32903step0 := by apply Matrix.ext; unfold raw32903step1 raw32903step0; decide +kernel
      have hl : raw32903step0Labels = labelEmbedding9 ∘ raw32903step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32903step0 raw32903step0Labels raw32903step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5179 node5179Labels := by rfl

def raw32904 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32904step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32904 raw32904Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw32904 raw32904Labels = mixedMoment B raw32904step0 raw32904step0Labels := by
      have ha : raw32904step0 = (fun i j => raw32904 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32904step0 raw32904; decide +kernel
      have hl : raw32904step0Labels = raw32904Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32904 raw32904Labels permutation152 permutation6
    mixedMoment B raw32904step0 raw32904step0Labels = mixedMoment B raw32904step1 raw32904step1Labels := by
      have ha : raw32904step1 = raw32904step0 := by apply Matrix.ext; unfold raw32904step1 raw32904step0; decide +kernel
      have hl : raw32904step0Labels = labelEmbedding9 ∘ raw32904step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32904step0 raw32904step0Labels raw32904step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw32905 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32905step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32905 raw32905Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw32905 raw32905Labels = mixedMoment B raw32905step0 raw32905step0Labels := by
      have ha : raw32905step0 = (fun i j => raw32905 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32905step0 raw32905; decide +kernel
      have hl : raw32905step0Labels = raw32905Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32905 raw32905Labels permutation154 permutation6
    mixedMoment B raw32905step0 raw32905step0Labels = mixedMoment B raw32905step1 raw32905step1Labels := by
      have ha : raw32905step1 = raw32905step0 := by apply Matrix.ext; unfold raw32905step1 raw32905step0; decide +kernel
      have hl : raw32905step0Labels = labelEmbedding9 ∘ raw32905step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32905step0 raw32905step0Labels raw32905step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw32906 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw32906step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32906step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32906step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32906step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32906step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32906 raw32906Labels = mixedMoment B node4787 node4787Labels := by
  calc
    mixedMoment B raw32906 raw32906Labels = mixedMoment B raw32906step0 raw32906step0Labels := by
      have ha : raw32906step0 = (fun i j => raw32906 (permutation179 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32906step0 raw32906; decide +kernel
      have hl : raw32906step0Labels = raw32906Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32906 raw32906Labels permutation179 permutation4
    mixedMoment B raw32906step0 raw32906step0Labels = mixedMoment B raw32906step1 raw32906step1Labels := by
      have ha : raw32906step1 = -raw32906step0 := by apply Matrix.ext; change ∀ i j, raw32906step1 i j = -(raw32906step0 i j); unfold raw32906step1 raw32906step0; decide +kernel
      have hl : raw32906step1Labels = raw32906step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32906step1 raw32906step1Labels = mixedMoment B raw32906step2 raw32906step2Labels := by
      have ha : raw32906step2 = raw32906step1 := by apply Matrix.ext; unfold raw32906step2 raw32906step1; decide +kernel
      have hl : raw32906step1Labels = labelEmbedding7 ∘ raw32906step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32906step1 raw32906step1Labels raw32906step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4787 node4787Labels := by rfl

def raw32907 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32907step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32907step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32907step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32907 raw32907Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw32907 raw32907Labels = mixedMoment B raw32907step0 raw32907step0Labels := by
      have ha : raw32907step0 = (fun i j => raw32907 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32907step0 raw32907; decide +kernel
      have hl : raw32907step0Labels = raw32907Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32907 raw32907Labels permutation154 permutation6
    mixedMoment B raw32907step0 raw32907step0Labels = mixedMoment B raw32907step1 raw32907step1Labels := by
      have ha : raw32907step1 = raw32907step0 := by apply Matrix.ext; unfold raw32907step1 raw32907step0; decide +kernel
      have hl : raw32907step0Labels = labelEmbedding9 ∘ raw32907step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32907step0 raw32907step0Labels raw32907step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5059 node5059Labels := by rfl

def raw32908 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32908step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32908step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32908 raw32908Labels = mixedMoment B node5124 node5124Labels := by
  calc
    mixedMoment B raw32908 raw32908Labels = mixedMoment B raw32908step0 raw32908step0Labels := by
      have ha : raw32908step0 = (fun i j => raw32908 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32908step0 raw32908; decide +kernel
      have hl : raw32908step0Labels = raw32908Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32908 raw32908Labels permutation154 permutation6
    mixedMoment B raw32908step0 raw32908step0Labels = mixedMoment B raw32908step1 raw32908step1Labels := by
      have ha : raw32908step1 = raw32908step0 := by apply Matrix.ext; unfold raw32908step1 raw32908step0; decide +kernel
      have hl : raw32908step0Labels = labelEmbedding9 ∘ raw32908step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32908step0 raw32908step0Labels raw32908step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5124 node5124Labels := by rfl

def raw32909 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32909step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32909step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32909 raw32909Labels = mixedMoment B node5135 node5135Labels := by
  calc
    mixedMoment B raw32909 raw32909Labels = mixedMoment B raw32909step0 raw32909step0Labels := by
      have ha : raw32909step0 = (fun i j => raw32909 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32909step0 raw32909; decide +kernel
      have hl : raw32909step0Labels = raw32909Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32909 raw32909Labels permutation154 permutation6
    mixedMoment B raw32909step0 raw32909step0Labels = mixedMoment B raw32909step1 raw32909step1Labels := by
      have ha : raw32909step1 = raw32909step0 := by apply Matrix.ext; unfold raw32909step1 raw32909step0; decide +kernel
      have hl : raw32909step0Labels = labelEmbedding9 ∘ raw32909step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32909step0 raw32909step0Labels raw32909step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5135 node5135Labels := by rfl

def raw32910 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw32910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw32910step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32910step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32910step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32910step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32910step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32910 raw32910Labels = mixedMoment B node4787 node4787Labels := by
  calc
    mixedMoment B raw32910 raw32910Labels = mixedMoment B raw32910step0 raw32910step0Labels := by
      have ha : raw32910step0 = (fun i j => raw32910 (permutation177 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32910step0 raw32910; decide +kernel
      have hl : raw32910step0Labels = raw32910Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32910 raw32910Labels permutation177 permutation4
    mixedMoment B raw32910step0 raw32910step0Labels = mixedMoment B raw32910step1 raw32910step1Labels := by
      have ha : raw32910step1 = -raw32910step0 := by apply Matrix.ext; change ∀ i j, raw32910step1 i j = -(raw32910step0 i j); unfold raw32910step1 raw32910step0; decide +kernel
      have hl : raw32910step1Labels = raw32910step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32910step1 raw32910step1Labels = mixedMoment B raw32910step2 raw32910step2Labels := by
      have ha : raw32910step2 = raw32910step1 := by apply Matrix.ext; unfold raw32910step2 raw32910step1; decide +kernel
      have hl : raw32910step1Labels = labelEmbedding7 ∘ raw32910step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32910step1 raw32910step1Labels raw32910step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4787 node4787Labels := by rfl

def raw32911 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw32911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32911step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32911step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32911step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32911 raw32911Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw32911 raw32911Labels = mixedMoment B raw32911step0 raw32911step0Labels := by
      have ha : raw32911step0 = (fun i j => raw32911 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32911step0 raw32911; decide +kernel
      have hl : raw32911step0Labels = raw32911Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32911 raw32911Labels permutation152 permutation6
    mixedMoment B raw32911step0 raw32911step0Labels = mixedMoment B raw32911step1 raw32911step1Labels := by
      have ha : raw32911step1 = raw32911step0 := by apply Matrix.ext; unfold raw32911step1 raw32911step0; decide +kernel
      have hl : raw32911step0Labels = labelEmbedding9 ∘ raw32911step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32911step0 raw32911step0Labels raw32911step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5059 node5059Labels := by rfl

def raw32912 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw32912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32912step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32912step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32912 raw32912Labels = mixedMoment B node5124 node5124Labels := by
  calc
    mixedMoment B raw32912 raw32912Labels = mixedMoment B raw32912step0 raw32912step0Labels := by
      have ha : raw32912step0 = (fun i j => raw32912 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32912step0 raw32912; decide +kernel
      have hl : raw32912step0Labels = raw32912Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32912 raw32912Labels permutation152 permutation6
    mixedMoment B raw32912step0 raw32912step0Labels = mixedMoment B raw32912step1 raw32912step1Labels := by
      have ha : raw32912step1 = raw32912step0 := by apply Matrix.ext; unfold raw32912step1 raw32912step0; decide +kernel
      have hl : raw32912step0Labels = labelEmbedding9 ∘ raw32912step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32912step0 raw32912step0Labels raw32912step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5124 node5124Labels := by rfl

def raw32913 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw32913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32913step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32913step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32913 raw32913Labels = mixedMoment B node5135 node5135Labels := by
  calc
    mixedMoment B raw32913 raw32913Labels = mixedMoment B raw32913step0 raw32913step0Labels := by
      have ha : raw32913step0 = (fun i j => raw32913 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32913step0 raw32913; decide +kernel
      have hl : raw32913step0Labels = raw32913Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32913 raw32913Labels permutation152 permutation6
    mixedMoment B raw32913step0 raw32913step0Labels = mixedMoment B raw32913step1 raw32913step1Labels := by
      have ha : raw32913step1 = raw32913step0 := by apply Matrix.ext; unfold raw32913step1 raw32913step0; decide +kernel
      have hl : raw32913step0Labels = labelEmbedding9 ∘ raw32913step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32913step0 raw32913step0Labels raw32913step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5135 node5135Labels := by rfl

def raw32914 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw32914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32914step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32914step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32914step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32914step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32914step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32914 raw32914Labels = mixedMoment B node4786 node4786Labels := by
  calc
    mixedMoment B raw32914 raw32914Labels = mixedMoment B raw32914step0 raw32914step0Labels := by
      have ha : raw32914step0 = (fun i j => raw32914 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32914step0 raw32914; decide +kernel
      have hl : raw32914step0Labels = raw32914Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32914 raw32914Labels permutation176 permutation4
    mixedMoment B raw32914step0 raw32914step0Labels = mixedMoment B raw32914step1 raw32914step1Labels := by
      have ha : raw32914step1 = -raw32914step0 := by apply Matrix.ext; change ∀ i j, raw32914step1 i j = -(raw32914step0 i j); unfold raw32914step1 raw32914step0; decide +kernel
      have hl : raw32914step1Labels = raw32914step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32914step1 raw32914step1Labels = mixedMoment B raw32914step2 raw32914step2Labels := by
      have ha : raw32914step2 = raw32914step1 := by apply Matrix.ext; unfold raw32914step2 raw32914step1; decide +kernel
      have hl : raw32914step1Labels = labelEmbedding7 ∘ raw32914step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32914step1 raw32914step1Labels raw32914step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4786 node4786Labels := by rfl

def raw32915 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw32915Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32915step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32915step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32915step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32915 raw32915Labels = mixedMoment B node5058 node5058Labels := by
  calc
    mixedMoment B raw32915 raw32915Labels = mixedMoment B raw32915step0 raw32915step0Labels := by
      have ha : raw32915step0 = (fun i j => raw32915 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32915step0 raw32915; decide +kernel
      have hl : raw32915step0Labels = raw32915Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32915 raw32915Labels permutation152 permutation6
    mixedMoment B raw32915step0 raw32915step0Labels = mixedMoment B raw32915step1 raw32915step1Labels := by
      have ha : raw32915step1 = raw32915step0 := by apply Matrix.ext; unfold raw32915step1 raw32915step0; decide +kernel
      have hl : raw32915step0Labels = labelEmbedding9 ∘ raw32915step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32915step0 raw32915step0Labels raw32915step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5058 node5058Labels := by rfl

def raw32916 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw32916Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32916step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32916step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32916 raw32916Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw32916 raw32916Labels = mixedMoment B raw32916step0 raw32916step0Labels := by
      have ha : raw32916step0 = (fun i j => raw32916 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32916step0 raw32916; decide +kernel
      have hl : raw32916step0Labels = raw32916Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32916 raw32916Labels permutation152 permutation6
    mixedMoment B raw32916step0 raw32916step0Labels = mixedMoment B raw32916step1 raw32916step1Labels := by
      have ha : raw32916step1 = raw32916step0 := by apply Matrix.ext; unfold raw32916step1 raw32916step0; decide +kernel
      have hl : raw32916step0Labels = labelEmbedding9 ∘ raw32916step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32916step0 raw32916step0Labels raw32916step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

def raw32917 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw32917Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32917step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32917step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32917 raw32917Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw32917 raw32917Labels = mixedMoment B raw32917step0 raw32917step0Labels := by
      have ha : raw32917step0 = (fun i j => raw32917 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32917step0 raw32917; decide +kernel
      have hl : raw32917step0Labels = raw32917Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32917 raw32917Labels permutation152 permutation6
    mixedMoment B raw32917step0 raw32917step0Labels = mixedMoment B raw32917step1 raw32917step1Labels := by
      have ha : raw32917step1 = raw32917step0 := by apply Matrix.ext; unfold raw32917step1 raw32917step0; decide +kernel
      have hl : raw32917step0Labels = labelEmbedding9 ∘ raw32917step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32917step0 raw32917step0Labels raw32917step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw32918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32918step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32918 raw32918Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw32918 raw32918Labels = mixedMoment B raw32918step0 raw32918step0Labels := by
      have ha : raw32918step0 = (fun i j => raw32918 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32918step0 raw32918; decide +kernel
      have hl : raw32918step0Labels = raw32918Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32918 raw32918Labels permutation154 permutation2
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw32919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32919step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32919 raw32919Labels = mixedMoment B node5394 node5394Labels := by
  calc
    mixedMoment B raw32919 raw32919Labels = mixedMoment B raw32919step0 raw32919step0Labels := by
      have ha : raw32919step0 = (fun i j => raw32919 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32919step0 raw32919; decide +kernel
      have hl : raw32919step0Labels = raw32919Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32919 raw32919Labels permutation178 permutation2
    _ = mixedMoment B node5394 node5394Labels := by rfl

def raw32920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32920 raw32920Labels = mixedMoment B node5423 node5423Labels := by
  calc
    _ = mixedMoment B node5423 node5423Labels := by rfl

def raw32921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32921step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw32921step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32921step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32921step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32921 raw32921Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw32921 raw32921Labels = mixedMoment B raw32921step0 raw32921step0Labels := by
      have hz : ∀ j, raw32921 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32921step0 = (fun i j => raw32921 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32921step0 raw32921; decide +kernel
      have hl : raw32921step0Labels = raw32921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32921 raw32921Labels permutation520 hz
    mixedMoment B raw32921step0 raw32921step0Labels = mixedMoment B raw32921step1 raw32921step1Labels := by
      have ha : raw32921step1 = (fun i j => raw32921step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32921step1 raw32921step0; decide +kernel
      have hl : raw32921step1Labels = raw32921step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32921step0 raw32921step0Labels permutation151 permutation2
    mixedMoment B raw32921step1 raw32921step1Labels = mixedMoment B raw32921step2 raw32921step2Labels := by
      have ha : raw32921step2 = -raw32921step1 := by apply Matrix.ext; change ∀ i j, raw32921step2 i j = -(raw32921step1 i j); unfold raw32921step2 raw32921step1; decide +kernel
      have hl : raw32921step2Labels = raw32921step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw32922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32922step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32922step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32922step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32922step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32922step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32922 raw32922Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw32922 raw32922Labels = mixedMoment B raw32922step0 raw32922step0Labels := by
      have ha : raw32922step0 = (fun i j => raw32922 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32922step0 raw32922; decide +kernel
      have hl : raw32922step0Labels = raw32922Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32922 raw32922Labels permutation178 permutation7
    mixedMoment B raw32922step0 raw32922step0Labels = mixedMoment B raw32922step1 raw32922step1Labels := by
      have ha : raw32922step1 = -raw32922step0 := by apply Matrix.ext; change ∀ i j, raw32922step1 i j = -(raw32922step0 i j); unfold raw32922step1 raw32922step0; decide +kernel
      have hl : raw32922step1Labels = raw32922step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32922step1 raw32922step1Labels = mixedMoment B raw32922step2 raw32922step2Labels := by
      have ha : raw32922step2 = raw32922step1 := by apply Matrix.ext; unfold raw32922step2 raw32922step1; decide +kernel
      have hl : raw32922step1Labels = labelEmbedding10 ∘ raw32922step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32922step1 raw32922step1Labels raw32922step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw32923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32923step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32923 raw32923Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw32923 raw32923Labels = mixedMoment B raw32923step0 raw32923step0Labels := by
      have hz : ∀ j, raw32923 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw32923step0 = (fun i j => raw32923 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw32923step0 raw32923; decide +kernel
      have hl : raw32923step0Labels = raw32923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32923 raw32923Labels permutation265 hz
    mixedMoment B raw32923step0 raw32923step0Labels = mixedMoment B raw32923step1 raw32923step1Labels := by
      have ha : raw32923step1 = (fun i j => raw32923step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32923step1 raw32923step0; decide +kernel
      have hl : raw32923step1Labels = raw32923step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32923step0 raw32923step0Labels permutation34 permutation2
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw32924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32924step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32924 raw32924Labels = mixedMoment B node4963 node4963Labels := by
  calc
    mixedMoment B raw32924 raw32924Labels = mixedMoment B raw32924step0 raw32924step0Labels := by
      have ha : raw32924step0 = (fun i j => raw32924 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32924step0 raw32924; decide +kernel
      have hl : raw32924step0Labels = raw32924Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32924 raw32924Labels permutation154 permutation2
    _ = mixedMoment B node4963 node4963Labels := by rfl

def raw32925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32925 raw32925Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw32925 raw32925Labels = mixedMoment B raw32925step0 raw32925step0Labels := by
      have ha : raw32925step0 = (fun i j => raw32925 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32925step0 raw32925; decide +kernel
      have hl : raw32925step0Labels = raw32925Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32925 raw32925Labels permutation158 permutation2
    _ = mixedMoment B node5144 node5144Labels := by rfl

def raw32926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32926 raw32926Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw32926 raw32926Labels = mixedMoment B raw32926step0 raw32926step0Labels := by
      have hz : ∀ j, raw32926 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32926step0 = (fun i j => raw32926 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32926step0 raw32926; decide +kernel
      have hl : raw32926step0Labels = raw32926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32926 raw32926Labels permutation520 hz
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw32927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32927 raw32927Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw32927 raw32927Labels = mixedMoment B raw32927step0 raw32927step0Labels := by
      have ha : raw32927step0 = (fun i j => raw32927 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32927step0 raw32927; decide +kernel
      have hl : raw32927step0Labels = raw32927Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32927 raw32927Labels permutation154 permutation2
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw32928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32928 raw32928Labels = mixedMoment B node4955 node4955Labels := by
  calc
    mixedMoment B raw32928 raw32928Labels = mixedMoment B raw32928step0 raw32928step0Labels := by
      have ha : raw32928step0 = (fun i j => raw32928 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32928step0 raw32928; decide +kernel
      have hl : raw32928step0Labels = raw32928Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32928 raw32928Labels permutation154 permutation2
    _ = mixedMoment B node4955 node4955Labels := by rfl

def raw32929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32929 raw32929Labels = mixedMoment B node5036 node5036Labels := by
  calc
    mixedMoment B raw32929 raw32929Labels = mixedMoment B raw32929step0 raw32929step0Labels := by
      have ha : raw32929step0 = (fun i j => raw32929 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32929step0 raw32929; decide +kernel
      have hl : raw32929step0Labels = raw32929Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32929 raw32929Labels permutation178 permutation2
    _ = mixedMoment B node5036 node5036Labels := by rfl

def raw32930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32930 raw32930Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw32930 raw32930Labels = mixedMoment B raw32930step0 raw32930step0Labels := by
      have hz : ∀ j, raw32930 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32930step0 = (fun i j => raw32930 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32930step0 raw32930; decide +kernel
      have hl : raw32930step0Labels = raw32930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32930 raw32930Labels permutation520 hz
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw32931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32931step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32931 raw32931Labels = mixedMoment B node5135 node5135Labels := by
  calc
    mixedMoment B raw32931 raw32931Labels = mixedMoment B raw32931step0 raw32931step0Labels := by
      have ha : raw32931step0 = (fun i j => raw32931 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32931step0 raw32931; decide +kernel
      have hl : raw32931step0Labels = raw32931Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32931 raw32931Labels permutation155 permutation2
    _ = mixedMoment B node5135 node5135Labels := by rfl

def raw32932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32932 raw32932Labels = mixedMoment B node4957 node4957Labels := by
  calc
    _ = mixedMoment B node4957 node4957Labels := by rfl

def raw32933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32933 raw32933Labels = mixedMoment B node5038 node5038Labels := by
  calc
    mixedMoment B raw32933 raw32933Labels = mixedMoment B raw32933step0 raw32933step0Labels := by
      have ha : raw32933step0 = (fun i j => raw32933 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32933step0 raw32933; decide +kernel
      have hl : raw32933step0Labels = raw32933Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32933 raw32933Labels permutation176 permutation2
    _ = mixedMoment B node5038 node5038Labels := by rfl

def raw32934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32934 raw32934Labels = mixedMoment B node5129 node5129Labels := by
  calc
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw32935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw32935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32935 raw32935Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw32935 raw32935Labels = mixedMoment B raw32935step0 raw32935step0Labels := by
      have ha : raw32935step0 = (fun i j => raw32935 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32935step0 raw32935; decide +kernel
      have hl : raw32935step0Labels = raw32935Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32935 raw32935Labels permutation153 permutation2
    _ = mixedMoment B node5138 node5138Labels := by rfl

def raw32936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32936step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw32936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32936 raw32936Labels = mixedMoment B node4954 node4954Labels := by
  calc
    mixedMoment B raw32936 raw32936Labels = mixedMoment B raw32936step0 raw32936step0Labels := by
      have ha : raw32936step0 = (fun i j => raw32936 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32936step0 raw32936; decide +kernel
      have hl : raw32936step0Labels = raw32936Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32936 raw32936Labels permutation154 permutation2
    _ = mixedMoment B node4954 node4954Labels := by rfl

def raw32937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw32937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32937 raw32937Labels = mixedMoment B node5033 node5033Labels := by
  calc
    mixedMoment B raw32937 raw32937Labels = mixedMoment B raw32937step0 raw32937step0Labels := by
      have ha : raw32937step0 = (fun i j => raw32937 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32937step0 raw32937; decide +kernel
      have hl : raw32937step0Labels = raw32937Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32937 raw32937Labels permutation178 permutation2
    _ = mixedMoment B node5033 node5033Labels := by rfl

def raw32938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32938 raw32938Labels = mixedMoment B node5127 node5127Labels := by
  calc
    _ = mixedMoment B node5127 node5127Labels := by rfl

def raw32939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw32939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw32939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw32939step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32939step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32939 raw32939Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw32939 raw32939Labels = mixedMoment B raw32939step0 raw32939step0Labels := by
      have hz : ∀ j, raw32939 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32939step0 = (fun i j => raw32939 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32939step0 raw32939; decide +kernel
      have hl : raw32939step0Labels = raw32939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32939 raw32939Labels permutation520 hz
    mixedMoment B raw32939step0 raw32939step0Labels = mixedMoment B raw32939step1 raw32939step1Labels := by
      have ha : raw32939step1 = (fun i j => raw32939step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32939step1 raw32939step0; decide +kernel
      have hl : raw32939step1Labels = raw32939step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32939step0 raw32939step0Labels permutation151 permutation2
    mixedMoment B raw32939step1 raw32939step1Labels = mixedMoment B raw32939step2 raw32939step2Labels := by
      have ha : raw32939step2 = -raw32939step1 := by apply Matrix.ext; change ∀ i j, raw32939step2 i j = -(raw32939step1 i j); unfold raw32939step2 raw32939step1; decide +kernel
      have hl : raw32939step2Labels = raw32939step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw32940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32940Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw32940step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32940step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw32940step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32940 raw32940Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw32940 raw32940Labels = mixedMoment B raw32940step0 raw32940step0Labels := by
      have ha : raw32940step0 = (fun i j => raw32940 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32940step0 raw32940; decide +kernel
      have hl : raw32940step0Labels = raw32940Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32940 raw32940Labels permutation662 permutation7
    mixedMoment B raw32940step0 raw32940step0Labels = mixedMoment B raw32940step1 raw32940step1Labels := by
      have ha : raw32940step1 = raw32940step0 := by apply Matrix.ext; unfold raw32940step1 raw32940step0; decide +kernel
      have hl : raw32940step0Labels = labelEmbedding1 ∘ raw32940step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32940step0 raw32940step0Labels raw32940step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

def raw32941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32941Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32941step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32941step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32941 raw32941Labels = mixedMoment B node3793 node3793Labels := by
  calc
    mixedMoment B raw32941 raw32941Labels = mixedMoment B raw32941step0 raw32941step0Labels := by
      have ha : raw32941step0 = (fun i j => raw32941 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32941step0 raw32941; decide +kernel
      have hl : raw32941step0Labels = raw32941Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32941 raw32941Labels permutation662 permutation7
    mixedMoment B raw32941step0 raw32941step0Labels = mixedMoment B raw32941step1 raw32941step1Labels := by
      have ha : raw32941step1 = raw32941step0 := by apply Matrix.ext; unfold raw32941step1 raw32941step0; decide +kernel
      have hl : raw32941step0Labels = labelEmbedding1 ∘ raw32941step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32941step0 raw32941step0Labels raw32941step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3793 node3793Labels := by rfl

def raw32942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32942Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32942step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32942step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32942step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32942 raw32942Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw32942 raw32942Labels = mixedMoment B raw32942step0 raw32942step0Labels := by
      have ha : raw32942step0 = (fun i j => raw32942 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32942step0 raw32942; decide +kernel
      have hl : raw32942step0Labels = raw32942Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32942 raw32942Labels permutation662 permutation7
    mixedMoment B raw32942step0 raw32942step0Labels = mixedMoment B raw32942step1 raw32942step1Labels := by
      have ha : raw32942step1 = raw32942step0 := by apply Matrix.ext; unfold raw32942step1 raw32942step0; decide +kernel
      have hl : raw32942step0Labels = labelEmbedding1 ∘ raw32942step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32942step0 raw32942step0Labels raw32942step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3837 node3837Labels := by rfl

def raw32943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32943Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32943step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32943step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32943 raw32943Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw32943 raw32943Labels = mixedMoment B raw32943step0 raw32943step0Labels := by
      have hz : ∀ j, raw32943 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32943step0 = (fun i j => raw32943 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32943step0 raw32943; decide +kernel
      have hl : raw32943step0Labels = raw32943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32943 raw32943Labels permutation520 hz
    mixedMoment B raw32943step0 raw32943step0Labels = mixedMoment B raw32943step1 raw32943step1Labels := by
      have ha : raw32943step1 = (fun i j => raw32943step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32943step1 raw32943step0; decide +kernel
      have hl : raw32943step1Labels = raw32943step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32943step0 raw32943step0Labels permutation149 permutation7
    mixedMoment B raw32943step1 raw32943step1Labels = mixedMoment B raw32943step2 raw32943step2Labels := by
      have ha : raw32943step2 = raw32943step1 := by apply Matrix.ext; unfold raw32943step2 raw32943step1; decide +kernel
      have hl : raw32943step1Labels = labelEmbedding1 ∘ raw32943step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32943step1 raw32943step1Labels raw32943step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw32944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32944Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32944step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32944step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32944step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32944 raw32944Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw32944 raw32944Labels = mixedMoment B raw32944step0 raw32944step0Labels := by
      have ha : raw32944step0 = (fun i j => raw32944 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32944step0 raw32944; decide +kernel
      have hl : raw32944step0Labels = raw32944Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32944 raw32944Labels permutation178 permutation7
    mixedMoment B raw32944step0 raw32944step0Labels = mixedMoment B raw32944step1 raw32944step1Labels := by
      have ha : raw32944step1 = -raw32944step0 := by apply Matrix.ext; change ∀ i j, raw32944step1 i j = -(raw32944step0 i j); unfold raw32944step1 raw32944step0; decide +kernel
      have hl : raw32944step1Labels = raw32944step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32944step1 raw32944step1Labels = mixedMoment B raw32944step2 raw32944step2Labels := by
      have ha : raw32944step2 = raw32944step1 := by apply Matrix.ext; unfold raw32944step2 raw32944step1; decide +kernel
      have hl : raw32944step1Labels = labelEmbedding1 ∘ raw32944step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32944step1 raw32944step1Labels raw32944step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw32945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32945Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32945step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32945step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32945step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32945step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32945step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32945 raw32945Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw32945 raw32945Labels = mixedMoment B raw32945step0 raw32945step0Labels := by
      have hz : ∀ j, raw32945 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw32945step0 = (fun i j => raw32945 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw32945step0 raw32945; decide +kernel
      have hl : raw32945step0Labels = raw32945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32945 raw32945Labels permutation265 hz
    mixedMoment B raw32945step0 raw32945step0Labels = mixedMoment B raw32945step1 raw32945step1Labels := by
      have ha : raw32945step1 = (fun i j => raw32945step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32945step1 raw32945step0; decide +kernel
      have hl : raw32945step1Labels = raw32945step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32945step0 raw32945step0Labels permutation34 permutation7
    mixedMoment B raw32945step1 raw32945step1Labels = mixedMoment B raw32945step2 raw32945step2Labels := by
      have ha : raw32945step2 = -raw32945step1 := by apply Matrix.ext; change ∀ i j, raw32945step2 i j = -(raw32945step1 i j); unfold raw32945step2 raw32945step1; decide +kernel
      have hl : raw32945step2Labels = raw32945step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32945step2 raw32945step2Labels = mixedMoment B raw32945step3 raw32945step3Labels := by
      have ha : raw32945step3 = raw32945step2 := by apply Matrix.ext; unfold raw32945step3 raw32945step2; decide +kernel
      have hl : raw32945step2Labels = labelEmbedding1 ∘ raw32945step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32945step2 raw32945step2Labels raw32945step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

def raw32946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32946step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32946step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32946 raw32946Labels = mixedMoment B node3553 node3553Labels := by
  calc
    mixedMoment B raw32946 raw32946Labels = mixedMoment B raw32946step0 raw32946step0Labels := by
      have ha : raw32946step0 = (fun i j => raw32946 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32946step0 raw32946; decide +kernel
      have hl : raw32946step0Labels = raw32946Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32946 raw32946Labels permutation178 permutation7
    mixedMoment B raw32946step0 raw32946step0Labels = mixedMoment B raw32946step1 raw32946step1Labels := by
      have ha : raw32946step1 = -raw32946step0 := by apply Matrix.ext; change ∀ i j, raw32946step1 i j = -(raw32946step0 i j); unfold raw32946step1 raw32946step0; decide +kernel
      have hl : raw32946step1Labels = raw32946step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32946step1 raw32946step1Labels = mixedMoment B raw32946step2 raw32946step2Labels := by
      have ha : raw32946step2 = raw32946step1 := by apply Matrix.ext; unfold raw32946step2 raw32946step1; decide +kernel
      have hl : raw32946step1Labels = labelEmbedding1 ∘ raw32946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32946step1 raw32946step1Labels raw32946step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3553 node3553Labels := by rfl

def raw32947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32947Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw32947step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32947step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32947step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32947step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32947 raw32947Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw32947 raw32947Labels = mixedMoment B raw32947step0 raw32947step0Labels := by
      have ha : raw32947step0 = (fun i j => raw32947 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32947step0 raw32947; decide +kernel
      have hl : raw32947step0Labels = raw32947Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32947 raw32947Labels permutation178 permutation7
    mixedMoment B raw32947step0 raw32947step0Labels = mixedMoment B raw32947step1 raw32947step1Labels := by
      have ha : raw32947step1 = -raw32947step0 := by apply Matrix.ext; change ∀ i j, raw32947step1 i j = -(raw32947step0 i j); unfold raw32947step1 raw32947step0; decide +kernel
      have hl : raw32947step1Labels = raw32947step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32947step1 raw32947step1Labels = mixedMoment B raw32947step2 raw32947step2Labels := by
      have ha : raw32947step2 = raw32947step1 := by apply Matrix.ext; unfold raw32947step2 raw32947step1; decide +kernel
      have hl : raw32947step1Labels = labelEmbedding1 ∘ raw32947step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32947step1 raw32947step1Labels raw32947step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

def raw32948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32948Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32948step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32948step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32948step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32948step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32948 raw32948Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw32948 raw32948Labels = mixedMoment B raw32948step0 raw32948step0Labels := by
      have hz : ∀ j, raw32948 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32948step0 = (fun i j => raw32948 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32948step0 raw32948; decide +kernel
      have hl : raw32948step0Labels = raw32948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32948 raw32948Labels permutation520 hz
    mixedMoment B raw32948step0 raw32948step0Labels = mixedMoment B raw32948step1 raw32948step1Labels := by
      have ha : raw32948step1 = (fun i j => raw32948step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32948step1 raw32948step0; decide +kernel
      have hl : raw32948step1Labels = raw32948step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32948step0 raw32948step0Labels permutation38 permutation7
    mixedMoment B raw32948step1 raw32948step1Labels = mixedMoment B raw32948step2 raw32948step2Labels := by
      have ha : raw32948step2 = -raw32948step1 := by apply Matrix.ext; change ∀ i j, raw32948step2 i j = -(raw32948step1 i j); unfold raw32948step2 raw32948step1; decide +kernel
      have hl : raw32948step2Labels = raw32948step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32948step2 raw32948step2Labels = mixedMoment B raw32948step3 raw32948step3Labels := by
      have ha : raw32948step3 = raw32948step2 := by apply Matrix.ext; unfold raw32948step3 raw32948step2; decide +kernel
      have hl : raw32948step2Labels = labelEmbedding1 ∘ raw32948step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32948step2 raw32948step2Labels raw32948step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

def raw32949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32949Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32949step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32949step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32949step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32949step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32949 raw32949Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw32949 raw32949Labels = mixedMoment B raw32949step0 raw32949step0Labels := by
      have ha : raw32949step0 = (fun i j => raw32949 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32949step0 raw32949; decide +kernel
      have hl : raw32949step0Labels = raw32949Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32949 raw32949Labels permutation178 permutation7
    mixedMoment B raw32949step0 raw32949step0Labels = mixedMoment B raw32949step1 raw32949step1Labels := by
      have ha : raw32949step1 = -raw32949step0 := by apply Matrix.ext; change ∀ i j, raw32949step1 i j = -(raw32949step0 i j); unfold raw32949step1 raw32949step0; decide +kernel
      have hl : raw32949step1Labels = raw32949step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32949step1 raw32949step1Labels = mixedMoment B raw32949step2 raw32949step2Labels := by
      have ha : raw32949step2 = raw32949step1 := by apply Matrix.ext; unfold raw32949step2 raw32949step1; decide +kernel
      have hl : raw32949step1Labels = labelEmbedding1 ∘ raw32949step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32949step1 raw32949step1Labels raw32949step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw32950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32950Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw32950step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw32950step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32950step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw32950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32950 raw32950Labels = mixedMoment B node3508 node3508Labels := by
  calc
    mixedMoment B raw32950 raw32950Labels = mixedMoment B raw32950step0 raw32950step0Labels := by
      have ha : raw32950step0 = (fun i j => raw32950 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32950step0 raw32950; decide +kernel
      have hl : raw32950step0Labels = raw32950Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32950 raw32950Labels permutation178 permutation7
    mixedMoment B raw32950step0 raw32950step0Labels = mixedMoment B raw32950step1 raw32950step1Labels := by
      have ha : raw32950step1 = -raw32950step0 := by apply Matrix.ext; change ∀ i j, raw32950step1 i j = -(raw32950step0 i j); unfold raw32950step1 raw32950step0; decide +kernel
      have hl : raw32950step1Labels = raw32950step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32950step1 raw32950step1Labels = mixedMoment B raw32950step2 raw32950step2Labels := by
      have ha : raw32950step2 = raw32950step1 := by apply Matrix.ext; unfold raw32950step2 raw32950step1; decide +kernel
      have hl : raw32950step1Labels = labelEmbedding1 ∘ raw32950step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32950step1 raw32950step1Labels raw32950step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3508 node3508Labels := by rfl

def raw32951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32951Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw32951step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32951step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw32951step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32951step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw32951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32951 raw32951Labels = mixedMoment B node3450 node3450Labels := by
  calc
    mixedMoment B raw32951 raw32951Labels = mixedMoment B raw32951step0 raw32951step0Labels := by
      have ha : raw32951step0 = (fun i j => raw32951 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32951step0 raw32951; decide +kernel
      have hl : raw32951step0Labels = raw32951Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32951 raw32951Labels permutation178 permutation7
    mixedMoment B raw32951step0 raw32951step0Labels = mixedMoment B raw32951step1 raw32951step1Labels := by
      have ha : raw32951step1 = -raw32951step0 := by apply Matrix.ext; change ∀ i j, raw32951step1 i j = -(raw32951step0 i j); unfold raw32951step1 raw32951step0; decide +kernel
      have hl : raw32951step1Labels = raw32951step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32951step1 raw32951step1Labels = mixedMoment B raw32951step2 raw32951step2Labels := by
      have ha : raw32951step2 = raw32951step1 := by apply Matrix.ext; unfold raw32951step2 raw32951step1; decide +kernel
      have hl : raw32951step1Labels = labelEmbedding1 ∘ raw32951step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32951step1 raw32951step1Labels raw32951step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3450 node3450Labels := by rfl

def raw32952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32952step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw32952step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32952step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32952step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32952step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32952 raw32952Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw32952 raw32952Labels = mixedMoment B raw32952step0 raw32952step0Labels := by
      have hz : ∀ j, raw32952 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32952step0 = (fun i j => raw32952 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32952step0 raw32952; decide +kernel
      have hl : raw32952step0Labels = raw32952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32952 raw32952Labels permutation520 hz
    mixedMoment B raw32952step0 raw32952step0Labels = mixedMoment B raw32952step1 raw32952step1Labels := by
      have ha : raw32952step1 = (fun i j => raw32952step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32952step1 raw32952step0; decide +kernel
      have hl : raw32952step1Labels = raw32952step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32952step0 raw32952step0Labels permutation38 permutation7
    mixedMoment B raw32952step1 raw32952step1Labels = mixedMoment B raw32952step2 raw32952step2Labels := by
      have ha : raw32952step2 = -raw32952step1 := by apply Matrix.ext; change ∀ i j, raw32952step2 i j = -(raw32952step1 i j); unfold raw32952step2 raw32952step1; decide +kernel
      have hl : raw32952step2Labels = raw32952step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32952step2 raw32952step2Labels = mixedMoment B raw32952step3 raw32952step3Labels := by
      have ha : raw32952step3 = raw32952step2 := by apply Matrix.ext; unfold raw32952step3 raw32952step2; decide +kernel
      have hl : raw32952step2Labels = labelEmbedding1 ∘ raw32952step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32952step2 raw32952step2Labels raw32952step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

def raw32953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw32953step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32953step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32953step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32953step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32953 raw32953Labels = mixedMoment B node3515 node3515Labels := by
  calc
    mixedMoment B raw32953 raw32953Labels = mixedMoment B raw32953step0 raw32953step0Labels := by
      have ha : raw32953step0 = (fun i j => raw32953 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32953step0 raw32953; decide +kernel
      have hl : raw32953step0Labels = raw32953Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32953 raw32953Labels permutation178 permutation7
    mixedMoment B raw32953step0 raw32953step0Labels = mixedMoment B raw32953step1 raw32953step1Labels := by
      have ha : raw32953step1 = -raw32953step0 := by apply Matrix.ext; change ∀ i j, raw32953step1 i j = -(raw32953step0 i j); unfold raw32953step1 raw32953step0; decide +kernel
      have hl : raw32953step1Labels = raw32953step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32953step1 raw32953step1Labels = mixedMoment B raw32953step2 raw32953step2Labels := by
      have ha : raw32953step2 = raw32953step1 := by apply Matrix.ext; unfold raw32953step2 raw32953step1; decide +kernel
      have hl : raw32953step1Labels = labelEmbedding1 ∘ raw32953step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32953step1 raw32953step1Labels raw32953step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3515 node3515Labels := by rfl

def raw32954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw32954step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32954step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw32954step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32954step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw32954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32954 raw32954Labels = mixedMoment B node3509 node3509Labels := by
  calc
    mixedMoment B raw32954 raw32954Labels = mixedMoment B raw32954step0 raw32954step0Labels := by
      have ha : raw32954step0 = (fun i j => raw32954 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32954step0 raw32954; decide +kernel
      have hl : raw32954step0Labels = raw32954Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32954 raw32954Labels permutation178 permutation7
    mixedMoment B raw32954step0 raw32954step0Labels = mixedMoment B raw32954step1 raw32954step1Labels := by
      have ha : raw32954step1 = -raw32954step0 := by apply Matrix.ext; change ∀ i j, raw32954step1 i j = -(raw32954step0 i j); unfold raw32954step1 raw32954step0; decide +kernel
      have hl : raw32954step1Labels = raw32954step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32954step1 raw32954step1Labels = mixedMoment B raw32954step2 raw32954step2Labels := by
      have ha : raw32954step2 = raw32954step1 := by apply Matrix.ext; unfold raw32954step2 raw32954step1; decide +kernel
      have hl : raw32954step1Labels = labelEmbedding1 ∘ raw32954step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32954step1 raw32954step1Labels raw32954step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3509 node3509Labels := by rfl

def raw32955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw32955step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw32955step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32955step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw32955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32955 raw32955Labels = mixedMoment B node3453 node3453Labels := by
  calc
    mixedMoment B raw32955 raw32955Labels = mixedMoment B raw32955step0 raw32955step0Labels := by
      have ha : raw32955step0 = (fun i j => raw32955 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32955step0 raw32955; decide +kernel
      have hl : raw32955step0Labels = raw32955Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32955 raw32955Labels permutation178 permutation7
    mixedMoment B raw32955step0 raw32955step0Labels = mixedMoment B raw32955step1 raw32955step1Labels := by
      have ha : raw32955step1 = -raw32955step0 := by apply Matrix.ext; change ∀ i j, raw32955step1 i j = -(raw32955step0 i j); unfold raw32955step1 raw32955step0; decide +kernel
      have hl : raw32955step1Labels = raw32955step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32955step1 raw32955step1Labels = mixedMoment B raw32955step2 raw32955step2Labels := by
      have ha : raw32955step2 = raw32955step1 := by apply Matrix.ext; unfold raw32955step2 raw32955step1; decide +kernel
      have hl : raw32955step1Labels = labelEmbedding1 ∘ raw32955step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32955step1 raw32955step1Labels raw32955step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3453 node3453Labels := by rfl

def raw32956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw32956step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32956step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw32956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32956step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw32956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32956 raw32956Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw32956 raw32956Labels = mixedMoment B raw32956step0 raw32956step0Labels := by
      have ha : raw32956step0 = (fun i j => raw32956 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32956step0 raw32956; decide +kernel
      have hl : raw32956step0Labels = raw32956Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32956 raw32956Labels permutation178 permutation7
    mixedMoment B raw32956step0 raw32956step0Labels = mixedMoment B raw32956step1 raw32956step1Labels := by
      have ha : raw32956step1 = -raw32956step0 := by apply Matrix.ext; change ∀ i j, raw32956step1 i j = -(raw32956step0 i j); unfold raw32956step1 raw32956step0; decide +kernel
      have hl : raw32956step1Labels = raw32956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32956step1 raw32956step1Labels = mixedMoment B raw32956step2 raw32956step2Labels := by
      have ha : raw32956step2 = raw32956step1 := by apply Matrix.ext; unfold raw32956step2 raw32956step1; decide +kernel
      have hl : raw32956step1Labels = labelEmbedding1 ∘ raw32956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32956step1 raw32956step1Labels raw32956step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw32957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw32957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw32957step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32957step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32957step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32957step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32957 raw32957Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw32957 raw32957Labels = mixedMoment B raw32957step0 raw32957step0Labels := by
      have ha : raw32957step0 = (fun i j => raw32957 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32957step0 raw32957; decide +kernel
      have hl : raw32957step0Labels = raw32957Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32957 raw32957Labels permutation178 permutation7
    mixedMoment B raw32957step0 raw32957step0Labels = mixedMoment B raw32957step1 raw32957step1Labels := by
      have ha : raw32957step1 = -raw32957step0 := by apply Matrix.ext; change ∀ i j, raw32957step1 i j = -(raw32957step0 i j); unfold raw32957step1 raw32957step0; decide +kernel
      have hl : raw32957step1Labels = raw32957step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32957step1 raw32957step1Labels = mixedMoment B raw32957step2 raw32957step2Labels := by
      have ha : raw32957step2 = raw32957step1 := by apply Matrix.ext; unfold raw32957step2 raw32957step1; decide +kernel
      have hl : raw32957step1Labels = labelEmbedding1 ∘ raw32957step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32957step1 raw32957step1Labels raw32957step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

def raw32958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw32958step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32958step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw32958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32958 raw32958Labels = mixedMoment B node3452 node3452Labels := by
  calc
    mixedMoment B raw32958 raw32958Labels = mixedMoment B raw32958step0 raw32958step0Labels := by
      have ha : raw32958step0 = (fun i j => raw32958 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32958step0 raw32958; decide +kernel
      have hl : raw32958step0Labels = raw32958Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32958 raw32958Labels permutation662 permutation7
    mixedMoment B raw32958step0 raw32958step0Labels = mixedMoment B raw32958step1 raw32958step1Labels := by
      have ha : raw32958step1 = raw32958step0 := by apply Matrix.ext; unfold raw32958step1 raw32958step0; decide +kernel
      have hl : raw32958step0Labels = labelEmbedding1 ∘ raw32958step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32958step0 raw32958step0Labels raw32958step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3452 node3452Labels := by rfl

def raw32959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw32959step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw32959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32959 raw32959Labels = mixedMoment B node3449 node3449Labels := by
  calc
    mixedMoment B raw32959 raw32959Labels = mixedMoment B raw32959step0 raw32959step0Labels := by
      have ha : raw32959step0 = (fun i j => raw32959 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32959step0 raw32959; decide +kernel
      have hl : raw32959step0Labels = raw32959Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32959 raw32959Labels permutation662 permutation7
    mixedMoment B raw32959step0 raw32959step0Labels = mixedMoment B raw32959step1 raw32959step1Labels := by
      have ha : raw32959step1 = raw32959step0 := by apply Matrix.ext; unfold raw32959step1 raw32959step0; decide +kernel
      have hl : raw32959step0Labels = labelEmbedding1 ∘ raw32959step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32959step0 raw32959step0Labels raw32959step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3449 node3449Labels := by rfl

def raw32960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw32960step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32960step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw32960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32960 raw32960Labels = mixedMoment B node3513 node3513Labels := by
  calc
    mixedMoment B raw32960 raw32960Labels = mixedMoment B raw32960step0 raw32960step0Labels := by
      have ha : raw32960step0 = (fun i j => raw32960 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32960step0 raw32960; decide +kernel
      have hl : raw32960step0Labels = raw32960Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32960 raw32960Labels permutation662 permutation7
    mixedMoment B raw32960step0 raw32960step0Labels = mixedMoment B raw32960step1 raw32960step1Labels := by
      have ha : raw32960step1 = raw32960step0 := by apply Matrix.ext; unfold raw32960step1 raw32960step0; decide +kernel
      have hl : raw32960step0Labels = labelEmbedding1 ∘ raw32960step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32960step0 raw32960step0Labels raw32960step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3513 node3513Labels := by rfl

def raw32961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw32961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw32961step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw32961step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw32961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32961 raw32961Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw32961 raw32961Labels = mixedMoment B raw32961step0 raw32961step0Labels := by
      have hz : ∀ j, raw32961 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32961step0 = (fun i j => raw32961 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32961step0 raw32961; decide +kernel
      have hl : raw32961step0Labels = raw32961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32961 raw32961Labels permutation520 hz
    mixedMoment B raw32961step0 raw32961step0Labels = mixedMoment B raw32961step1 raw32961step1Labels := by
      have ha : raw32961step1 = (fun i j => raw32961step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32961step1 raw32961step0; decide +kernel
      have hl : raw32961step1Labels = raw32961step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32961step0 raw32961step0Labels permutation149 permutation7
    mixedMoment B raw32961step1 raw32961step1Labels = mixedMoment B raw32961step2 raw32961step2Labels := by
      have ha : raw32961step2 = raw32961step1 := by apply Matrix.ext; unfold raw32961step2 raw32961step1; decide +kernel
      have hl : raw32961step1Labels = labelEmbedding1 ∘ raw32961step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32961step1 raw32961step1Labels raw32961step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

def raw32962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32962Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32962step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32962 raw32962Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw32962 raw32962Labels = mixedMoment B raw32962step0 raw32962step0Labels := by
      have ha : raw32962step0 = (fun i j => raw32962 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32962step0 raw32962; decide +kernel
      have hl : raw32962step0Labels = raw32962Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32962 raw32962Labels permutation154 permutation2
    _ = mixedMoment B node3719 node3719Labels := by rfl

def raw32963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32963step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32963step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32963 raw32963Labels = mixedMoment B node2353 node2353Labels := by
  calc
    mixedMoment B raw32963 raw32963Labels = mixedMoment B raw32963step0 raw32963step0Labels := by
      have ha : raw32963step0 = (fun i j => raw32963 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32963step0 raw32963; decide +kernel
      have hl : raw32963step0Labels = raw32963Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32963 raw32963Labels permutation154 permutation2
    _ = mixedMoment B node2353 node2353Labels := by rfl

def raw32964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32964 raw32964Labels = mixedMoment B node2348 node2348Labels := by
  calc
    mixedMoment B raw32964 raw32964Labels = mixedMoment B raw32964step0 raw32964step0Labels := by
      have ha : raw32964step0 = (fun i j => raw32964 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32964step0 raw32964; decide +kernel
      have hl : raw32964step0Labels = raw32964Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32964 raw32964Labels permutation154 permutation2
    _ = mixedMoment B node2348 node2348Labels := by rfl

def raw32965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw32965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32965 raw32965Labels = mixedMoment B node2347 node2347Labels := by
  calc
    mixedMoment B raw32965 raw32965Labels = mixedMoment B raw32965step0 raw32965step0Labels := by
      have ha : raw32965step0 = (fun i j => raw32965 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32965step0 raw32965; decide +kernel
      have hl : raw32965step0Labels = raw32965Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32965 raw32965Labels permutation154 permutation2
    _ = mixedMoment B node2347 node2347Labels := by rfl

def raw32966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw32966step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32966step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32966step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32966step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32966step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32966 raw32966Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw32966 raw32966Labels = mixedMoment B raw32966step0 raw32966step0Labels := by
      have ha : raw32966step0 = (fun i j => raw32966 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32966step0 raw32966; decide +kernel
      have hl : raw32966step0Labels = raw32966Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32966 raw32966Labels permutation663 permutation3
    mixedMoment B raw32966step0 raw32966step0Labels = mixedMoment B raw32966step1 raw32966step1Labels := by
      have ha : raw32966step1 = -raw32966step0 := by apply Matrix.ext; change ∀ i j, raw32966step1 i j = -(raw32966step0 i j); unfold raw32966step1 raw32966step0; decide +kernel
      have hl : raw32966step1Labels = raw32966step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32966step1 raw32966step1Labels = mixedMoment B raw32966step2 raw32966step2Labels := by
      have ha : raw32966step2 = raw32966step1 := by apply Matrix.ext; unfold raw32966step2 raw32966step1; decide +kernel
      have hl : raw32966step1Labels = labelEmbedding6 ∘ raw32966step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32966step1 raw32966step1Labels raw32966step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw32967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw32967step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32967step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32967step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32967step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32967step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32967 raw32967Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw32967 raw32967Labels = mixedMoment B raw32967step0 raw32967step0Labels := by
      have ha : raw32967step0 = (fun i j => raw32967 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32967step0 raw32967; decide +kernel
      have hl : raw32967step0Labels = raw32967Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32967 raw32967Labels permutation662 permutation3
    mixedMoment B raw32967step0 raw32967step0Labels = mixedMoment B raw32967step1 raw32967step1Labels := by
      have ha : raw32967step1 = -raw32967step0 := by apply Matrix.ext; change ∀ i j, raw32967step1 i j = -(raw32967step0 i j); unfold raw32967step1 raw32967step0; decide +kernel
      have hl : raw32967step1Labels = raw32967step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32967step1 raw32967step1Labels = mixedMoment B raw32967step2 raw32967step2Labels := by
      have ha : raw32967step2 = raw32967step1 := by apply Matrix.ext; unfold raw32967step2 raw32967step1; decide +kernel
      have hl : raw32967step1Labels = labelEmbedding6 ∘ raw32967step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32967step1 raw32967step1Labels raw32967step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw32968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32968step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw32968step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32968step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32968step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32968step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32968 raw32968Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw32968 raw32968Labels = mixedMoment B raw32968step0 raw32968step0Labels := by
      have hz : ∀ j, raw32968 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32968step0 = (fun i j => raw32968 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32968step0 raw32968; decide +kernel
      have hl : raw32968step0Labels = raw32968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32968 raw32968Labels permutation434 hz
    mixedMoment B raw32968step0 raw32968step0Labels = mixedMoment B raw32968step1 raw32968step1Labels := by
      have ha : raw32968step1 = (fun i j => raw32968step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32968step1 raw32968step0; decide +kernel
      have hl : raw32968step1Labels = raw32968step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32968step0 raw32968step0Labels permutation151 permutation3
    mixedMoment B raw32968step1 raw32968step1Labels = mixedMoment B raw32968step2 raw32968step2Labels := by
      have ha : raw32968step2 = -raw32968step1 := by apply Matrix.ext; change ∀ i j, raw32968step2 i j = -(raw32968step1 i j); unfold raw32968step2 raw32968step1; decide +kernel
      have hl : raw32968step2Labels = raw32968step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32968step2 raw32968step2Labels = mixedMoment B raw32968step3 raw32968step3Labels := by
      have ha : raw32968step3 = raw32968step2 := by apply Matrix.ext; unfold raw32968step3 raw32968step2; decide +kernel
      have hl : raw32968step2Labels = labelEmbedding6 ∘ raw32968step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32968step2 raw32968step2Labels raw32968step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw32969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw32969step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32969step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32969step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32969step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32969 raw32969Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw32969 raw32969Labels = mixedMoment B raw32969step0 raw32969step0Labels := by
      have ha : raw32969step0 = (fun i j => raw32969 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32969step0 raw32969; decide +kernel
      have hl : raw32969step0Labels = raw32969Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32969 raw32969Labels permutation658 permutation3
    mixedMoment B raw32969step0 raw32969step0Labels = mixedMoment B raw32969step1 raw32969step1Labels := by
      have ha : raw32969step1 = -raw32969step0 := by apply Matrix.ext; change ∀ i j, raw32969step1 i j = -(raw32969step0 i j); unfold raw32969step1 raw32969step0; decide +kernel
      have hl : raw32969step1Labels = raw32969step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32969step1 raw32969step1Labels = mixedMoment B raw32969step2 raw32969step2Labels := by
      have ha : raw32969step2 = raw32969step1 := by apply Matrix.ext; unfold raw32969step2 raw32969step1; decide +kernel
      have hl : raw32969step1Labels = labelEmbedding6 ∘ raw32969step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32969step1 raw32969step1Labels raw32969step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw32970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32970 raw32970Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw32970 raw32970Labels = mixedMoment B raw32970step0 raw32970step0Labels := by
      have ha : raw32970step0 = (fun i j => raw32970 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32970step0 raw32970; decide +kernel
      have hl : raw32970step0Labels = raw32970Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32970 raw32970Labels permutation153 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw32971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32971step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32971 raw32971Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw32971 raw32971Labels = mixedMoment B raw32971step0 raw32971step0Labels := by
      have ha : raw32971step0 = (fun i j => raw32971 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32971step0 raw32971; decide +kernel
      have hl : raw32971step0Labels = raw32971Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32971 raw32971Labels permutation178 permutation3
    mixedMoment B raw32971step0 raw32971step0Labels = mixedMoment B raw32971step1 raw32971step1Labels := by
      have ha : raw32971step1 = raw32971step0 := by apply Matrix.ext; unfold raw32971step1 raw32971step0; decide +kernel
      have hl : raw32971step0Labels = labelEmbedding6 ∘ raw32971step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32971step0 raw32971step0Labels raw32971step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

def raw32972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32972step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32972step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32972step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32972 raw32972Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw32972 raw32972Labels = mixedMoment B raw32972step0 raw32972step0Labels := by
      have ha : raw32972step0 = (fun i j => raw32972 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32972step0 raw32972; decide +kernel
      have hl : raw32972step0Labels = raw32972Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32972 raw32972Labels permutation178 permutation3
    mixedMoment B raw32972step0 raw32972step0Labels = mixedMoment B raw32972step1 raw32972step1Labels := by
      have ha : raw32972step1 = raw32972step0 := by apply Matrix.ext; unfold raw32972step1 raw32972step0; decide +kernel
      have hl : raw32972step0Labels = labelEmbedding6 ∘ raw32972step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32972step0 raw32972step0Labels raw32972step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

def raw32973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32973step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32973step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32973 raw32973Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw32973 raw32973Labels = mixedMoment B raw32973step0 raw32973step0Labels := by
      have hz : ∀ j, raw32973 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32973step0 = (fun i j => raw32973 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32973step0 raw32973; decide +kernel
      have hl : raw32973step0Labels = raw32973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32973 raw32973Labels permutation434 hz
    mixedMoment B raw32973step0 raw32973step0Labels = mixedMoment B raw32973step1 raw32973step1Labels := by
      have ha : raw32973step1 = (fun i j => raw32973step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32973step1 raw32973step0; decide +kernel
      have hl : raw32973step1Labels = raw32973step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32973step0 raw32973step0Labels permutation38 permutation3
    mixedMoment B raw32973step1 raw32973step1Labels = mixedMoment B raw32973step2 raw32973step2Labels := by
      have ha : raw32973step2 = raw32973step1 := by apply Matrix.ext; unfold raw32973step2 raw32973step1; decide +kernel
      have hl : raw32973step1Labels = labelEmbedding6 ∘ raw32973step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32973step1 raw32973step1Labels raw32973step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw32974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32974step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32974 raw32974Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw32974 raw32974Labels = mixedMoment B raw32974step0 raw32974step0Labels := by
      have ha : raw32974step0 = (fun i j => raw32974 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32974step0 raw32974; decide +kernel
      have hl : raw32974step0Labels = raw32974Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32974 raw32974Labels permutation188 permutation3
    mixedMoment B raw32974step0 raw32974step0Labels = mixedMoment B raw32974step1 raw32974step1Labels := by
      have ha : raw32974step1 = raw32974step0 := by apply Matrix.ext; unfold raw32974step1 raw32974step0; decide +kernel
      have hl : raw32974step0Labels = labelEmbedding6 ∘ raw32974step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32974step0 raw32974step0Labels raw32974step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

def raw32975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32975step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32975step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32975 raw32975Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw32975 raw32975Labels = mixedMoment B raw32975step0 raw32975step0Labels := by
      have ha : raw32975step0 = (fun i j => raw32975 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32975step0 raw32975; decide +kernel
      have hl : raw32975step0Labels = raw32975Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32975 raw32975Labels permutation178 permutation3
    mixedMoment B raw32975step0 raw32975step0Labels = mixedMoment B raw32975step1 raw32975step1Labels := by
      have ha : raw32975step1 = raw32975step0 := by apply Matrix.ext; unfold raw32975step1 raw32975step0; decide +kernel
      have hl : raw32975step0Labels = labelEmbedding6 ∘ raw32975step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32975step0 raw32975step0Labels raw32975step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw32976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32976step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32976step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32976step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32976 raw32976Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw32976 raw32976Labels = mixedMoment B raw32976step0 raw32976step0Labels := by
      have ha : raw32976step0 = (fun i j => raw32976 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32976step0 raw32976; decide +kernel
      have hl : raw32976step0Labels = raw32976Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32976 raw32976Labels permutation154 permutation3
    mixedMoment B raw32976step0 raw32976step0Labels = mixedMoment B raw32976step1 raw32976step1Labels := by
      have ha : raw32976step1 = raw32976step0 := by apply Matrix.ext; unfold raw32976step1 raw32976step0; decide +kernel
      have hl : raw32976step0Labels = labelEmbedding6 ∘ raw32976step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32976step0 raw32976step0Labels raw32976step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4341 node4341Labels := by rfl

def raw32977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32977step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32977step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32977step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32977step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32977 raw32977Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw32977 raw32977Labels = mixedMoment B raw32977step0 raw32977step0Labels := by
      have ha : raw32977step0 = (fun i j => raw32977 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32977step0 raw32977; decide +kernel
      have hl : raw32977step0Labels = raw32977Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32977 raw32977Labels permutation154 permutation3
    mixedMoment B raw32977step0 raw32977step0Labels = mixedMoment B raw32977step1 raw32977step1Labels := by
      have ha : raw32977step1 = raw32977step0 := by apply Matrix.ext; unfold raw32977step1 raw32977step0; decide +kernel
      have hl : raw32977step0Labels = labelEmbedding6 ∘ raw32977step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32977step0 raw32977step0Labels raw32977step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

def raw32978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32978step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32978step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32978step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32978 raw32978Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw32978 raw32978Labels = mixedMoment B raw32978step0 raw32978step0Labels := by
      have hz : ∀ j, raw32978 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32978step0 = (fun i j => raw32978 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32978step0 raw32978; decide +kernel
      have hl : raw32978step0Labels = raw32978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32978 raw32978Labels permutation434 hz
    mixedMoment B raw32978step0 raw32978step0Labels = mixedMoment B raw32978step1 raw32978step1Labels := by
      have ha : raw32978step1 = (fun i j => raw32978step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32978step1 raw32978step0; decide +kernel
      have hl : raw32978step1Labels = raw32978step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32978step0 raw32978step0Labels permutation32 permutation3
    mixedMoment B raw32978step1 raw32978step1Labels = mixedMoment B raw32978step2 raw32978step2Labels := by
      have ha : raw32978step2 = raw32978step1 := by apply Matrix.ext; unfold raw32978step2 raw32978step1; decide +kernel
      have hl : raw32978step1Labels = labelEmbedding6 ∘ raw32978step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32978step1 raw32978step1Labels raw32978step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw32979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32979step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32979step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32979step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32979 raw32979Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw32979 raw32979Labels = mixedMoment B raw32979step0 raw32979step0Labels := by
      have ha : raw32979step0 = (fun i j => raw32979 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32979step0 raw32979; decide +kernel
      have hl : raw32979step0Labels = raw32979Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32979 raw32979Labels permutation164 permutation3
    mixedMoment B raw32979step0 raw32979step0Labels = mixedMoment B raw32979step1 raw32979step1Labels := by
      have ha : raw32979step1 = raw32979step0 := by apply Matrix.ext; unfold raw32979step1 raw32979step0; decide +kernel
      have hl : raw32979step0Labels = labelEmbedding6 ∘ raw32979step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32979step0 raw32979step0Labels raw32979step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw32980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32980step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32980step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32980step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32980 raw32980Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw32980 raw32980Labels = mixedMoment B raw32980step0 raw32980step0Labels := by
      have ha : raw32980step0 = (fun i j => raw32980 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32980step0 raw32980; decide +kernel
      have hl : raw32980step0Labels = raw32980Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32980 raw32980Labels permutation154 permutation3
    mixedMoment B raw32980step0 raw32980step0Labels = mixedMoment B raw32980step1 raw32980step1Labels := by
      have ha : raw32980step1 = raw32980step0 := by apply Matrix.ext; unfold raw32980step1 raw32980step0; decide +kernel
      have hl : raw32980step0Labels = labelEmbedding6 ∘ raw32980step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32980step0 raw32980step0Labels raw32980step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5167 node5167Labels := by rfl

def raw32981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw32981step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32981step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw32981step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32981 raw32981Labels = mixedMoment B node4321 node4321Labels := by
  calc
    mixedMoment B raw32981 raw32981Labels = mixedMoment B raw32981step0 raw32981step0Labels := by
      have ha : raw32981step0 = (fun i j => raw32981 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32981step0 raw32981; decide +kernel
      have hl : raw32981step0Labels = raw32981Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32981 raw32981Labels permutation154 permutation3
    mixedMoment B raw32981step0 raw32981step0Labels = mixedMoment B raw32981step1 raw32981step1Labels := by
      have ha : raw32981step1 = raw32981step0 := by apply Matrix.ext; unfold raw32981step1 raw32981step0; decide +kernel
      have hl : raw32981step0Labels = labelEmbedding6 ∘ raw32981step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32981step0 raw32981step0Labels raw32981step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4321 node4321Labels := by rfl

def raw32982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw32982step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw32982step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32982 raw32982Labels = mixedMoment B node4926 node4926Labels := by
  calc
    mixedMoment B raw32982 raw32982Labels = mixedMoment B raw32982step0 raw32982step0Labels := by
      have ha : raw32982step0 = (fun i j => raw32982 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32982step0 raw32982; decide +kernel
      have hl : raw32982step0Labels = raw32982Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32982 raw32982Labels permutation154 permutation3
    mixedMoment B raw32982step0 raw32982step0Labels = mixedMoment B raw32982step1 raw32982step1Labels := by
      have ha : raw32982step1 = raw32982step0 := by apply Matrix.ext; unfold raw32982step1 raw32982step0; decide +kernel
      have hl : raw32982step0Labels = labelEmbedding6 ∘ raw32982step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32982step0 raw32982step0Labels raw32982step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4926 node4926Labels := by rfl

def raw32983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw32983step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw32983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32983 raw32983Labels = mixedMoment B node4985 node4985Labels := by
  calc
    mixedMoment B raw32983 raw32983Labels = mixedMoment B raw32983step0 raw32983step0Labels := by
      have ha : raw32983step0 = (fun i j => raw32983 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32983step0 raw32983; decide +kernel
      have hl : raw32983step0Labels = raw32983Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32983 raw32983Labels permutation178 permutation3
    mixedMoment B raw32983step0 raw32983step0Labels = mixedMoment B raw32983step1 raw32983step1Labels := by
      have ha : raw32983step1 = raw32983step0 := by apply Matrix.ext; unfold raw32983step1 raw32983step0; decide +kernel
      have hl : raw32983step0Labels = labelEmbedding6 ∘ raw32983step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32983step0 raw32983step0Labels raw32983step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4985 node4985Labels := by rfl

def raw32984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32984step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32984step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32984 raw32984Labels = mixedMoment B node5126 node5126Labels := by
  calc
    mixedMoment B raw32984 raw32984Labels = mixedMoment B raw32984step0 raw32984step0Labels := by
      have ha : raw32984step0 = (fun i j => raw32984 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32984step0 raw32984; decide +kernel
      have hl : raw32984step0Labels = raw32984Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32984 raw32984Labels permutation154 permutation3
    mixedMoment B raw32984step0 raw32984step0Labels = mixedMoment B raw32984step1 raw32984step1Labels := by
      have ha : raw32984step1 = raw32984step0 := by apply Matrix.ext; unfold raw32984step1 raw32984step0; decide +kernel
      have hl : raw32984step0Labels = labelEmbedding6 ∘ raw32984step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32984step0 raw32984step0Labels raw32984step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5126 node5126Labels := by rfl

def raw32985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32985step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32985step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32985 raw32985Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw32985 raw32985Labels = mixedMoment B raw32985step0 raw32985step0Labels := by
      have ha : raw32985step0 = (fun i j => raw32985 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32985step0 raw32985; decide +kernel
      have hl : raw32985step0Labels = raw32985Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32985 raw32985Labels permutation155 permutation3
    mixedMoment B raw32985step0 raw32985step0Labels = mixedMoment B raw32985step1 raw32985step1Labels := by
      have ha : raw32985step1 = raw32985step0 := by apply Matrix.ext; unfold raw32985step1 raw32985step0; decide +kernel
      have hl : raw32985step0Labels = labelEmbedding6 ∘ raw32985step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32985step0 raw32985step0Labels raw32985step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw32986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32986step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32986 raw32986Labels = mixedMoment B node4323 node4323Labels := by
  calc
    mixedMoment B raw32986 raw32986Labels = mixedMoment B raw32986step0 raw32986step0Labels := by
      have ha : raw32986step0 = (fun i j => raw32986 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32986step0 raw32986; decide +kernel
      have hl : raw32986step0Labels = raw32986Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32986 raw32986Labels permutation152 permutation3
    mixedMoment B raw32986step0 raw32986step0Labels = mixedMoment B raw32986step1 raw32986step1Labels := by
      have ha : raw32986step1 = raw32986step0 := by apply Matrix.ext; unfold raw32986step1 raw32986step0; decide +kernel
      have hl : raw32986step0Labels = labelEmbedding6 ∘ raw32986step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32986step0 raw32986step0Labels raw32986step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4323 node4323Labels := by rfl

def raw32987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32987step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32987step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32987 raw32987Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw32987 raw32987Labels = mixedMoment B raw32987step0 raw32987step0Labels := by
      have ha : raw32987step0 = (fun i j => raw32987 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32987step0 raw32987; decide +kernel
      have hl : raw32987step0Labels = raw32987Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32987 raw32987Labels permutation152 permutation3
    mixedMoment B raw32987step0 raw32987step0Labels = mixedMoment B raw32987step1 raw32987step1Labels := by
      have ha : raw32987step1 = raw32987step0 := by apply Matrix.ext; unfold raw32987step1 raw32987step0; decide +kernel
      have hl : raw32987step0Labels = labelEmbedding6 ∘ raw32987step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32987step0 raw32987step0Labels raw32987step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4928 node4928Labels := by rfl

def raw32988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32988step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32988step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32988 raw32988Labels = mixedMoment B node4987 node4987Labels := by
  calc
    mixedMoment B raw32988 raw32988Labels = mixedMoment B raw32988step0 raw32988step0Labels := by
      have ha : raw32988step0 = (fun i j => raw32988 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32988step0 raw32988; decide +kernel
      have hl : raw32988step0Labels = raw32988Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32988 raw32988Labels permutation176 permutation3
    mixedMoment B raw32988step0 raw32988step0Labels = mixedMoment B raw32988step1 raw32988step1Labels := by
      have ha : raw32988step1 = raw32988step0 := by apply Matrix.ext; unfold raw32988step1 raw32988step0; decide +kernel
      have hl : raw32988step0Labels = labelEmbedding6 ∘ raw32988step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32988step0 raw32988step0Labels raw32988step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4987 node4987Labels := by rfl

def raw32989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32989step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32989step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32989step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32989step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32989 raw32989Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw32989 raw32989Labels = mixedMoment B raw32989step0 raw32989step0Labels := by
      have hz : ∀ j, raw32989 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32989step0 = (fun i j => raw32989 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32989step0 raw32989; decide +kernel
      have hl : raw32989step0Labels = raw32989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32989 raw32989Labels permutation434 hz
    mixedMoment B raw32989step0 raw32989step0Labels = mixedMoment B raw32989step1 raw32989step1Labels := by
      have ha : raw32989step1 = (fun i j => raw32989step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32989step1 raw32989step0; decide +kernel
      have hl : raw32989step1Labels = raw32989step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32989step0 raw32989step0Labels permutation32 permutation3
    mixedMoment B raw32989step1 raw32989step1Labels = mixedMoment B raw32989step2 raw32989step2Labels := by
      have ha : raw32989step2 = raw32989step1 := by apply Matrix.ext; unfold raw32989step2 raw32989step1; decide +kernel
      have hl : raw32989step1Labels = labelEmbedding6 ∘ raw32989step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32989step1 raw32989step1Labels raw32989step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw32990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw32990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32990step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32990step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32990step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32990 raw32990Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw32990 raw32990Labels = mixedMoment B raw32990step0 raw32990step0Labels := by
      have ha : raw32990step0 = (fun i j => raw32990 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32990step0 raw32990; decide +kernel
      have hl : raw32990step0Labels = raw32990Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32990 raw32990Labels permutation153 permutation3
    mixedMoment B raw32990step0 raw32990step0Labels = mixedMoment B raw32990step1 raw32990step1Labels := by
      have ha : raw32990step1 = raw32990step0 := by apply Matrix.ext; unfold raw32990step1 raw32990step0; decide +kernel
      have hl : raw32990step0Labels = labelEmbedding6 ∘ raw32990step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32990step0 raw32990step0Labels raw32990step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

def raw32991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw32991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw32991step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32991step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw32991step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32991 raw32991Labels = mixedMoment B node4320 node4320Labels := by
  calc
    mixedMoment B raw32991 raw32991Labels = mixedMoment B raw32991step0 raw32991step0Labels := by
      have ha : raw32991step0 = (fun i j => raw32991 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32991step0 raw32991; decide +kernel
      have hl : raw32991step0Labels = raw32991Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32991 raw32991Labels permutation154 permutation3
    mixedMoment B raw32991step0 raw32991step0Labels = mixedMoment B raw32991step1 raw32991step1Labels := by
      have ha : raw32991step1 = raw32991step0 := by apply Matrix.ext; unfold raw32991step1 raw32991step0; decide +kernel
      have hl : raw32991step0Labels = labelEmbedding6 ∘ raw32991step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32991step0 raw32991step0Labels raw32991step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4320 node4320Labels := by rfl

def raw32992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw32992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw32992step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32992step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw32992step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32992step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw32992step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32992 raw32992Labels = mixedMoment B node4706 node4706Labels := by
  calc
    mixedMoment B raw32992 raw32992Labels = mixedMoment B raw32992step0 raw32992step0Labels := by
      have ha : raw32992step0 = (fun i j => raw32992 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32992step0 raw32992; decide +kernel
      have hl : raw32992step0Labels = raw32992Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32992 raw32992Labels permutation664 permutation3
    mixedMoment B raw32992step0 raw32992step0Labels = mixedMoment B raw32992step1 raw32992step1Labels := by
      have ha : raw32992step1 = -raw32992step0 := by apply Matrix.ext; change ∀ i j, raw32992step1 i j = -(raw32992step0 i j); unfold raw32992step1 raw32992step0; decide +kernel
      have hl : raw32992step1Labels = raw32992step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32992step1 raw32992step1Labels = mixedMoment B raw32992step2 raw32992step2Labels := by
      have ha : raw32992step2 = raw32992step1 := by apply Matrix.ext; unfold raw32992step2 raw32992step1; decide +kernel
      have hl : raw32992step1Labels = labelEmbedding6 ∘ raw32992step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32992step1 raw32992step1Labels raw32992step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4706 node4706Labels := by rfl

def raw32993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw32993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw32993step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32993step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw32993step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32993step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw32993step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32993 raw32993Labels = mixedMoment B node4709 node4709Labels := by
  calc
    mixedMoment B raw32993 raw32993Labels = mixedMoment B raw32993step0 raw32993step0Labels := by
      have ha : raw32993step0 = (fun i j => raw32993 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32993step0 raw32993; decide +kernel
      have hl : raw32993step0Labels = raw32993Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32993 raw32993Labels permutation662 permutation3
    mixedMoment B raw32993step0 raw32993step0Labels = mixedMoment B raw32993step1 raw32993step1Labels := by
      have ha : raw32993step1 = -raw32993step0 := by apply Matrix.ext; change ∀ i j, raw32993step1 i j = -(raw32993step0 i j); unfold raw32993step1 raw32993step0; decide +kernel
      have hl : raw32993step1Labels = raw32993step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32993step1 raw32993step1Labels = mixedMoment B raw32993step2 raw32993step2Labels := by
      have ha : raw32993step2 = raw32993step1 := by apply Matrix.ext; unfold raw32993step2 raw32993step1; decide +kernel
      have hl : raw32993step1Labels = labelEmbedding6 ∘ raw32993step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32993step1 raw32993step1Labels raw32993step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4709 node4709Labels := by rfl

def raw32994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw32994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw32994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw32994step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32994step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32994step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32994step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32994 raw32994Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw32994 raw32994Labels = mixedMoment B raw32994step0 raw32994step0Labels := by
      have hz : ∀ j, raw32994 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32994step0 = (fun i j => raw32994 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32994step0 raw32994; decide +kernel
      have hl : raw32994step0Labels = raw32994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32994 raw32994Labels permutation434 hz
    mixedMoment B raw32994step0 raw32994step0Labels = mixedMoment B raw32994step1 raw32994step1Labels := by
      have ha : raw32994step1 = (fun i j => raw32994step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32994step1 raw32994step0; decide +kernel
      have hl : raw32994step1Labels = raw32994step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32994step0 raw32994step0Labels permutation151 permutation3
    mixedMoment B raw32994step1 raw32994step1Labels = mixedMoment B raw32994step2 raw32994step2Labels := by
      have ha : raw32994step2 = -raw32994step1 := by apply Matrix.ext; change ∀ i j, raw32994step2 i j = -(raw32994step1 i j); unfold raw32994step2 raw32994step1; decide +kernel
      have hl : raw32994step2Labels = raw32994step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32994step2 raw32994step2Labels = mixedMoment B raw32994step3 raw32994step3Labels := by
      have ha : raw32994step3 = raw32994step2 := by apply Matrix.ext; unfold raw32994step3 raw32994step2; decide +kernel
      have hl : raw32994step2Labels = labelEmbedding6 ∘ raw32994step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32994step2 raw32994step2Labels raw32994step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw32995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw32995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32995step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw32995step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32995step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32995step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32995step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32995step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32995 raw32995Labels = mixedMoment B node4728 node4728Labels := by
  calc
    mixedMoment B raw32995 raw32995Labels = mixedMoment B raw32995step0 raw32995step0Labels := by
      have ha : raw32995step0 = (fun i j => raw32995 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32995step0 raw32995; decide +kernel
      have hl : raw32995step0Labels = raw32995Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32995 raw32995Labels permutation658 permutation3
    mixedMoment B raw32995step0 raw32995step0Labels = mixedMoment B raw32995step1 raw32995step1Labels := by
      have ha : raw32995step1 = -raw32995step0 := by apply Matrix.ext; change ∀ i j, raw32995step1 i j = -(raw32995step0 i j); unfold raw32995step1 raw32995step0; decide +kernel
      have hl : raw32995step1Labels = raw32995step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32995step1 raw32995step1Labels = mixedMoment B raw32995step2 raw32995step2Labels := by
      have ha : raw32995step2 = raw32995step1 := by apply Matrix.ext; unfold raw32995step2 raw32995step1; decide +kernel
      have hl : raw32995step1Labels = labelEmbedding6 ∘ raw32995step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32995step1 raw32995step1Labels raw32995step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4728 node4728Labels := by rfl

def raw32996 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32996step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32996step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32996step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32996 raw32996Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw32996 raw32996Labels = mixedMoment B raw32996step0 raw32996step0Labels := by
      have ha : raw32996step0 = (fun i j => raw32996 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32996step0 raw32996; decide +kernel
      have hl : raw32996step0Labels = raw32996Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32996 raw32996Labels permutation152 permutation7
    mixedMoment B raw32996step0 raw32996step0Labels = mixedMoment B raw32996step1 raw32996step1Labels := by
      have ha : raw32996step1 = raw32996step0 := by apply Matrix.ext; unfold raw32996step1 raw32996step0; decide +kernel
      have hl : raw32996step0Labels = labelEmbedding10 ∘ raw32996step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32996step0 raw32996step0Labels raw32996step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw32997 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32997Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32997step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32997step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32997step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32997 raw32997Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw32997 raw32997Labels = mixedMoment B raw32997step0 raw32997step0Labels := by
      have ha : raw32997step0 = (fun i j => raw32997 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32997step0 raw32997; decide +kernel
      have hl : raw32997step0Labels = raw32997Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32997 raw32997Labels permutation152 permutation7
    mixedMoment B raw32997step0 raw32997step0Labels = mixedMoment B raw32997step1 raw32997step1Labels := by
      have ha : raw32997step1 = raw32997step0 := by apply Matrix.ext; unfold raw32997step1 raw32997step0; decide +kernel
      have hl : raw32997step0Labels = labelEmbedding10 ∘ raw32997step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32997step0 raw32997step0Labels raw32997step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5086 node5086Labels := by rfl

def raw32998 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32998step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32998step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32998step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32998 raw32998Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw32998 raw32998Labels = mixedMoment B raw32998step0 raw32998step0Labels := by
      have ha : raw32998step0 = (fun i j => raw32998 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32998step0 raw32998; decide +kernel
      have hl : raw32998step0Labels = raw32998Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32998 raw32998Labels permutation152 permutation7
    mixedMoment B raw32998step0 raw32998step0Labels = mixedMoment B raw32998step1 raw32998step1Labels := by
      have ha : raw32998step1 = raw32998step0 := by apply Matrix.ext; unfold raw32998step1 raw32998step0; decide +kernel
      have hl : raw32998step0Labels = labelEmbedding10 ∘ raw32998step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32998step0 raw32998step0Labels raw32998step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5076 node5076Labels := by rfl

def raw32999 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32999step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32999step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32999step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32999step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32999step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32999 raw32999Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw32999 raw32999Labels = mixedMoment B raw32999step0 raw32999step0Labels := by
      have ha : raw32999step0 = (fun i j => raw32999 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32999step0 raw32999; decide +kernel
      have hl : raw32999step0Labels = raw32999Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32999 raw32999Labels permutation188 permutation4
    mixedMoment B raw32999step0 raw32999step0Labels = mixedMoment B raw32999step1 raw32999step1Labels := by
      have ha : raw32999step1 = -raw32999step0 := by apply Matrix.ext; change ∀ i j, raw32999step1 i j = -(raw32999step0 i j); unfold raw32999step1 raw32999step0; decide +kernel
      have hl : raw32999step1Labels = raw32999step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32999step1 raw32999step1Labels = mixedMoment B raw32999step2 raw32999step2Labels := by
      have ha : raw32999step2 = raw32999step1 := by apply Matrix.ext; unfold raw32999step2 raw32999step1; decide +kernel
      have hl : raw32999step1Labels = labelEmbedding7 ∘ raw32999step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32999step1 raw32999step1Labels raw32999step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

def raw33000 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33000step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33000step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33000step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33000 raw33000Labels = mixedMoment B node5178 node5178Labels := by
  calc
    mixedMoment B raw33000 raw33000Labels = mixedMoment B raw33000step0 raw33000step0Labels := by
      have ha : raw33000step0 = (fun i j => raw33000 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33000step0 raw33000; decide +kernel
      have hl : raw33000step0Labels = raw33000Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33000 raw33000Labels permutation154 permutation6
    mixedMoment B raw33000step0 raw33000step0Labels = mixedMoment B raw33000step1 raw33000step1Labels := by
      have ha : raw33000step1 = raw33000step0 := by apply Matrix.ext; unfold raw33000step1 raw33000step0; decide +kernel
      have hl : raw33000step0Labels = labelEmbedding9 ∘ raw33000step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33000step0 raw33000step0Labels raw33000step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5178 node5178Labels := by rfl

def raw33001 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33001step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33001step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33001step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33001 raw33001Labels = mixedMoment B node5184 node5184Labels := by
  calc
    mixedMoment B raw33001 raw33001Labels = mixedMoment B raw33001step0 raw33001step0Labels := by
      have ha : raw33001step0 = (fun i j => raw33001 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33001step0 raw33001; decide +kernel
      have hl : raw33001step0Labels = raw33001Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33001 raw33001Labels permutation152 permutation6
    mixedMoment B raw33001step0 raw33001step0Labels = mixedMoment B raw33001step1 raw33001step1Labels := by
      have ha : raw33001step1 = raw33001step0 := by apply Matrix.ext; unfold raw33001step1 raw33001step0; decide +kernel
      have hl : raw33001step0Labels = labelEmbedding9 ∘ raw33001step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33001step0 raw33001step0Labels raw33001step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5184 node5184Labels := by rfl

def raw33002 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw33002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw33002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33002step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33002step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33002 raw33002Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw33002 raw33002Labels = mixedMoment B raw33002step0 raw33002step0Labels := by
      have hz : ∀ j, raw33002 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33002step0 = (fun i j => raw33002 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33002step0 raw33002; decide +kernel
      have hl : raw33002step0Labels = raw33002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33002 raw33002Labels permutation346 hz
    mixedMoment B raw33002step0 raw33002step0Labels = mixedMoment B raw33002step1 raw33002step1Labels := by
      have ha : raw33002step1 = (fun i j => raw33002step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33002step1 raw33002step0; decide +kernel
      have hl : raw33002step1Labels = raw33002step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33002step0 raw33002step0Labels permutation34 permutation6
    mixedMoment B raw33002step1 raw33002step1Labels = mixedMoment B raw33002step2 raw33002step2Labels := by
      have ha : raw33002step2 = raw33002step1 := by apply Matrix.ext; unfold raw33002step2 raw33002step1; decide +kernel
      have hl : raw33002step1Labels = labelEmbedding9 ∘ raw33002step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33002step1 raw33002step1Labels raw33002step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw33003 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw33003step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33003step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33003step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33003step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33003step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33003 raw33003Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw33003 raw33003Labels = mixedMoment B raw33003step0 raw33003step0Labels := by
      have ha : raw33003step0 = (fun i j => raw33003 (permutation178 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33003step0 raw33003; decide +kernel
      have hl : raw33003step0Labels = raw33003Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33003 raw33003Labels permutation178 permutation4
    mixedMoment B raw33003step0 raw33003step0Labels = mixedMoment B raw33003step1 raw33003step1Labels := by
      have ha : raw33003step1 = -raw33003step0 := by apply Matrix.ext; change ∀ i j, raw33003step1 i j = -(raw33003step0 i j); unfold raw33003step1 raw33003step0; decide +kernel
      have hl : raw33003step1Labels = raw33003step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33003step1 raw33003step1Labels = mixedMoment B raw33003step2 raw33003step2Labels := by
      have ha : raw33003step2 = raw33003step1 := by apply Matrix.ext; unfold raw33003step2 raw33003step1; decide +kernel
      have hl : raw33003step1Labels = labelEmbedding7 ∘ raw33003step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33003step1 raw33003step1Labels raw33003step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

def raw33004 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw33004step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33004step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw33004step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33004 raw33004Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw33004 raw33004Labels = mixedMoment B raw33004step0 raw33004step0Labels := by
      have ha : raw33004step0 = (fun i j => raw33004 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33004step0 raw33004; decide +kernel
      have hl : raw33004step0Labels = raw33004Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33004 raw33004Labels permutation154 permutation6
    mixedMoment B raw33004step0 raw33004step0Labels = mixedMoment B raw33004step1 raw33004step1Labels := by
      have ha : raw33004step1 = raw33004step0 := by apply Matrix.ext; unfold raw33004step1 raw33004step0; decide +kernel
      have hl : raw33004step0Labels = labelEmbedding9 ∘ raw33004step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33004step0 raw33004step0Labels raw33004step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw33005 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 2, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw33005step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw33005step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33005 raw33005Labels = mixedMoment B node5122 node5122Labels := by
  calc
    mixedMoment B raw33005 raw33005Labels = mixedMoment B raw33005step0 raw33005step0Labels := by
      have ha : raw33005step0 = (fun i j => raw33005 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33005step0 raw33005; decide +kernel
      have hl : raw33005step0Labels = raw33005Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33005 raw33005Labels permutation154 permutation6
    mixedMoment B raw33005step0 raw33005step0Labels = mixedMoment B raw33005step1 raw33005step1Labels := by
      have ha : raw33005step1 = raw33005step0 := by apply Matrix.ext; unfold raw33005step1 raw33005step0; decide +kernel
      have hl : raw33005step0Labels = labelEmbedding9 ∘ raw33005step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33005step0 raw33005step0Labels raw33005step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5122 node5122Labels := by rfl

def raw33006 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw33006step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33006step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33006step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33006step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33006step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33006 raw33006Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw33006 raw33006Labels = mixedMoment B raw33006step0 raw33006step0Labels := by
      have ha : raw33006step0 = (fun i j => raw33006 (permutation178 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33006step0 raw33006; decide +kernel
      have hl : raw33006step0Labels = raw33006Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33006 raw33006Labels permutation178 permutation4
    mixedMoment B raw33006step0 raw33006step0Labels = mixedMoment B raw33006step1 raw33006step1Labels := by
      have ha : raw33006step1 = -raw33006step0 := by apply Matrix.ext; change ∀ i j, raw33006step1 i j = -(raw33006step0 i j); unfold raw33006step1 raw33006step0; decide +kernel
      have hl : raw33006step1Labels = raw33006step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33006step1 raw33006step1Labels = mixedMoment B raw33006step2 raw33006step2Labels := by
      have ha : raw33006step2 = raw33006step1 := by apply Matrix.ext; unfold raw33006step2 raw33006step1; decide +kernel
      have hl : raw33006step1Labels = labelEmbedding7 ∘ raw33006step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33006step1 raw33006step1Labels raw33006step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4779 node4779Labels := by rfl

def raw33007 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33007step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33007step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33007step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33007 raw33007Labels = mixedMoment B node5055 node5055Labels := by
  calc
    mixedMoment B raw33007 raw33007Labels = mixedMoment B raw33007step0 raw33007step0Labels := by
      have ha : raw33007step0 = (fun i j => raw33007 (permutation664 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33007step0 raw33007; decide +kernel
      have hl : raw33007step0Labels = raw33007Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33007 raw33007Labels permutation664 permutation4
    mixedMoment B raw33007step0 raw33007step0Labels = mixedMoment B raw33007step1 raw33007step1Labels := by
      have ha : raw33007step1 = raw33007step0 := by apply Matrix.ext; unfold raw33007step1 raw33007step0; decide +kernel
      have hl : raw33007step0Labels = labelEmbedding7 ∘ raw33007step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33007step0 raw33007step0Labels raw33007step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5055 node5055Labels := by rfl

def raw33008 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw33008step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw33008step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33008 raw33008Labels = mixedMoment B node5049 node5049Labels := by
  calc
    mixedMoment B raw33008 raw33008Labels = mixedMoment B raw33008step0 raw33008step0Labels := by
      have ha : raw33008step0 = (fun i j => raw33008 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33008step0 raw33008; decide +kernel
      have hl : raw33008step0Labels = raw33008Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33008 raw33008Labels permutation662 permutation4
    mixedMoment B raw33008step0 raw33008step0Labels = mixedMoment B raw33008step1 raw33008step1Labels := by
      have ha : raw33008step1 = raw33008step0 := by apply Matrix.ext; unfold raw33008step1 raw33008step0; decide +kernel
      have hl : raw33008step0Labels = labelEmbedding7 ∘ raw33008step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33008step0 raw33008step0Labels raw33008step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5049 node5049Labels := by rfl

def raw33009 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33009step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33009step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33009step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33009 raw33009Labels = mixedMoment B node5133 node5133Labels := by
  calc
    mixedMoment B raw33009 raw33009Labels = mixedMoment B raw33009step0 raw33009step0Labels := by
      have ha : raw33009step0 = (fun i j => raw33009 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33009step0 raw33009; decide +kernel
      have hl : raw33009step0Labels = raw33009Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33009 raw33009Labels permutation152 permutation6
    mixedMoment B raw33009step0 raw33009step0Labels = mixedMoment B raw33009step1 raw33009step1Labels := by
      have ha : raw33009step1 = raw33009step0 := by apply Matrix.ext; unfold raw33009step1 raw33009step0; decide +kernel
      have hl : raw33009step0Labels = labelEmbedding9 ∘ raw33009step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33009step0 raw33009step0Labels raw33009step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5133 node5133Labels := by rfl

def raw33010 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33010 raw33010Labels = mixedMoment B node3370 node3370Labels := by
  calc
    mixedMoment B raw33010 raw33010Labels = mixedMoment B raw33010step0 raw33010step0Labels := by
      have ha : raw33010step0 = (fun i j => raw33010 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33010step0 raw33010; decide +kernel
      have hl : raw33010step0Labels = raw33010Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33010 raw33010Labels permutation176 permutation4
    mixedMoment B raw33010step0 raw33010step0Labels = mixedMoment B raw33010step1 raw33010step1Labels := by
      have ha : raw33010step1 = -raw33010step0 := by apply Matrix.ext; change ∀ i j, raw33010step1 i j = -(raw33010step0 i j); unfold raw33010step1 raw33010step0; decide +kernel
      have hl : raw33010step1Labels = raw33010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3370 node3370Labels := by rfl

def raw33011 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33011step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33011step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33011 raw33011Labels = mixedMoment B node1798 node1798Labels := by
  calc
    mixedMoment B raw33011 raw33011Labels = mixedMoment B raw33011step0 raw33011step0Labels := by
      have ha : raw33011step0 = (fun i j => raw33011 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33011step0 raw33011; decide +kernel
      have hl : raw33011step0Labels = raw33011Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33011 raw33011Labels permutation176 permutation4
    mixedMoment B raw33011step0 raw33011step0Labels = mixedMoment B raw33011step1 raw33011step1Labels := by
      have ha : raw33011step1 = -raw33011step0 := by apply Matrix.ext; change ∀ i j, raw33011step1 i j = -(raw33011step0 i j); unfold raw33011step1 raw33011step0; decide +kernel
      have hl : raw33011step1Labels = raw33011step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1798 node1798Labels := by rfl

def raw33012 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33012step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33012 raw33012Labels = mixedMoment B node1999 node1999Labels := by
  calc
    mixedMoment B raw33012 raw33012Labels = mixedMoment B raw33012step0 raw33012step0Labels := by
      have ha : raw33012step0 = (fun i j => raw33012 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33012step0 raw33012; decide +kernel
      have hl : raw33012step0Labels = raw33012Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33012 raw33012Labels permutation176 permutation4
    mixedMoment B raw33012step0 raw33012step0Labels = mixedMoment B raw33012step1 raw33012step1Labels := by
      have ha : raw33012step1 = -raw33012step0 := by apply Matrix.ext; change ∀ i j, raw33012step1 i j = -(raw33012step0 i j); unfold raw33012step1 raw33012step0; decide +kernel
      have hl : raw33012step1Labels = raw33012step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1999 node1999Labels := by rfl

def raw33013 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw33013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33013step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33013step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33013 raw33013Labels = mixedMoment B node1787 node1787Labels := by
  calc
    mixedMoment B raw33013 raw33013Labels = mixedMoment B raw33013step0 raw33013step0Labels := by
      have ha : raw33013step0 = (fun i j => raw33013 (permutation178 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33013step0 raw33013; decide +kernel
      have hl : raw33013step0Labels = raw33013Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33013 raw33013Labels permutation178 permutation4
    mixedMoment B raw33013step0 raw33013step0Labels = mixedMoment B raw33013step1 raw33013step1Labels := by
      have ha : raw33013step1 = -raw33013step0 := by apply Matrix.ext; change ∀ i j, raw33013step1 i j = -(raw33013step0 i j); unfold raw33013step1 raw33013step0; decide +kernel
      have hl : raw33013step1Labels = raw33013step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1787 node1787Labels := by rfl

def raw33014 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw33014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw33014step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33014step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33014step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33014 raw33014Labels = mixedMoment B node1787 node1787Labels := by
  calc
    mixedMoment B raw33014 raw33014Labels = mixedMoment B raw33014step0 raw33014step0Labels := by
      have ha : raw33014step0 = (fun i j => raw33014 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33014step0 raw33014; decide +kernel
      have hl : raw33014step0Labels = raw33014Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33014 raw33014Labels permutation176 permutation4
    mixedMoment B raw33014step0 raw33014step0Labels = mixedMoment B raw33014step1 raw33014step1Labels := by
      have ha : raw33014step1 = -raw33014step0 := by apply Matrix.ext; change ∀ i j, raw33014step1 i j = -(raw33014step0 i j); unfold raw33014step1 raw33014step0; decide +kernel
      have hl : raw33014step1Labels = raw33014step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1787 node1787Labels := by rfl

def raw33015 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw33015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33015step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw33015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33015step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33015step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33015 raw33015Labels = mixedMoment B node1786 node1786Labels := by
  calc
    mixedMoment B raw33015 raw33015Labels = mixedMoment B raw33015step0 raw33015step0Labels := by
      have ha : raw33015step0 = (fun i j => raw33015 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33015step0 raw33015; decide +kernel
      have hl : raw33015step0Labels = raw33015Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33015 raw33015Labels permutation176 permutation4
    mixedMoment B raw33015step0 raw33015step0Labels = mixedMoment B raw33015step1 raw33015step1Labels := by
      have ha : raw33015step1 = -raw33015step0 := by apply Matrix.ext; change ∀ i j, raw33015step1 i j = -(raw33015step0 i j); unfold raw33015step1 raw33015step0; decide +kernel
      have hl : raw33015step1Labels = raw33015step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1786 node1786Labels := by rfl

def raw33016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33016step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33016step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33016step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33016step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33016 raw33016Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw33016 raw33016Labels = mixedMoment B raw33016step0 raw33016step0Labels := by
      have ha : raw33016step0 = (fun i j => raw33016 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33016step0 raw33016; decide +kernel
      have hl : raw33016step0Labels = raw33016Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33016 raw33016Labels permutation156 permutation3
    mixedMoment B raw33016step0 raw33016step0Labels = mixedMoment B raw33016step1 raw33016step1Labels := by
      have ha : raw33016step1 = raw33016step0 := by apply Matrix.ext; unfold raw33016step1 raw33016step0; decide +kernel
      have hl : raw33016step0Labels = labelEmbedding6 ∘ raw33016step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33016step0 raw33016step0Labels raw33016step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

def raw33017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33017step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33017step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33017 raw33017Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw33017 raw33017Labels = mixedMoment B raw33017step0 raw33017step0Labels := by
      have hz : ∀ j, raw33017 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33017step0 = (fun i j => raw33017 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33017step0 raw33017; decide +kernel
      have hl : raw33017step0Labels = raw33017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33017 raw33017Labels permutation265 hz
    mixedMoment B raw33017step0 raw33017step0Labels = mixedMoment B raw33017step1 raw33017step1Labels := by
      have ha : raw33017step1 = (fun i j => raw33017step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33017step1 raw33017step0; decide +kernel
      have hl : raw33017step1Labels = raw33017step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33017step0 raw33017step0Labels permutation32 permutation3
    mixedMoment B raw33017step1 raw33017step1Labels = mixedMoment B raw33017step2 raw33017step2Labels := by
      have ha : raw33017step2 = raw33017step1 := by apply Matrix.ext; unfold raw33017step2 raw33017step1; decide +kernel
      have hl : raw33017step1Labels = labelEmbedding6 ∘ raw33017step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33017step1 raw33017step1Labels raw33017step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw33018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33018step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33018step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33018 raw33018Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw33018 raw33018Labels = mixedMoment B raw33018step0 raw33018step0Labels := by
      have hz : ∀ j, raw33018 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33018step0 = (fun i j => raw33018 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33018step0 raw33018; decide +kernel
      have hl : raw33018step0Labels = raw33018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33018 raw33018Labels permutation265 hz
    mixedMoment B raw33018step0 raw33018step0Labels = mixedMoment B raw33018step1 raw33018step1Labels := by
      have ha : raw33018step1 = (fun i j => raw33018step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33018step1 raw33018step0; decide +kernel
      have hl : raw33018step1Labels = raw33018step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33018step0 raw33018step0Labels permutation32 permutation3
    mixedMoment B raw33018step1 raw33018step1Labels = mixedMoment B raw33018step2 raw33018step2Labels := by
      have ha : raw33018step2 = raw33018step1 := by apply Matrix.ext; unfold raw33018step2 raw33018step1; decide +kernel
      have hl : raw33018step1Labels = labelEmbedding6 ∘ raw33018step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33018step1 raw33018step1Labels raw33018step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5172 node5172Labels := by rfl

def raw33019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33019step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33019step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33019step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33019step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33019step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33019step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33019 raw33019Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw33019 raw33019Labels = mixedMoment B raw33019step0 raw33019step0Labels := by
      have hz : ∀ j, raw33019 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33019step0 = (fun i j => raw33019 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33019step0 raw33019; decide +kernel
      have hl : raw33019step0Labels = raw33019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33019 raw33019Labels permutation520 hz
    mixedMoment B raw33019step0 raw33019step0Labels = mixedMoment B raw33019step1 raw33019step1Labels := by
      have hz : ∀ j, raw33019step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw33019step1 = (fun i j => raw33019step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw33019step1 raw33019step0; decide +kernel
      have hl : raw33019step1Labels = raw33019step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33019step0 raw33019step0Labels permutation56 hz
    mixedMoment B raw33019step1 raw33019step1Labels = mixedMoment B raw33019step2 raw33019step2Labels := by
      have ha : raw33019step2 = (fun i j => raw33019step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33019step2 raw33019step1; decide +kernel
      have hl : raw33019step2Labels = raw33019step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33019step1 raw33019step1Labels permutation8 permutation3
    mixedMoment B raw33019step2 raw33019step2Labels = mixedMoment B raw33019step3 raw33019step3Labels := by
      have ha : raw33019step3 = raw33019step2 := by apply Matrix.ext; unfold raw33019step3 raw33019step2; decide +kernel
      have hl : raw33019step2Labels = labelEmbedding6 ∘ raw33019step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33019step2 raw33019step2Labels raw33019step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw33020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33020step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33020step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33020step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33020 raw33020Labels = mixedMoment B node4307 node4307Labels := by
  calc
    mixedMoment B raw33020 raw33020Labels = mixedMoment B raw33020step0 raw33020step0Labels := by
      have ha : raw33020step0 = (fun i j => raw33020 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33020step0 raw33020; decide +kernel
      have hl : raw33020step0Labels = raw33020Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33020 raw33020Labels permutation160 permutation3
    mixedMoment B raw33020step0 raw33020step0Labels = mixedMoment B raw33020step1 raw33020step1Labels := by
      have ha : raw33020step1 = raw33020step0 := by apply Matrix.ext; unfold raw33020step1 raw33020step0; decide +kernel
      have hl : raw33020step0Labels = labelEmbedding6 ∘ raw33020step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33020step0 raw33020step0Labels raw33020step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4307 node4307Labels := by rfl

def raw33021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33021step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33021step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33021step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33021 raw33021Labels = mixedMoment B node4917 node4917Labels := by
  calc
    mixedMoment B raw33021 raw33021Labels = mixedMoment B raw33021step0 raw33021step0Labels := by
      have ha : raw33021step0 = (fun i j => raw33021 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33021step0 raw33021; decide +kernel
      have hl : raw33021step0Labels = raw33021Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33021 raw33021Labels permutation160 permutation3
    mixedMoment B raw33021step0 raw33021step0Labels = mixedMoment B raw33021step1 raw33021step1Labels := by
      have ha : raw33021step1 = raw33021step0 := by apply Matrix.ext; unfold raw33021step1 raw33021step0; decide +kernel
      have hl : raw33021step0Labels = labelEmbedding6 ∘ raw33021step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33021step0 raw33021step0Labels raw33021step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4917 node4917Labels := by rfl

def raw33022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33022step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33022step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33022 raw33022Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw33022 raw33022Labels = mixedMoment B raw33022step0 raw33022step0Labels := by
      have hz : ∀ j, raw33022 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33022step0 = (fun i j => raw33022 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33022step0 raw33022; decide +kernel
      have hl : raw33022step0Labels = raw33022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33022 raw33022Labels permutation520 hz
    mixedMoment B raw33022step0 raw33022step0Labels = mixedMoment B raw33022step1 raw33022step1Labels := by
      have ha : raw33022step1 = (fun i j => raw33022step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33022step1 raw33022step0; decide +kernel
      have hl : raw33022step1Labels = raw33022step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33022step0 raw33022step0Labels permutation34 permutation3
    mixedMoment B raw33022step1 raw33022step1Labels = mixedMoment B raw33022step2 raw33022step2Labels := by
      have ha : raw33022step2 = raw33022step1 := by apply Matrix.ext; unfold raw33022step2 raw33022step1; decide +kernel
      have hl : raw33022step1Labels = labelEmbedding6 ∘ raw33022step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33022step1 raw33022step1Labels raw33022step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw33023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33023step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33023step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33023 raw33023Labels = mixedMoment B node4291 node4291Labels := by
  calc
    mixedMoment B raw33023 raw33023Labels = mixedMoment B raw33023step0 raw33023step0Labels := by
      have ha : raw33023step0 = (fun i j => raw33023 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33023step0 raw33023; decide +kernel
      have hl : raw33023step0Labels = raw33023Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33023 raw33023Labels permutation155 permutation3
    mixedMoment B raw33023step0 raw33023step0Labels = mixedMoment B raw33023step1 raw33023step1Labels := by
      have ha : raw33023step1 = raw33023step0 := by apply Matrix.ext; unfold raw33023step1 raw33023step0; decide +kernel
      have hl : raw33023step0Labels = labelEmbedding6 ∘ raw33023step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33023step0 raw33023step0Labels raw33023step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4291 node4291Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
