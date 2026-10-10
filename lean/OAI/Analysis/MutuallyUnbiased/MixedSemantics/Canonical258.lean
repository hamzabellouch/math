import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw33024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33024step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33024step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33024step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33024 raw33024Labels = mixedMoment B node4905 node4905Labels := by
  calc
    mixedMoment B raw33024 raw33024Labels = mixedMoment B raw33024step0 raw33024step0Labels := by
      have ha : raw33024step0 = (fun i j => raw33024 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33024step0 raw33024; decide +kernel
      have hl : raw33024step0Labels = raw33024Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33024 raw33024Labels permutation155 permutation3
    mixedMoment B raw33024step0 raw33024step0Labels = mixedMoment B raw33024step1 raw33024step1Labels := by
      have ha : raw33024step1 = raw33024step0 := by apply Matrix.ext; unfold raw33024step1 raw33024step0; decide +kernel
      have hl : raw33024step0Labels = labelEmbedding6 ∘ raw33024step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33024step0 raw33024step0Labels raw33024step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4905 node4905Labels := by rfl

def raw33025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33025step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33025step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33025 raw33025Labels = mixedMoment B node5038 node5038Labels := by
  calc
    mixedMoment B raw33025 raw33025Labels = mixedMoment B raw33025step0 raw33025step0Labels := by
      have ha : raw33025step0 = (fun i j => raw33025 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33025step0 raw33025; decide +kernel
      have hl : raw33025step0Labels = raw33025Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33025 raw33025Labels permutation155 permutation3
    mixedMoment B raw33025step0 raw33025step0Labels = mixedMoment B raw33025step1 raw33025step1Labels := by
      have ha : raw33025step1 = raw33025step0 := by apply Matrix.ext; unfold raw33025step1 raw33025step0; decide +kernel
      have hl : raw33025step0Labels = labelEmbedding6 ∘ raw33025step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33025step0 raw33025step0Labels raw33025step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5038 node5038Labels := by rfl

def raw33026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw33026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33026step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33026step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33026step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33026 raw33026Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw33026 raw33026Labels = mixedMoment B raw33026step0 raw33026step0Labels := by
      have hz : ∀ j, raw33026 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33026step0 = (fun i j => raw33026 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33026step0 raw33026; decide +kernel
      have hl : raw33026step0Labels = raw33026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33026 raw33026Labels permutation520 hz
    mixedMoment B raw33026step0 raw33026step0Labels = mixedMoment B raw33026step1 raw33026step1Labels := by
      have ha : raw33026step1 = (fun i j => raw33026step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33026step1 raw33026step0; decide +kernel
      have hl : raw33026step1Labels = raw33026step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33026step0 raw33026step0Labels permutation33 permutation3
    mixedMoment B raw33026step1 raw33026step1Labels = mixedMoment B raw33026step2 raw33026step2Labels := by
      have ha : raw33026step2 = raw33026step1 := by apply Matrix.ext; unfold raw33026step2 raw33026step1; decide +kernel
      have hl : raw33026step1Labels = labelEmbedding6 ∘ raw33026step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33026step1 raw33026step1Labels raw33026step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw33027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw33027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33027step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33027step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33027 raw33027Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw33027 raw33027Labels = mixedMoment B raw33027step0 raw33027step0Labels := by
      have hz : ∀ j, raw33027 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33027step0 = (fun i j => raw33027 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33027step0 raw33027; decide +kernel
      have hl : raw33027step0Labels = raw33027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33027 raw33027Labels permutation434 hz
    mixedMoment B raw33027step0 raw33027step0Labels = mixedMoment B raw33027step1 raw33027step1Labels := by
      have ha : raw33027step1 = (fun i j => raw33027step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33027step1 raw33027step0; decide +kernel
      have hl : raw33027step1Labels = raw33027step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33027step0 raw33027step0Labels permutation33 permutation3
    mixedMoment B raw33027step1 raw33027step1Labels = mixedMoment B raw33027step2 raw33027step2Labels := by
      have ha : raw33027step2 = raw33027step1 := by apply Matrix.ext; unfold raw33027step2 raw33027step1; decide +kernel
      have hl : raw33027step1Labels = labelEmbedding6 ∘ raw33027step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33027step1 raw33027step1Labels raw33027step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw33028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33028step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33028step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33028 raw33028Labels = mixedMoment B node4290 node4290Labels := by
  calc
    mixedMoment B raw33028 raw33028Labels = mixedMoment B raw33028step0 raw33028step0Labels := by
      have ha : raw33028step0 = (fun i j => raw33028 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33028step0 raw33028; decide +kernel
      have hl : raw33028step0Labels = raw33028Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33028 raw33028Labels permutation152 permutation3
    mixedMoment B raw33028step0 raw33028step0Labels = mixedMoment B raw33028step1 raw33028step1Labels := by
      have ha : raw33028step1 = raw33028step0 := by apply Matrix.ext; unfold raw33028step1 raw33028step0; decide +kernel
      have hl : raw33028step0Labels = labelEmbedding6 ∘ raw33028step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33028step0 raw33028step0Labels raw33028step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4290 node4290Labels := by rfl

def raw33029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33029step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33029step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33029step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33029 raw33029Labels = mixedMoment B node4904 node4904Labels := by
  calc
    mixedMoment B raw33029 raw33029Labels = mixedMoment B raw33029step0 raw33029step0Labels := by
      have ha : raw33029step0 = (fun i j => raw33029 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33029step0 raw33029; decide +kernel
      have hl : raw33029step0Labels = raw33029Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33029 raw33029Labels permutation152 permutation3
    mixedMoment B raw33029step0 raw33029step0Labels = mixedMoment B raw33029step1 raw33029step1Labels := by
      have ha : raw33029step1 = raw33029step0 := by apply Matrix.ext; unfold raw33029step1 raw33029step0; decide +kernel
      have hl : raw33029step0Labels = labelEmbedding6 ∘ raw33029step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33029step0 raw33029step0Labels raw33029step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4904 node4904Labels := by rfl

def raw33030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33030step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33030step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33030 raw33030Labels = mixedMoment B node5037 node5037Labels := by
  calc
    mixedMoment B raw33030 raw33030Labels = mixedMoment B raw33030step0 raw33030step0Labels := by
      have ha : raw33030step0 = (fun i j => raw33030 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33030step0 raw33030; decide +kernel
      have hl : raw33030step0Labels = raw33030Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33030 raw33030Labels permutation152 permutation3
    mixedMoment B raw33030step0 raw33030step0Labels = mixedMoment B raw33030step1 raw33030step1Labels := by
      have ha : raw33030step1 = raw33030step0 := by apply Matrix.ext; unfold raw33030step1 raw33030step0; decide +kernel
      have hl : raw33030step0Labels = labelEmbedding6 ∘ raw33030step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33030step0 raw33030step0Labels raw33030step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5037 node5037Labels := by rfl

def raw33031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw33031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw33031step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33031step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33031step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33031 raw33031Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw33031 raw33031Labels = mixedMoment B raw33031step0 raw33031step0Labels := by
      have hz : ∀ j, raw33031 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33031step0 = (fun i j => raw33031 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33031step0 raw33031; decide +kernel
      have hl : raw33031step0Labels = raw33031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33031 raw33031Labels permutation520 hz
    mixedMoment B raw33031step0 raw33031step0Labels = mixedMoment B raw33031step1 raw33031step1Labels := by
      have ha : raw33031step1 = (fun i j => raw33031step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33031step1 raw33031step0; decide +kernel
      have hl : raw33031step1Labels = raw33031step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33031step0 raw33031step0Labels permutation32 permutation3
    mixedMoment B raw33031step1 raw33031step1Labels = mixedMoment B raw33031step2 raw33031step2Labels := by
      have ha : raw33031step2 = raw33031step1 := by apply Matrix.ext; unfold raw33031step2 raw33031step1; decide +kernel
      have hl : raw33031step1Labels = labelEmbedding6 ∘ raw33031step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33031step1 raw33031step1Labels raw33031step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw33032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33032Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33032 raw33032Labels = mixedMoment B node3979 node3979Labels := by
  calc
    mixedMoment B raw33032 raw33032Labels = mixedMoment B raw33032step0 raw33032step0Labels := by
      have ha : raw33032step0 = (fun i j => raw33032 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33032step0 raw33032; decide +kernel
      have hl : raw33032step0Labels = raw33032Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33032 raw33032Labels permutation156 permutation3
    _ = mixedMoment B node3979 node3979Labels := by rfl

def raw33033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33033Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33033step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33033step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33033 raw33033Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw33033 raw33033Labels = mixedMoment B raw33033step0 raw33033step0Labels := by
      have hz : ∀ j, raw33033 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33033step0 = (fun i j => raw33033 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33033step0 raw33033; decide +kernel
      have hl : raw33033step0Labels = raw33033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33033 raw33033Labels permutation265 hz
    mixedMoment B raw33033step0 raw33033step0Labels = mixedMoment B raw33033step1 raw33033step1Labels := by
      have ha : raw33033step1 = (fun i j => raw33033step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33033step1 raw33033step0; decide +kernel
      have hl : raw33033step1Labels = raw33033step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33033step0 raw33033step0Labels permutation32 permutation3
    _ = mixedMoment B node1044 node1044Labels := by rfl

def raw33034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33034Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33034step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33034 raw33034Labels = mixedMoment B node2599 node2599Labels := by
  calc
    mixedMoment B raw33034 raw33034Labels = mixedMoment B raw33034step0 raw33034step0Labels := by
      have hz : ∀ j, raw33034 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33034step0 = (fun i j => raw33034 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33034step0 raw33034; decide +kernel
      have hl : raw33034step0Labels = raw33034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33034 raw33034Labels permutation265 hz
    mixedMoment B raw33034step0 raw33034step0Labels = mixedMoment B raw33034step1 raw33034step1Labels := by
      have ha : raw33034step1 = (fun i j => raw33034step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33034step1 raw33034step0; decide +kernel
      have hl : raw33034step1Labels = raw33034step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33034step0 raw33034step0Labels permutation32 permutation3
    _ = mixedMoment B node2599 node2599Labels := by rfl

def raw33035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33035Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33035step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33035step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33035step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33035step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33035 raw33035Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw33035 raw33035Labels = mixedMoment B raw33035step0 raw33035step0Labels := by
      have hz : ∀ j, raw33035 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33035step0 = (fun i j => raw33035 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33035step0 raw33035; decide +kernel
      have hl : raw33035step0Labels = raw33035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33035 raw33035Labels permutation520 hz
    mixedMoment B raw33035step0 raw33035step0Labels = mixedMoment B raw33035step1 raw33035step1Labels := by
      have hz : ∀ j, raw33035step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw33035step1 = (fun i j => raw33035step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw33035step1 raw33035step0; decide +kernel
      have hl : raw33035step1Labels = raw33035step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33035step0 raw33035step0Labels permutation56 hz
    mixedMoment B raw33035step1 raw33035step1Labels = mixedMoment B raw33035step2 raw33035step2Labels := by
      have ha : raw33035step2 = (fun i j => raw33035step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33035step2 raw33035step1; decide +kernel
      have hl : raw33035step2Labels = raw33035step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33035step1 raw33035step1Labels permutation8 permutation3
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw33036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33036Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33036 raw33036Labels = mixedMoment B node885 node885Labels := by
  calc
    mixedMoment B raw33036 raw33036Labels = mixedMoment B raw33036step0 raw33036step0Labels := by
      have ha : raw33036step0 = (fun i j => raw33036 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33036step0 raw33036; decide +kernel
      have hl : raw33036step0Labels = raw33036Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33036 raw33036Labels permutation160 permutation3
    _ = mixedMoment B node885 node885Labels := by rfl

def raw33037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33037Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33037 raw33037Labels = mixedMoment B node2308 node2308Labels := by
  calc
    mixedMoment B raw33037 raw33037Labels = mixedMoment B raw33037step0 raw33037step0Labels := by
      have ha : raw33037step0 = (fun i j => raw33037 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33037step0 raw33037; decide +kernel
      have hl : raw33037step0Labels = raw33037Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33037 raw33037Labels permutation160 permutation3
    _ = mixedMoment B node2308 node2308Labels := by rfl

def raw33038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33038Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33038step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33038step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33038 raw33038Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw33038 raw33038Labels = mixedMoment B raw33038step0 raw33038step0Labels := by
      have hz : ∀ j, raw33038 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33038step0 = (fun i j => raw33038 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33038step0 raw33038; decide +kernel
      have hl : raw33038step0Labels = raw33038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33038 raw33038Labels permutation520 hz
    mixedMoment B raw33038step0 raw33038step0Labels = mixedMoment B raw33038step1 raw33038step1Labels := by
      have ha : raw33038step1 = (fun i j => raw33038step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33038step1 raw33038step0; decide +kernel
      have hl : raw33038step1Labels = raw33038step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33038step0 raw33038step0Labels permutation34 permutation3
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw33039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33039Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33039step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33039 raw33039Labels = mixedMoment B node869 node869Labels := by
  calc
    mixedMoment B raw33039 raw33039Labels = mixedMoment B raw33039step0 raw33039step0Labels := by
      have ha : raw33039step0 = (fun i j => raw33039 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33039step0 raw33039; decide +kernel
      have hl : raw33039step0Labels = raw33039Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33039 raw33039Labels permutation155 permutation3
    _ = mixedMoment B node869 node869Labels := by rfl

def raw33040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33040Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33040 raw33040Labels = mixedMoment B node2298 node2298Labels := by
  calc
    mixedMoment B raw33040 raw33040Labels = mixedMoment B raw33040step0 raw33040step0Labels := by
      have ha : raw33040step0 = (fun i j => raw33040 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33040step0 raw33040; decide +kernel
      have hl : raw33040step0Labels = raw33040Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33040 raw33040Labels permutation155 permutation3
    _ = mixedMoment B node2298 node2298Labels := by rfl

def raw33041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33041Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33041 raw33041Labels = mixedMoment B node2431 node2431Labels := by
  calc
    mixedMoment B raw33041 raw33041Labels = mixedMoment B raw33041step0 raw33041step0Labels := by
      have ha : raw33041step0 = (fun i j => raw33041 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33041step0 raw33041; decide +kernel
      have hl : raw33041step0Labels = raw33041Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33041 raw33041Labels permutation155 permutation3
    _ = mixedMoment B node2431 node2431Labels := by rfl

def raw33042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33042Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw33042step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33042 raw33042Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw33042 raw33042Labels = mixedMoment B raw33042step0 raw33042step0Labels := by
      have hz : ∀ j, raw33042 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33042step0 = (fun i j => raw33042 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33042step0 raw33042; decide +kernel
      have hl : raw33042step0Labels = raw33042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33042 raw33042Labels permutation520 hz
    mixedMoment B raw33042step0 raw33042step0Labels = mixedMoment B raw33042step1 raw33042step1Labels := by
      have ha : raw33042step1 = (fun i j => raw33042step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33042step1 raw33042step0; decide +kernel
      have hl : raw33042step1Labels = raw33042step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33042step0 raw33042step0Labels permutation33 permutation3
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw33043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33043Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw33043step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33043step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33043 raw33043Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw33043 raw33043Labels = mixedMoment B raw33043step0 raw33043step0Labels := by
      have hz : ∀ j, raw33043 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33043step0 = (fun i j => raw33043 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33043step0 raw33043; decide +kernel
      have hl : raw33043step0Labels = raw33043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33043 raw33043Labels permutation434 hz
    mixedMoment B raw33043step0 raw33043step0Labels = mixedMoment B raw33043step1 raw33043step1Labels := by
      have ha : raw33043step1 = (fun i j => raw33043step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33043step1 raw33043step0; decide +kernel
      have hl : raw33043step1Labels = raw33043step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33043step0 raw33043step0Labels permutation33 permutation3
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw33044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33044Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33044 raw33044Labels = mixedMoment B node868 node868Labels := by
  calc
    mixedMoment B raw33044 raw33044Labels = mixedMoment B raw33044step0 raw33044step0Labels := by
      have ha : raw33044step0 = (fun i j => raw33044 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33044step0 raw33044; decide +kernel
      have hl : raw33044step0Labels = raw33044Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33044 raw33044Labels permutation152 permutation3
    _ = mixedMoment B node868 node868Labels := by rfl

def raw33045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33045Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33045 raw33045Labels = mixedMoment B node2297 node2297Labels := by
  calc
    mixedMoment B raw33045 raw33045Labels = mixedMoment B raw33045step0 raw33045step0Labels := by
      have ha : raw33045step0 = (fun i j => raw33045 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33045step0 raw33045; decide +kernel
      have hl : raw33045step0Labels = raw33045Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33045 raw33045Labels permutation152 permutation3
    _ = mixedMoment B node2297 node2297Labels := by rfl

def raw33046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33046Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33046 raw33046Labels = mixedMoment B node2429 node2429Labels := by
  calc
    mixedMoment B raw33046 raw33046Labels = mixedMoment B raw33046step0 raw33046step0Labels := by
      have ha : raw33046step0 = (fun i j => raw33046 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33046step0 raw33046; decide +kernel
      have hl : raw33046step0Labels = raw33046Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33046 raw33046Labels permutation152 permutation3
    _ = mixedMoment B node2429 node2429Labels := by rfl

def raw33047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw33047Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw33047step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33047step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33047 raw33047Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw33047 raw33047Labels = mixedMoment B raw33047step0 raw33047step0Labels := by
      have hz : ∀ j, raw33047 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33047step0 = (fun i j => raw33047 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33047step0 raw33047; decide +kernel
      have hl : raw33047step0Labels = raw33047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33047 raw33047Labels permutation520 hz
    mixedMoment B raw33047step0 raw33047step0Labels = mixedMoment B raw33047step1 raw33047step1Labels := by
      have ha : raw33047step1 = (fun i j => raw33047step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33047step1 raw33047step0; decide +kernel
      have hl : raw33047step1Labels = raw33047step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33047step0 raw33047step0Labels permutation32 permutation3
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw33048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33048step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33048 raw33048Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw33048 raw33048Labels = mixedMoment B raw33048step0 raw33048step0Labels := by
      have ha : raw33048step0 = (fun i j => raw33048 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33048step0 raw33048; decide +kernel
      have hl : raw33048step0Labels = raw33048Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33048 raw33048Labels permutation154 permutation2
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw33049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33049 raw33049Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw33049 raw33049Labels = mixedMoment B raw33049step0 raw33049step0Labels := by
      have ha : raw33049step0 = (fun i j => raw33049 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33049step0 raw33049; decide +kernel
      have hl : raw33049step0Labels = raw33049Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33049 raw33049Labels permutation154 permutation2
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw33050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33050step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33050 raw33050Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw33050 raw33050Labels = mixedMoment B raw33050step0 raw33050step0Labels := by
      have hz : ∀ j, raw33050 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33050step0 = (fun i j => raw33050 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33050step0 raw33050; decide +kernel
      have hl : raw33050step0Labels = raw33050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33050 raw33050Labels permutation520 hz
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw33051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33051step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33051 raw33051Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw33051 raw33051Labels = mixedMoment B raw33051step0 raw33051step0Labels := by
      have ha : raw33051step0 = (fun i j => raw33051 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33051step0 raw33051; decide +kernel
      have hl : raw33051step0Labels = raw33051Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33051 raw33051Labels permutation154 permutation2
    _ = mixedMoment B node5408 node5408Labels := by rfl

def raw33052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33052 raw33052Labels = mixedMoment B node5250 node5250Labels := by
  calc
    _ = mixedMoment B node5250 node5250Labels := by rfl

def raw33053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33053 raw33053Labels = mixedMoment B node4544 node4544Labels := by
  calc
    mixedMoment B raw33053 raw33053Labels = mixedMoment B raw33053step0 raw33053step0Labels := by
      have ha : raw33053step0 = (fun i j => raw33053 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33053step0 raw33053; decide +kernel
      have hl : raw33053step0Labels = raw33053Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33053 raw33053Labels permutation164 permutation2
    _ = mixedMoment B node4544 node4544Labels := by rfl

def raw33054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33054 raw33054Labels = mixedMoment B node4941 node4941Labels := by
  calc
    mixedMoment B raw33054 raw33054Labels = mixedMoment B raw33054step0 raw33054step0Labels := by
      have ha : raw33054step0 = (fun i j => raw33054 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33054step0 raw33054; decide +kernel
      have hl : raw33054step0Labels = raw33054Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33054 raw33054Labels permutation164 permutation2
    _ = mixedMoment B node4941 node4941Labels := by rfl

def raw33055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33055step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33055 raw33055Labels = mixedMoment B node5104 node5104Labels := by
  calc
    mixedMoment B raw33055 raw33055Labels = mixedMoment B raw33055step0 raw33055step0Labels := by
      have hz : ∀ j, raw33055 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33055step0 = (fun i j => raw33055 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33055step0 raw33055; decide +kernel
      have hl : raw33055step0Labels = raw33055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33055 raw33055Labels permutation520 hz
    _ = mixedMoment B node5104 node5104Labels := by rfl

def raw33056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33056step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33056 raw33056Labels = mixedMoment B node5100 node5100Labels := by
  calc
    mixedMoment B raw33056 raw33056Labels = mixedMoment B raw33056step0 raw33056step0Labels := by
      have ha : raw33056step0 = (fun i j => raw33056 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33056step0 raw33056; decide +kernel
      have hl : raw33056step0Labels = raw33056Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33056 raw33056Labels permutation164 permutation2
    _ = mixedMoment B node5100 node5100Labels := by rfl

def raw33057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33057Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33057step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33057 raw33057Labels = mixedMoment B node4530 node4530Labels := by
  calc
    mixedMoment B raw33057 raw33057Labels = mixedMoment B raw33057step0 raw33057step0Labels := by
      have ha : raw33057step0 = (fun i j => raw33057 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33057step0 raw33057; decide +kernel
      have hl : raw33057step0Labels = raw33057Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33057 raw33057Labels permutation154 permutation2
    _ = mixedMoment B node4530 node4530Labels := by rfl

def raw33058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33058step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33058 raw33058Labels = mixedMoment B node4932 node4932Labels := by
  calc
    mixedMoment B raw33058 raw33058Labels = mixedMoment B raw33058step0 raw33058step0Labels := by
      have ha : raw33058step0 = (fun i j => raw33058 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33058step0 raw33058; decide +kernel
      have hl : raw33058step0Labels = raw33058Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33058 raw33058Labels permutation154 permutation2
    _ = mixedMoment B node4932 node4932Labels := by rfl

def raw33059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33059Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33059step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33059 raw33059Labels = mixedMoment B node5043 node5043Labels := by
  calc
    mixedMoment B raw33059 raw33059Labels = mixedMoment B raw33059step0 raw33059step0Labels := by
      have ha : raw33059step0 = (fun i j => raw33059 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33059step0 raw33059; decide +kernel
      have hl : raw33059step0Labels = raw33059Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33059 raw33059Labels permutation154 permutation2
    _ = mixedMoment B node5043 node5043Labels := by rfl

def raw33060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33060Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33060step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33060 raw33060Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw33060 raw33060Labels = mixedMoment B raw33060step0 raw33060step0Labels := by
      have hz : ∀ j, raw33060 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33060step0 = (fun i j => raw33060 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33060step0 raw33060; decide +kernel
      have hl : raw33060step0Labels = raw33060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33060 raw33060Labels permutation520 hz
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw33061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33061 raw33061Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw33061 raw33061Labels = mixedMoment B raw33061step0 raw33061step0Labels := by
      have ha : raw33061step0 = (fun i j => raw33061 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33061step0 raw33061; decide +kernel
      have hl : raw33061step0Labels = raw33061Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33061 raw33061Labels permutation155 permutation2
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw33062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33062 raw33062Labels = mixedMoment B node4533 node4533Labels := by
  calc
    _ = mixedMoment B node4533 node4533Labels := by rfl

def raw33063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33063 raw33063Labels = mixedMoment B node4933 node4933Labels := by
  calc
    _ = mixedMoment B node4933 node4933Labels := by rfl

def raw33064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33064 raw33064Labels = mixedMoment B node5044 node5044Labels := by
  calc
    _ = mixedMoment B node5044 node5044Labels := by rfl

def raw33065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33065 raw33065Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw33065 raw33065Labels = mixedMoment B raw33065step0 raw33065step0Labels := by
      have ha : raw33065step0 = (fun i j => raw33065 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33065step0 raw33065; decide +kernel
      have hl : raw33065step0Labels = raw33065Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33065 raw33065Labels permutation153 permutation2
    _ = mixedMoment B node5076 node5076Labels := by rfl

def raw33066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33066 raw33066Labels = mixedMoment B node4528 node4528Labels := by
  calc
    mixedMoment B raw33066 raw33066Labels = mixedMoment B raw33066step0 raw33066step0Labels := by
      have ha : raw33066step0 = (fun i j => raw33066 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33066step0 raw33066; decide +kernel
      have hl : raw33066step0Labels = raw33066Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33066 raw33066Labels permutation154 permutation2
    _ = mixedMoment B node4528 node4528Labels := by rfl

def raw33067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33067 raw33067Labels = mixedMoment B node4930 node4930Labels := by
  calc
    mixedMoment B raw33067 raw33067Labels = mixedMoment B raw33067step0 raw33067step0Labels := by
      have ha : raw33067step0 = (fun i j => raw33067 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33067step0 raw33067; decide +kernel
      have hl : raw33067step0Labels = raw33067Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33067 raw33067Labels permutation154 permutation2
    _ = mixedMoment B node4930 node4930Labels := by rfl

def raw33068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw33068step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw33068step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33068step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw33068step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33068 raw33068Labels = mixedMoment B node5034 node5034Labels := by
  calc
    mixedMoment B raw33068 raw33068Labels = mixedMoment B raw33068step0 raw33068step0Labels := by
      have ha : raw33068step0 = (fun i j => raw33068 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33068step0 raw33068; decide +kernel
      have hl : raw33068step0Labels = raw33068Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33068 raw33068Labels permutation686 permutation3
    mixedMoment B raw33068step0 raw33068step0Labels = mixedMoment B raw33068step1 raw33068step1Labels := by
      have ha : raw33068step1 = -raw33068step0 := by apply Matrix.ext; change ∀ i j, raw33068step1 i j = -(raw33068step0 i j); unfold raw33068step1 raw33068step0; decide +kernel
      have hl : raw33068step1Labels = raw33068step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33068step1 raw33068step1Labels = mixedMoment B raw33068step2 raw33068step2Labels := by
      have ha : raw33068step2 = raw33068step1 := by apply Matrix.ext; unfold raw33068step2 raw33068step1; decide +kernel
      have hl : raw33068step1Labels = labelEmbedding6 ∘ raw33068step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33068step1 raw33068step1Labels raw33068step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5034 node5034Labels := by rfl

def raw33069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw33069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33069 raw33069Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw33069 raw33069Labels = mixedMoment B raw33069step0 raw33069step0Labels := by
      have hz : ∀ j, raw33069 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33069step0 = (fun i j => raw33069 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33069step0 raw33069; decide +kernel
      have hl : raw33069step0Labels = raw33069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33069 raw33069Labels permutation520 hz
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw33070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33070Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33070step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33070step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33070step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33070step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33070 raw33070Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw33070 raw33070Labels = mixedMoment B raw33070step0 raw33070step0Labels := by
      have ha : raw33070step0 = (fun i j => raw33070 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33070step0 raw33070; decide +kernel
      have hl : raw33070step0Labels = raw33070Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33070 raw33070Labels permutation164 permutation7
    mixedMoment B raw33070step0 raw33070step0Labels = mixedMoment B raw33070step1 raw33070step1Labels := by
      have ha : raw33070step1 = -raw33070step0 := by apply Matrix.ext; change ∀ i j, raw33070step1 i j = -(raw33070step0 i j); unfold raw33070step1 raw33070step0; decide +kernel
      have hl : raw33070step1Labels = raw33070step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33070step1 raw33070step1Labels = mixedMoment B raw33070step2 raw33070step2Labels := by
      have ha : raw33070step2 = raw33070step1 := by apply Matrix.ext; unfold raw33070step2 raw33070step1; decide +kernel
      have hl : raw33070step1Labels = labelEmbedding1 ∘ raw33070step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33070step1 raw33070step1Labels raw33070step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

def raw33071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33071Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33071step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33071step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33071step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33071step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33071 raw33071Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw33071 raw33071Labels = mixedMoment B raw33071step0 raw33071step0Labels := by
      have ha : raw33071step0 = (fun i j => raw33071 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33071step0 raw33071; decide +kernel
      have hl : raw33071step0Labels = raw33071Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33071 raw33071Labels permutation164 permutation7
    mixedMoment B raw33071step0 raw33071step0Labels = mixedMoment B raw33071step1 raw33071step1Labels := by
      have ha : raw33071step1 = -raw33071step0 := by apply Matrix.ext; change ∀ i j, raw33071step1 i j = -(raw33071step0 i j); unfold raw33071step1 raw33071step0; decide +kernel
      have hl : raw33071step1Labels = raw33071step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33071step1 raw33071step1Labels = mixedMoment B raw33071step2 raw33071step2Labels := by
      have ha : raw33071step2 = raw33071step1 := by apply Matrix.ext; unfold raw33071step2 raw33071step1; decide +kernel
      have hl : raw33071step1Labels = labelEmbedding1 ∘ raw33071step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33071step1 raw33071step1Labels raw33071step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw33072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33072Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33072step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33072step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33072step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33072step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33072step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33072step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33072 raw33072Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw33072 raw33072Labels = mixedMoment B raw33072step0 raw33072step0Labels := by
      have hz : ∀ j, raw33072 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33072step0 = (fun i j => raw33072 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33072step0 raw33072; decide +kernel
      have hl : raw33072step0Labels = raw33072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33072 raw33072Labels permutation520 hz
    mixedMoment B raw33072step0 raw33072step0Labels = mixedMoment B raw33072step1 raw33072step1Labels := by
      have ha : raw33072step1 = (fun i j => raw33072step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33072step1 raw33072step0; decide +kernel
      have hl : raw33072step1Labels = raw33072step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33072step0 raw33072step0Labels permutation32 permutation7
    mixedMoment B raw33072step1 raw33072step1Labels = mixedMoment B raw33072step2 raw33072step2Labels := by
      have ha : raw33072step2 = -raw33072step1 := by apply Matrix.ext; change ∀ i j, raw33072step2 i j = -(raw33072step1 i j); unfold raw33072step2 raw33072step1; decide +kernel
      have hl : raw33072step2Labels = raw33072step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33072step2 raw33072step2Labels = mixedMoment B raw33072step3 raw33072step3Labels := by
      have ha : raw33072step3 = raw33072step2 := by apply Matrix.ext; unfold raw33072step3 raw33072step2; decide +kernel
      have hl : raw33072step2Labels = labelEmbedding1 ∘ raw33072step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33072step2 raw33072step2Labels raw33072step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw33073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33073Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33073step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33073step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33073step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33073 raw33073Labels = mixedMoment B node3806 node3806Labels := by
  calc
    mixedMoment B raw33073 raw33073Labels = mixedMoment B raw33073step0 raw33073step0Labels := by
      have ha : raw33073step0 = (fun i j => raw33073 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33073step0 raw33073; decide +kernel
      have hl : raw33073step0Labels = raw33073Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33073 raw33073Labels permutation164 permutation7
    mixedMoment B raw33073step0 raw33073step0Labels = mixedMoment B raw33073step1 raw33073step1Labels := by
      have ha : raw33073step1 = -raw33073step0 := by apply Matrix.ext; change ∀ i j, raw33073step1 i j = -(raw33073step0 i j); unfold raw33073step1 raw33073step0; decide +kernel
      have hl : raw33073step1Labels = raw33073step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33073step1 raw33073step1Labels = mixedMoment B raw33073step2 raw33073step2Labels := by
      have ha : raw33073step2 = raw33073step1 := by apply Matrix.ext; unfold raw33073step2 raw33073step1; decide +kernel
      have hl : raw33073step1Labels = labelEmbedding1 ∘ raw33073step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33073step1 raw33073step1Labels raw33073step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3806 node3806Labels := by rfl

def raw33074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33074Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw33074step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33074step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33074step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33074 raw33074Labels = mixedMoment B node3531 node3531Labels := by
  calc
    mixedMoment B raw33074 raw33074Labels = mixedMoment B raw33074step0 raw33074step0Labels := by
      have ha : raw33074step0 = (fun i j => raw33074 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33074step0 raw33074; decide +kernel
      have hl : raw33074step0Labels = raw33074Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33074 raw33074Labels permutation164 permutation7
    mixedMoment B raw33074step0 raw33074step0Labels = mixedMoment B raw33074step1 raw33074step1Labels := by
      have ha : raw33074step1 = -raw33074step0 := by apply Matrix.ext; change ∀ i j, raw33074step1 i j = -(raw33074step0 i j); unfold raw33074step1 raw33074step0; decide +kernel
      have hl : raw33074step1Labels = raw33074step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33074step1 raw33074step1Labels = mixedMoment B raw33074step2 raw33074step2Labels := by
      have ha : raw33074step2 = raw33074step1 := by apply Matrix.ext; unfold raw33074step2 raw33074step1; decide +kernel
      have hl : raw33074step1Labels = labelEmbedding1 ∘ raw33074step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33074step1 raw33074step1Labels raw33074step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3531 node3531Labels := by rfl

def raw33075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33075Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33075step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33075step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33075step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33075step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33075 raw33075Labels = mixedMoment B node3263 node3263Labels := by
  calc
    mixedMoment B raw33075 raw33075Labels = mixedMoment B raw33075step0 raw33075step0Labels := by
      have ha : raw33075step0 = (fun i j => raw33075 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33075step0 raw33075; decide +kernel
      have hl : raw33075step0Labels = raw33075Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33075 raw33075Labels permutation164 permutation7
    mixedMoment B raw33075step0 raw33075step0Labels = mixedMoment B raw33075step1 raw33075step1Labels := by
      have ha : raw33075step1 = -raw33075step0 := by apply Matrix.ext; change ∀ i j, raw33075step1 i j = -(raw33075step0 i j); unfold raw33075step1 raw33075step0; decide +kernel
      have hl : raw33075step1Labels = raw33075step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33075step1 raw33075step1Labels = mixedMoment B raw33075step2 raw33075step2Labels := by
      have ha : raw33075step2 = raw33075step1 := by apply Matrix.ext; unfold raw33075step2 raw33075step1; decide +kernel
      have hl : raw33075step1Labels = labelEmbedding1 ∘ raw33075step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33075step1 raw33075step1Labels raw33075step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3263 node3263Labels := by rfl

def raw33076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33076Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33076step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33076step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33076step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33076step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33076 raw33076Labels = mixedMoment B node3410 node3410Labels := by
  calc
    mixedMoment B raw33076 raw33076Labels = mixedMoment B raw33076step0 raw33076step0Labels := by
      have ha : raw33076step0 = (fun i j => raw33076 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33076step0 raw33076; decide +kernel
      have hl : raw33076step0Labels = raw33076Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33076 raw33076Labels permutation164 permutation7
    mixedMoment B raw33076step0 raw33076step0Labels = mixedMoment B raw33076step1 raw33076step1Labels := by
      have ha : raw33076step1 = -raw33076step0 := by apply Matrix.ext; change ∀ i j, raw33076step1 i j = -(raw33076step0 i j); unfold raw33076step1 raw33076step0; decide +kernel
      have hl : raw33076step1Labels = raw33076step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33076step1 raw33076step1Labels = mixedMoment B raw33076step2 raw33076step2Labels := by
      have ha : raw33076step2 = raw33076step1 := by apply Matrix.ext; unfold raw33076step2 raw33076step1; decide +kernel
      have hl : raw33076step1Labels = labelEmbedding1 ∘ raw33076step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33076step1 raw33076step1Labels raw33076step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3410 node3410Labels := by rfl

def raw33077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33077Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33077step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33077step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33077step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33077step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33077step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33077 raw33077Labels = mixedMoment B node3483 node3483Labels := by
  calc
    mixedMoment B raw33077 raw33077Labels = mixedMoment B raw33077step0 raw33077step0Labels := by
      have hz : ∀ j, raw33077 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33077step0 = (fun i j => raw33077 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33077step0 raw33077; decide +kernel
      have hl : raw33077step0Labels = raw33077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33077 raw33077Labels permutation520 hz
    mixedMoment B raw33077step0 raw33077step0Labels = mixedMoment B raw33077step1 raw33077step1Labels := by
      have ha : raw33077step1 = (fun i j => raw33077step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33077step1 raw33077step0; decide +kernel
      have hl : raw33077step1Labels = raw33077step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33077step0 raw33077step0Labels permutation32 permutation7
    mixedMoment B raw33077step1 raw33077step1Labels = mixedMoment B raw33077step2 raw33077step2Labels := by
      have ha : raw33077step2 = -raw33077step1 := by apply Matrix.ext; change ∀ i j, raw33077step2 i j = -(raw33077step1 i j); unfold raw33077step2 raw33077step1; decide +kernel
      have hl : raw33077step2Labels = raw33077step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33077step2 raw33077step2Labels = mixedMoment B raw33077step3 raw33077step3Labels := by
      have ha : raw33077step3 = raw33077step2 := by apply Matrix.ext; unfold raw33077step3 raw33077step2; decide +kernel
      have hl : raw33077step2Labels = labelEmbedding1 ∘ raw33077step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33077step2 raw33077step2Labels raw33077step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3483 node3483Labels := by rfl

def raw33078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33078Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33078step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33078step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33078step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33078 raw33078Labels = mixedMoment B node3469 node3469Labels := by
  calc
    mixedMoment B raw33078 raw33078Labels = mixedMoment B raw33078step0 raw33078step0Labels := by
      have ha : raw33078step0 = (fun i j => raw33078 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33078step0 raw33078; decide +kernel
      have hl : raw33078step0Labels = raw33078Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33078 raw33078Labels permutation164 permutation7
    mixedMoment B raw33078step0 raw33078step0Labels = mixedMoment B raw33078step1 raw33078step1Labels := by
      have ha : raw33078step1 = -raw33078step0 := by apply Matrix.ext; change ∀ i j, raw33078step1 i j = -(raw33078step0 i j); unfold raw33078step1 raw33078step0; decide +kernel
      have hl : raw33078step1Labels = raw33078step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33078step1 raw33078step1Labels = mixedMoment B raw33078step2 raw33078step2Labels := by
      have ha : raw33078step2 = raw33078step1 := by apply Matrix.ext; unfold raw33078step2 raw33078step1; decide +kernel
      have hl : raw33078step1Labels = labelEmbedding1 ∘ raw33078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33078step1 raw33078step1Labels raw33078step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3469 node3469Labels := by rfl

def raw33079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33079Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw33079step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33079step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33079step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33079 raw33079Labels = mixedMoment B node3261 node3261Labels := by
  calc
    mixedMoment B raw33079 raw33079Labels = mixedMoment B raw33079step0 raw33079step0Labels := by
      have ha : raw33079step0 = (fun i j => raw33079 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33079step0 raw33079; decide +kernel
      have hl : raw33079step0Labels = raw33079Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33079 raw33079Labels permutation164 permutation7
    mixedMoment B raw33079step0 raw33079step0Labels = mixedMoment B raw33079step1 raw33079step1Labels := by
      have ha : raw33079step1 = -raw33079step0 := by apply Matrix.ext; change ∀ i j, raw33079step1 i j = -(raw33079step0 i j); unfold raw33079step1 raw33079step0; decide +kernel
      have hl : raw33079step1Labels = raw33079step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33079step1 raw33079step1Labels = mixedMoment B raw33079step2 raw33079step2Labels := by
      have ha : raw33079step2 = raw33079step1 := by apply Matrix.ext; unfold raw33079step2 raw33079step1; decide +kernel
      have hl : raw33079step1Labels = labelEmbedding1 ∘ raw33079step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33079step1 raw33079step1Labels raw33079step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3261 node3261Labels := by rfl

def raw33080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33080Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw33080step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33080step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33080step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33080step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33080 raw33080Labels = mixedMoment B node3409 node3409Labels := by
  calc
    mixedMoment B raw33080 raw33080Labels = mixedMoment B raw33080step0 raw33080step0Labels := by
      have ha : raw33080step0 = (fun i j => raw33080 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33080step0 raw33080; decide +kernel
      have hl : raw33080step0Labels = raw33080Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33080 raw33080Labels permutation164 permutation7
    mixedMoment B raw33080step0 raw33080step0Labels = mixedMoment B raw33080step1 raw33080step1Labels := by
      have ha : raw33080step1 = -raw33080step0 := by apply Matrix.ext; change ∀ i j, raw33080step1 i j = -(raw33080step0 i j); unfold raw33080step1 raw33080step0; decide +kernel
      have hl : raw33080step1Labels = raw33080step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33080step1 raw33080step1Labels = mixedMoment B raw33080step2 raw33080step2Labels := by
      have ha : raw33080step2 = raw33080step1 := by apply Matrix.ext; unfold raw33080step2 raw33080step1; decide +kernel
      have hl : raw33080step1Labels = labelEmbedding1 ∘ raw33080step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33080step1 raw33080step1Labels raw33080step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3409 node3409Labels := by rfl

def raw33081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33081Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw33081step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33081step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw33081step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33081step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw33081step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33081 raw33081Labels = mixedMoment B node3465 node3465Labels := by
  calc
    mixedMoment B raw33081 raw33081Labels = mixedMoment B raw33081step0 raw33081step0Labels := by
      have ha : raw33081step0 = (fun i j => raw33081 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33081step0 raw33081; decide +kernel
      have hl : raw33081step0Labels = raw33081Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33081 raw33081Labels permutation164 permutation7
    mixedMoment B raw33081step0 raw33081step0Labels = mixedMoment B raw33081step1 raw33081step1Labels := by
      have ha : raw33081step1 = -raw33081step0 := by apply Matrix.ext; change ∀ i j, raw33081step1 i j = -(raw33081step0 i j); unfold raw33081step1 raw33081step0; decide +kernel
      have hl : raw33081step1Labels = raw33081step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33081step1 raw33081step1Labels = mixedMoment B raw33081step2 raw33081step2Labels := by
      have ha : raw33081step2 = raw33081step1 := by apply Matrix.ext; unfold raw33081step2 raw33081step1; decide +kernel
      have hl : raw33081step1Labels = labelEmbedding1 ∘ raw33081step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33081step1 raw33081step1Labels raw33081step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3465 node3465Labels := by rfl

def raw33082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33082Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33082step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw33082step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33082step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33082step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw33082step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33082 raw33082Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw33082 raw33082Labels = mixedMoment B raw33082step0 raw33082step0Labels := by
      have hz : ∀ j, raw33082 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33082step0 = (fun i j => raw33082 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33082step0 raw33082; decide +kernel
      have hl : raw33082step0Labels = raw33082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33082 raw33082Labels permutation520 hz
    mixedMoment B raw33082step0 raw33082step0Labels = mixedMoment B raw33082step1 raw33082step1Labels := by
      have ha : raw33082step1 = (fun i j => raw33082step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33082step1 raw33082step0; decide +kernel
      have hl : raw33082step1Labels = raw33082step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33082step0 raw33082step0Labels permutation32 permutation7
    mixedMoment B raw33082step1 raw33082step1Labels = mixedMoment B raw33082step2 raw33082step2Labels := by
      have ha : raw33082step2 = -raw33082step1 := by apply Matrix.ext; change ∀ i j, raw33082step2 i j = -(raw33082step1 i j); unfold raw33082step2 raw33082step1; decide +kernel
      have hl : raw33082step2Labels = raw33082step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33082step2 raw33082step2Labels = mixedMoment B raw33082step3 raw33082step3Labels := by
      have ha : raw33082step3 = raw33082step2 := by apply Matrix.ext; unfold raw33082step3 raw33082step2; decide +kernel
      have hl : raw33082step2Labels = labelEmbedding1 ∘ raw33082step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33082step2 raw33082step2Labels raw33082step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3482 node3482Labels := by rfl

def raw33083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33083Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33083step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33083step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33083step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33083step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33083step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33083 raw33083Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw33083 raw33083Labels = mixedMoment B raw33083step0 raw33083step0Labels := by
      have ha : raw33083step0 = (fun i j => raw33083 (permutation165 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33083step0 raw33083; decide +kernel
      have hl : raw33083step0Labels = raw33083Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33083 raw33083Labels permutation165 permutation7
    mixedMoment B raw33083step0 raw33083step0Labels = mixedMoment B raw33083step1 raw33083step1Labels := by
      have ha : raw33083step1 = -raw33083step0 := by apply Matrix.ext; change ∀ i j, raw33083step1 i j = -(raw33083step0 i j); unfold raw33083step1 raw33083step0; decide +kernel
      have hl : raw33083step1Labels = raw33083step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33083step1 raw33083step1Labels = mixedMoment B raw33083step2 raw33083step2Labels := by
      have ha : raw33083step2 = raw33083step1 := by apply Matrix.ext; unfold raw33083step2 raw33083step1; decide +kernel
      have hl : raw33083step1Labels = labelEmbedding1 ∘ raw33083step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33083step1 raw33083step1Labels raw33083step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

def raw33084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33084Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33084step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33084step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33084step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33084 raw33084Labels = mixedMoment B node3267 node3267Labels := by
  calc
    mixedMoment B raw33084 raw33084Labels = mixedMoment B raw33084step0 raw33084step0Labels := by
      have ha : raw33084step0 = (fun i j => raw33084 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33084step0 raw33084; decide +kernel
      have hl : raw33084step0Labels = raw33084Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33084 raw33084Labels permutation164 permutation7
    mixedMoment B raw33084step0 raw33084step0Labels = mixedMoment B raw33084step1 raw33084step1Labels := by
      have ha : raw33084step1 = -raw33084step0 := by apply Matrix.ext; change ∀ i j, raw33084step1 i j = -(raw33084step0 i j); unfold raw33084step1 raw33084step0; decide +kernel
      have hl : raw33084step1Labels = raw33084step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33084step1 raw33084step1Labels = mixedMoment B raw33084step2 raw33084step2Labels := by
      have ha : raw33084step2 = raw33084step1 := by apply Matrix.ext; unfold raw33084step2 raw33084step1; decide +kernel
      have hl : raw33084step1Labels = labelEmbedding1 ∘ raw33084step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33084step1 raw33084step1Labels raw33084step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3267 node3267Labels := by rfl

def raw33085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33085Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33085step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33085step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33085step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33085 raw33085Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw33085 raw33085Labels = mixedMoment B raw33085step0 raw33085step0Labels := by
      have ha : raw33085step0 = (fun i j => raw33085 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33085step0 raw33085; decide +kernel
      have hl : raw33085step0Labels = raw33085Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33085 raw33085Labels permutation164 permutation7
    mixedMoment B raw33085step0 raw33085step0Labels = mixedMoment B raw33085step1 raw33085step1Labels := by
      have ha : raw33085step1 = -raw33085step0 := by apply Matrix.ext; change ∀ i j, raw33085step1 i j = -(raw33085step0 i j); unfold raw33085step1 raw33085step0; decide +kernel
      have hl : raw33085step1Labels = raw33085step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33085step1 raw33085step1Labels = mixedMoment B raw33085step2 raw33085step2Labels := by
      have ha : raw33085step2 = raw33085step1 := by apply Matrix.ext; unfold raw33085step2 raw33085step1; decide +kernel
      have hl : raw33085step1Labels = labelEmbedding1 ∘ raw33085step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33085step1 raw33085step1Labels raw33085step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

def raw33086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33086Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33086step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33086step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33086step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33086step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33086 raw33086Labels = mixedMoment B node3474 node3474Labels := by
  calc
    mixedMoment B raw33086 raw33086Labels = mixedMoment B raw33086step0 raw33086step0Labels := by
      have ha : raw33086step0 = (fun i j => raw33086 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33086step0 raw33086; decide +kernel
      have hl : raw33086step0Labels = raw33086Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33086 raw33086Labels permutation164 permutation7
    mixedMoment B raw33086step0 raw33086step0Labels = mixedMoment B raw33086step1 raw33086step1Labels := by
      have ha : raw33086step1 = -raw33086step0 := by apply Matrix.ext; change ∀ i j, raw33086step1 i j = -(raw33086step0 i j); unfold raw33086step1 raw33086step0; decide +kernel
      have hl : raw33086step1Labels = raw33086step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33086step1 raw33086step1Labels = mixedMoment B raw33086step2 raw33086step2Labels := by
      have ha : raw33086step2 = raw33086step1 := by apply Matrix.ext; unfold raw33086step2 raw33086step1; decide +kernel
      have hl : raw33086step1Labels = labelEmbedding1 ∘ raw33086step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33086step1 raw33086step1Labels raw33086step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3474 node3474Labels := by rfl

def raw33087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33087Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33087step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33087step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33087step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33087step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33087 raw33087Labels = mixedMoment B node3477 node3477Labels := by
  calc
    mixedMoment B raw33087 raw33087Labels = mixedMoment B raw33087step0 raw33087step0Labels := by
      have ha : raw33087step0 = (fun i j => raw33087 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33087step0 raw33087; decide +kernel
      have hl : raw33087step0Labels = raw33087Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33087 raw33087Labels permutation164 permutation7
    mixedMoment B raw33087step0 raw33087step0Labels = mixedMoment B raw33087step1 raw33087step1Labels := by
      have ha : raw33087step1 = -raw33087step0 := by apply Matrix.ext; change ∀ i j, raw33087step1 i j = -(raw33087step0 i j); unfold raw33087step1 raw33087step0; decide +kernel
      have hl : raw33087step1Labels = raw33087step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33087step1 raw33087step1Labels = mixedMoment B raw33087step2 raw33087step2Labels := by
      have ha : raw33087step2 = raw33087step1 := by apply Matrix.ext; unfold raw33087step2 raw33087step1; decide +kernel
      have hl : raw33087step1Labels = labelEmbedding1 ∘ raw33087step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33087step1 raw33087step1Labels raw33087step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3477 node3477Labels := by rfl

def raw33088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33088Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw33088step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33088step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33088step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33088step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33088 raw33088Labels = mixedMoment B node3260 node3260Labels := by
  calc
    mixedMoment B raw33088 raw33088Labels = mixedMoment B raw33088step0 raw33088step0Labels := by
      have ha : raw33088step0 = (fun i j => raw33088 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33088step0 raw33088; decide +kernel
      have hl : raw33088step0Labels = raw33088Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33088 raw33088Labels permutation164 permutation7
    mixedMoment B raw33088step0 raw33088step0Labels = mixedMoment B raw33088step1 raw33088step1Labels := by
      have ha : raw33088step1 = -raw33088step0 := by apply Matrix.ext; change ∀ i j, raw33088step1 i j = -(raw33088step0 i j); unfold raw33088step1 raw33088step0; decide +kernel
      have hl : raw33088step1Labels = raw33088step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33088step1 raw33088step1Labels = mixedMoment B raw33088step2 raw33088step2Labels := by
      have ha : raw33088step2 = raw33088step1 := by apply Matrix.ext; unfold raw33088step2 raw33088step1; decide +kernel
      have hl : raw33088step1Labels = labelEmbedding1 ∘ raw33088step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33088step1 raw33088step1Labels raw33088step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3260 node3260Labels := by rfl

def raw33089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33089Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw33089step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33089step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33089step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33089step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33089 raw33089Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw33089 raw33089Labels = mixedMoment B raw33089step0 raw33089step0Labels := by
      have ha : raw33089step0 = (fun i j => raw33089 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33089step0 raw33089; decide +kernel
      have hl : raw33089step0Labels = raw33089Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33089 raw33089Labels permutation164 permutation7
    mixedMoment B raw33089step0 raw33089step0Labels = mixedMoment B raw33089step1 raw33089step1Labels := by
      have ha : raw33089step1 = -raw33089step0 := by apply Matrix.ext; change ∀ i j, raw33089step1 i j = -(raw33089step0 i j); unfold raw33089step1 raw33089step0; decide +kernel
      have hl : raw33089step1Labels = raw33089step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33089step1 raw33089step1Labels = mixedMoment B raw33089step2 raw33089step2Labels := by
      have ha : raw33089step2 = raw33089step1 := by apply Matrix.ext; unfold raw33089step2 raw33089step1; decide +kernel
      have hl : raw33089step1Labels = labelEmbedding1 ∘ raw33089step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33089step1 raw33089step1Labels raw33089step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

def raw33090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33090Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw33090step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw33090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33090 raw33090Labels = mixedMoment B node3451 node3451Labels := by
  calc
    mixedMoment B raw33090 raw33090Labels = mixedMoment B raw33090step0 raw33090step0Labels := by
      have ha : raw33090step0 = (fun i j => raw33090 (permutation685 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33090step0 raw33090; decide +kernel
      have hl : raw33090step0Labels = raw33090Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33090 raw33090Labels permutation685 permutation5
    mixedMoment B raw33090step0 raw33090step0Labels = mixedMoment B raw33090step1 raw33090step1Labels := by
      have ha : raw33090step1 = raw33090step0 := by apply Matrix.ext; unfold raw33090step1 raw33090step0; decide +kernel
      have hl : raw33090step0Labels = labelEmbedding1 ∘ raw33090step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33090step0 raw33090step0Labels raw33090step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3451 node3451Labels := by rfl

def raw33091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw33091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33091step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw33091step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33091step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33091step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33091step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw33091step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33091 raw33091Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw33091 raw33091Labels = mixedMoment B raw33091step0 raw33091step0Labels := by
      have hz : ∀ j, raw33091 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33091step0 = (fun i j => raw33091 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33091step0 raw33091; decide +kernel
      have hl : raw33091step0Labels = raw33091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33091 raw33091Labels permutation520 hz
    mixedMoment B raw33091step0 raw33091step0Labels = mixedMoment B raw33091step1 raw33091step1Labels := by
      have ha : raw33091step1 = (fun i j => raw33091step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33091step1 raw33091step0; decide +kernel
      have hl : raw33091step1Labels = raw33091step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33091step0 raw33091step0Labels permutation32 permutation7
    mixedMoment B raw33091step1 raw33091step1Labels = mixedMoment B raw33091step2 raw33091step2Labels := by
      have ha : raw33091step2 = -raw33091step1 := by apply Matrix.ext; change ∀ i j, raw33091step2 i j = -(raw33091step1 i j); unfold raw33091step2 raw33091step1; decide +kernel
      have hl : raw33091step2Labels = raw33091step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33091step2 raw33091step2Labels = mixedMoment B raw33091step3 raw33091step3Labels := by
      have ha : raw33091step3 = raw33091step2 := by apply Matrix.ext; unfold raw33091step3 raw33091step2; decide +kernel
      have hl : raw33091step2Labels = labelEmbedding1 ∘ raw33091step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33091step2 raw33091step2Labels raw33091step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

def raw33092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33092step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33092step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33092 raw33092Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw33092 raw33092Labels = mixedMoment B raw33092step0 raw33092step0Labels := by
      have ha : raw33092step0 = (fun i j => raw33092 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33092step0 raw33092; decide +kernel
      have hl : raw33092step0Labels = raw33092Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33092 raw33092Labels permutation267 permutation3
    mixedMoment B raw33092step0 raw33092step0Labels = mixedMoment B raw33092step1 raw33092step1Labels := by
      have ha : raw33092step1 = raw33092step0 := by apply Matrix.ext; unfold raw33092step1 raw33092step0; decide +kernel
      have hl : raw33092step0Labels = labelEmbedding6 ∘ raw33092step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33092step0 raw33092step0Labels raw33092step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw33093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33093 raw33093Labels = mixedMoment B node5476 node5476Labels := by
  calc
    mixedMoment B raw33093 raw33093Labels = mixedMoment B raw33093step0 raw33093step0Labels := by
      have ha : raw33093step0 = (fun i j => raw33093 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33093step0 raw33093; decide +kernel
      have hl : raw33093step0Labels = raw33093Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33093 raw33093Labels permutation176 permutation2
    _ = mixedMoment B node5476 node5476Labels := by rfl

def raw33094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33094step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33094step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33094 raw33094Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw33094 raw33094Labels = mixedMoment B raw33094step0 raw33094step0Labels := by
      have ha : raw33094step0 = (fun i j => raw33094 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33094step0 raw33094; decide +kernel
      have hl : raw33094step0Labels = raw33094Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33094 raw33094Labels permutation164 permutation3
    mixedMoment B raw33094step0 raw33094step0Labels = mixedMoment B raw33094step1 raw33094step1Labels := by
      have ha : raw33094step1 = raw33094step0 := by apply Matrix.ext; unfold raw33094step1 raw33094step0; decide +kernel
      have hl : raw33094step0Labels = labelEmbedding6 ∘ raw33094step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33094step0 raw33094step0Labels raw33094step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

def raw33095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33095step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33095 raw33095Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw33095 raw33095Labels = mixedMoment B raw33095step0 raw33095step0Labels := by
      have ha : raw33095step0 = (fun i j => raw33095 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33095step0 raw33095; decide +kernel
      have hl : raw33095step0Labels = raw33095Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33095 raw33095Labels permutation155 permutation3
    mixedMoment B raw33095step0 raw33095step0Labels = mixedMoment B raw33095step1 raw33095step1Labels := by
      have ha : raw33095step1 = raw33095step0 := by apply Matrix.ext; unfold raw33095step1 raw33095step0; decide +kernel
      have hl : raw33095step0Labels = labelEmbedding6 ∘ raw33095step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33095step0 raw33095step0Labels raw33095step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw33096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33096step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33096step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33096step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33096step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33096 raw33096Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw33096 raw33096Labels = mixedMoment B raw33096step0 raw33096step0Labels := by
      have hz : ∀ j, raw33096 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33096step0 = (fun i j => raw33096 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33096step0 raw33096; decide +kernel
      have hl : raw33096step0Labels = raw33096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33096 raw33096Labels permutation265 hz
    mixedMoment B raw33096step0 raw33096step0Labels = mixedMoment B raw33096step1 raw33096step1Labels := by
      have ha : raw33096step1 = (fun i j => raw33096step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33096step1 raw33096step0; decide +kernel
      have hl : raw33096step1Labels = raw33096step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33096step0 raw33096step0Labels permutation34 permutation3
    mixedMoment B raw33096step1 raw33096step1Labels = mixedMoment B raw33096step2 raw33096step2Labels := by
      have ha : raw33096step2 = raw33096step1 := by apply Matrix.ext; unfold raw33096step2 raw33096step1; decide +kernel
      have hl : raw33096step1Labels = labelEmbedding6 ∘ raw33096step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33096step1 raw33096step1Labels raw33096step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw33097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33097step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33097step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33097step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33097step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33097 raw33097Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw33097 raw33097Labels = mixedMoment B raw33097step0 raw33097step0Labels := by
      have hz : ∀ j, raw33097 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33097step0 = (fun i j => raw33097 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33097step0 raw33097; decide +kernel
      have hl : raw33097step0Labels = raw33097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33097 raw33097Labels permutation265 hz
    mixedMoment B raw33097step0 raw33097step0Labels = mixedMoment B raw33097step1 raw33097step1Labels := by
      have ha : raw33097step1 = (fun i j => raw33097step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33097step1 raw33097step0; decide +kernel
      have hl : raw33097step1Labels = raw33097step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33097step0 raw33097step0Labels permutation44 permutation3
    mixedMoment B raw33097step1 raw33097step1Labels = mixedMoment B raw33097step2 raw33097step2Labels := by
      have ha : raw33097step2 = raw33097step1 := by apply Matrix.ext; unfold raw33097step2 raw33097step1; decide +kernel
      have hl : raw33097step1Labels = labelEmbedding6 ∘ raw33097step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33097step1 raw33097step1Labels raw33097step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw33098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33098step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33098step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33098 raw33098Labels = mixedMoment B node4912 node4912Labels := by
  calc
    mixedMoment B raw33098 raw33098Labels = mixedMoment B raw33098step0 raw33098step0Labels := by
      have ha : raw33098step0 = (fun i j => raw33098 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33098step0 raw33098; decide +kernel
      have hl : raw33098step0Labels = raw33098Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33098 raw33098Labels permutation166 permutation3
    mixedMoment B raw33098step0 raw33098step0Labels = mixedMoment B raw33098step1 raw33098step1Labels := by
      have ha : raw33098step1 = raw33098step0 := by apply Matrix.ext; unfold raw33098step1 raw33098step0; decide +kernel
      have hl : raw33098step0Labels = labelEmbedding6 ∘ raw33098step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33098step0 raw33098step0Labels raw33098step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4912 node4912Labels := by rfl

def raw33099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33099step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33099step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33099step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33099 raw33099Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw33099 raw33099Labels = mixedMoment B raw33099step0 raw33099step0Labels := by
      have ha : raw33099step0 = (fun i j => raw33099 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33099step0 raw33099; decide +kernel
      have hl : raw33099step0Labels = raw33099Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33099 raw33099Labels permutation166 permutation3
    mixedMoment B raw33099step0 raw33099step0Labels = mixedMoment B raw33099step1 raw33099step1Labels := by
      have ha : raw33099step1 = raw33099step0 := by apply Matrix.ext; unfold raw33099step1 raw33099step0; decide +kernel
      have hl : raw33099step0Labels = labelEmbedding6 ∘ raw33099step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33099step0 raw33099step0Labels raw33099step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5059 node5059Labels := by rfl

def raw33100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33100step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33100 raw33100Labels = mixedMoment B node4288 node4288Labels := by
  calc
    mixedMoment B raw33100 raw33100Labels = mixedMoment B raw33100step0 raw33100step0Labels := by
      have ha : raw33100step0 = (fun i j => raw33100 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33100step0 raw33100; decide +kernel
      have hl : raw33100step0Labels = raw33100Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33100 raw33100Labels permutation155 permutation3
    mixedMoment B raw33100step0 raw33100step0Labels = mixedMoment B raw33100step1 raw33100step1Labels := by
      have ha : raw33100step1 = raw33100step0 := by apply Matrix.ext; unfold raw33100step1 raw33100step0; decide +kernel
      have hl : raw33100step0Labels = labelEmbedding6 ∘ raw33100step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33100step0 raw33100step0Labels raw33100step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4288 node4288Labels := by rfl

def raw33101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33101step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33101step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33101step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33101 raw33101Labels = mixedMoment B node4903 node4903Labels := by
  calc
    mixedMoment B raw33101 raw33101Labels = mixedMoment B raw33101step0 raw33101step0Labels := by
      have ha : raw33101step0 = (fun i j => raw33101 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33101step0 raw33101; decide +kernel
      have hl : raw33101step0Labels = raw33101Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33101 raw33101Labels permutation155 permutation3
    mixedMoment B raw33101step0 raw33101step0Labels = mixedMoment B raw33101step1 raw33101step1Labels := by
      have ha : raw33101step1 = raw33101step0 := by apply Matrix.ext; unfold raw33101step1 raw33101step0; decide +kernel
      have hl : raw33101step0Labels = labelEmbedding6 ∘ raw33101step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33101step0 raw33101step0Labels raw33101step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4903 node4903Labels := by rfl

def raw33102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33102step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33102step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33102 raw33102Labels = mixedMoment B node5036 node5036Labels := by
  calc
    mixedMoment B raw33102 raw33102Labels = mixedMoment B raw33102step0 raw33102step0Labels := by
      have ha : raw33102step0 = (fun i j => raw33102 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33102step0 raw33102; decide +kernel
      have hl : raw33102step0Labels = raw33102Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33102 raw33102Labels permutation155 permutation3
    mixedMoment B raw33102step0 raw33102step0Labels = mixedMoment B raw33102step1 raw33102step1Labels := by
      have ha : raw33102step1 = raw33102step0 := by apply Matrix.ext; unfold raw33102step1 raw33102step0; decide +kernel
      have hl : raw33102step0Labels = labelEmbedding6 ∘ raw33102step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33102step0 raw33102step0Labels raw33102step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5036 node5036Labels := by rfl

def raw33103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33103step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33103step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33103step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33103step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33103 raw33103Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw33103 raw33103Labels = mixedMoment B raw33103step0 raw33103step0Labels := by
      have ha : raw33103step0 = (fun i j => raw33103 (permutation165 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33103step0 raw33103; decide +kernel
      have hl : raw33103step0Labels = raw33103Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33103 raw33103Labels permutation165 permutation3
    mixedMoment B raw33103step0 raw33103step0Labels = mixedMoment B raw33103step1 raw33103step1Labels := by
      have ha : raw33103step1 = raw33103step0 := by apply Matrix.ext; unfold raw33103step1 raw33103step0; decide +kernel
      have hl : raw33103step0Labels = labelEmbedding6 ∘ raw33103step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33103step0 raw33103step0Labels raw33103step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5050 node5050Labels := by rfl

def raw33104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33104step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33104step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33104 raw33104Labels = mixedMoment B node5072 node5072Labels := by
  calc
    mixedMoment B raw33104 raw33104Labels = mixedMoment B raw33104step0 raw33104step0Labels := by
      have ha : raw33104step0 = (fun i j => raw33104 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33104step0 raw33104; decide +kernel
      have hl : raw33104step0Labels = raw33104Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33104 raw33104Labels permutation155 permutation3
    mixedMoment B raw33104step0 raw33104step0Labels = mixedMoment B raw33104step1 raw33104step1Labels := by
      have ha : raw33104step1 = raw33104step0 := by apply Matrix.ext; unfold raw33104step1 raw33104step0; decide +kernel
      have hl : raw33104step0Labels = labelEmbedding6 ∘ raw33104step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33104step0 raw33104step0Labels raw33104step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5072 node5072Labels := by rfl

def raw33105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw33105step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33105step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33105step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33105step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33105 raw33105Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw33105 raw33105Labels = mixedMoment B raw33105step0 raw33105step0Labels := by
      have hz : ∀ j, raw33105 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33105step0 = (fun i j => raw33105 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33105step0 raw33105; decide +kernel
      have hl : raw33105step0Labels = raw33105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33105 raw33105Labels permutation434 hz
    mixedMoment B raw33105step0 raw33105step0Labels = mixedMoment B raw33105step1 raw33105step1Labels := by
      have ha : raw33105step1 = (fun i j => raw33105step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33105step1 raw33105step0; decide +kernel
      have hl : raw33105step1Labels = raw33105step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33105step0 raw33105step0Labels permutation32 permutation3
    mixedMoment B raw33105step1 raw33105step1Labels = mixedMoment B raw33105step2 raw33105step2Labels := by
      have ha : raw33105step2 = raw33105step1 := by apply Matrix.ext; unfold raw33105step2 raw33105step1; decide +kernel
      have hl : raw33105step1Labels = labelEmbedding6 ∘ raw33105step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33105step1 raw33105step1Labels raw33105step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw33106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33106step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33106step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33106step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33106 raw33106Labels = mixedMoment B node4287 node4287Labels := by
  calc
    mixedMoment B raw33106 raw33106Labels = mixedMoment B raw33106step0 raw33106step0Labels := by
      have ha : raw33106step0 = (fun i j => raw33106 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33106step0 raw33106; decide +kernel
      have hl : raw33106step0Labels = raw33106Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33106 raw33106Labels permutation154 permutation3
    mixedMoment B raw33106step0 raw33106step0Labels = mixedMoment B raw33106step1 raw33106step1Labels := by
      have ha : raw33106step1 = raw33106step0 := by apply Matrix.ext; unfold raw33106step1 raw33106step0; decide +kernel
      have hl : raw33106step0Labels = labelEmbedding6 ∘ raw33106step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33106step0 raw33106step0Labels raw33106step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4287 node4287Labels := by rfl

def raw33107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33107step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33107step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33107step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33107 raw33107Labels = mixedMoment B node4902 node4902Labels := by
  calc
    mixedMoment B raw33107 raw33107Labels = mixedMoment B raw33107step0 raw33107step0Labels := by
      have ha : raw33107step0 = (fun i j => raw33107 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33107step0 raw33107; decide +kernel
      have hl : raw33107step0Labels = raw33107Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33107 raw33107Labels permutation154 permutation3
    mixedMoment B raw33107step0 raw33107step0Labels = mixedMoment B raw33107step1 raw33107step1Labels := by
      have ha : raw33107step1 = raw33107step0 := by apply Matrix.ext; unfold raw33107step1 raw33107step0; decide +kernel
      have hl : raw33107step0Labels = labelEmbedding6 ∘ raw33107step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33107step0 raw33107step0Labels raw33107step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4902 node4902Labels := by rfl

def raw33108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33108step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33108step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33108step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33108 raw33108Labels = mixedMoment B node5033 node5033Labels := by
  calc
    mixedMoment B raw33108 raw33108Labels = mixedMoment B raw33108step0 raw33108step0Labels := by
      have ha : raw33108step0 = (fun i j => raw33108 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33108step0 raw33108; decide +kernel
      have hl : raw33108step0Labels = raw33108Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33108 raw33108Labels permutation154 permutation3
    mixedMoment B raw33108step0 raw33108step0Labels = mixedMoment B raw33108step1 raw33108step1Labels := by
      have ha : raw33108step1 = raw33108step0 := by apply Matrix.ext; unfold raw33108step1 raw33108step0; decide +kernel
      have hl : raw33108step0Labels = labelEmbedding6 ∘ raw33108step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33108step0 raw33108step0Labels raw33108step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5033 node5033Labels := by rfl

def raw33109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw33109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33109step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33109step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33109step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33109 raw33109Labels = mixedMoment B node5047 node5047Labels := by
  calc
    mixedMoment B raw33109 raw33109Labels = mixedMoment B raw33109step0 raw33109step0Labels := by
      have ha : raw33109step0 = (fun i j => raw33109 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33109step0 raw33109; decide +kernel
      have hl : raw33109step0Labels = raw33109Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33109 raw33109Labels permutation164 permutation3
    mixedMoment B raw33109step0 raw33109step0Labels = mixedMoment B raw33109step1 raw33109step1Labels := by
      have ha : raw33109step1 = raw33109step0 := by apply Matrix.ext; unfold raw33109step1 raw33109step0; decide +kernel
      have hl : raw33109step0Labels = labelEmbedding6 ∘ raw33109step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33109step0 raw33109step0Labels raw33109step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5047 node5047Labels := by rfl

def raw33110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33110Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33110step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33110 raw33110Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw33110 raw33110Labels = mixedMoment B raw33110step0 raw33110step0Labels := by
      have ha : raw33110step0 = (fun i j => raw33110 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33110step0 raw33110; decide +kernel
      have hl : raw33110step0Labels = raw33110Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33110 raw33110Labels permutation267 permutation3
    _ = mixedMoment B node3690 node3690Labels := by rfl

def raw33111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33111 raw33111Labels = mixedMoment B node3965 node3965Labels := by
  calc
    mixedMoment B raw33111 raw33111Labels = mixedMoment B raw33111step0 raw33111step0Labels := by
      have ha : raw33111step0 = (fun i j => raw33111 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33111step0 raw33111; decide +kernel
      have hl : raw33111step0Labels = raw33111Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33111 raw33111Labels permutation154 permutation3
    _ = mixedMoment B node3965 node3965Labels := by rfl

def raw33112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33112step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33112 raw33112Labels = mixedMoment B node3971 node3971Labels := by
  calc
    mixedMoment B raw33112 raw33112Labels = mixedMoment B raw33112step0 raw33112step0Labels := by
      have ha : raw33112step0 = (fun i j => raw33112 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33112step0 raw33112; decide +kernel
      have hl : raw33112step0Labels = raw33112Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33112 raw33112Labels permutation164 permutation3
    _ = mixedMoment B node3971 node3971Labels := by rfl

def raw33113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33113Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33113 raw33113Labels = mixedMoment B node3980 node3980Labels := by
  calc
    mixedMoment B raw33113 raw33113Labels = mixedMoment B raw33113step0 raw33113step0Labels := by
      have ha : raw33113step0 = (fun i j => raw33113 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33113step0 raw33113; decide +kernel
      have hl : raw33113step0Labels = raw33113Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33113 raw33113Labels permutation155 permutation3
    _ = mixedMoment B node3980 node3980Labels := by rfl

def raw33114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33114step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33114 raw33114Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw33114 raw33114Labels = mixedMoment B raw33114step0 raw33114step0Labels := by
      have hz : ∀ j, raw33114 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33114step0 = (fun i j => raw33114 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33114step0 raw33114; decide +kernel
      have hl : raw33114step0Labels = raw33114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33114 raw33114Labels permutation265 hz
    mixedMoment B raw33114step0 raw33114step0Labels = mixedMoment B raw33114step1 raw33114step1Labels := by
      have ha : raw33114step1 = (fun i j => raw33114step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33114step1 raw33114step0; decide +kernel
      have hl : raw33114step1Labels = raw33114step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33114step0 raw33114step0Labels permutation34 permutation3
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw33115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33115step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33115 raw33115Labels = mixedMoment B node2595 node2595Labels := by
  calc
    mixedMoment B raw33115 raw33115Labels = mixedMoment B raw33115step0 raw33115step0Labels := by
      have hz : ∀ j, raw33115 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33115step0 = (fun i j => raw33115 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33115step0 raw33115; decide +kernel
      have hl : raw33115step0Labels = raw33115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33115 raw33115Labels permutation265 hz
    mixedMoment B raw33115step0 raw33115step0Labels = mixedMoment B raw33115step1 raw33115step1Labels := by
      have ha : raw33115step1 = (fun i j => raw33115step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33115step1 raw33115step0; decide +kernel
      have hl : raw33115step1Labels = raw33115step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33115step0 raw33115step0Labels permutation34 permutation3
    _ = mixedMoment B node2595 node2595Labels := by rfl

def raw33116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33116step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33116 raw33116Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw33116 raw33116Labels = mixedMoment B raw33116step0 raw33116step0Labels := by
      have hz : ∀ j, raw33116 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33116step0 = (fun i j => raw33116 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33116step0 raw33116; decide +kernel
      have hl : raw33116step0Labels = raw33116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33116 raw33116Labels permutation265 hz
    mixedMoment B raw33116step0 raw33116step0Labels = mixedMoment B raw33116step1 raw33116step1Labels := by
      have ha : raw33116step1 = (fun i j => raw33116step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33116step1 raw33116step0; decide +kernel
      have hl : raw33116step1Labels = raw33116step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33116step0 raw33116step0Labels permutation44 permutation3
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw33117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33117step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33117 raw33117Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw33117 raw33117Labels = mixedMoment B raw33117step0 raw33117step0Labels := by
      have hz : ∀ j, raw33117 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw33117step0 = (fun i j => raw33117 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw33117step0 raw33117; decide +kernel
      have hl : raw33117step0Labels = raw33117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33117 raw33117Labels permutation265 hz
    mixedMoment B raw33117step0 raw33117step0Labels = mixedMoment B raw33117step1 raw33117step1Labels := by
      have ha : raw33117step1 = (fun i j => raw33117step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33117step1 raw33117step0; decide +kernel
      have hl : raw33117step1Labels = raw33117step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33117step0 raw33117step0Labels permutation35 permutation3
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw33118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33118step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33118step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33118 raw33118Labels = mixedMoment B node879 node879Labels := by
  calc
    mixedMoment B raw33118 raw33118Labels = mixedMoment B raw33118step0 raw33118step0Labels := by
      have ha : raw33118step0 = (fun i j => raw33118 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33118step0 raw33118; decide +kernel
      have hl : raw33118step0Labels = raw33118Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33118 raw33118Labels permutation166 permutation3
    _ = mixedMoment B node879 node879Labels := by rfl

def raw33119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33119step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33119 raw33119Labels = mixedMoment B node2305 node2305Labels := by
  calc
    mixedMoment B raw33119 raw33119Labels = mixedMoment B raw33119step0 raw33119step0Labels := by
      have ha : raw33119step0 = (fun i j => raw33119 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33119step0 raw33119; decide +kernel
      have hl : raw33119step0Labels = raw33119Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33119 raw33119Labels permutation166 permutation3
    _ = mixedMoment B node2305 node2305Labels := by rfl

def raw33120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33120Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33120step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33120 raw33120Labels = mixedMoment B node2462 node2462Labels := by
  calc
    mixedMoment B raw33120 raw33120Labels = mixedMoment B raw33120step0 raw33120step0Labels := by
      have ha : raw33120step0 = (fun i j => raw33120 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33120step0 raw33120; decide +kernel
      have hl : raw33120step0Labels = raw33120Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33120 raw33120Labels permutation166 permutation3
    _ = mixedMoment B node2462 node2462Labels := by rfl

def raw33121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33121Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33121step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33121 raw33121Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw33121 raw33121Labels = mixedMoment B raw33121step0 raw33121step0Labels := by
      have ha : raw33121step0 = (fun i j => raw33121 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33121step0 raw33121; decide +kernel
      have hl : raw33121step0Labels = raw33121Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33121 raw33121Labels permutation169 permutation3
    _ = mixedMoment B node2508 node2508Labels := by rfl

def raw33122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33122Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33122step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33122 raw33122Labels = mixedMoment B node866 node866Labels := by
  calc
    mixedMoment B raw33122 raw33122Labels = mixedMoment B raw33122step0 raw33122step0Labels := by
      have ha : raw33122step0 = (fun i j => raw33122 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33122step0 raw33122; decide +kernel
      have hl : raw33122step0Labels = raw33122Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33122 raw33122Labels permutation155 permutation3
    _ = mixedMoment B node866 node866Labels := by rfl

def raw33123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33123Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33123 raw33123Labels = mixedMoment B node2296 node2296Labels := by
  calc
    mixedMoment B raw33123 raw33123Labels = mixedMoment B raw33123step0 raw33123step0Labels := by
      have ha : raw33123step0 = (fun i j => raw33123 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33123step0 raw33123; decide +kernel
      have hl : raw33123step0Labels = raw33123Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33123 raw33123Labels permutation155 permutation3
    _ = mixedMoment B node2296 node2296Labels := by rfl

def raw33124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33124Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33124 raw33124Labels = mixedMoment B node2428 node2428Labels := by
  calc
    mixedMoment B raw33124 raw33124Labels = mixedMoment B raw33124step0 raw33124step0Labels := by
      have ha : raw33124step0 = (fun i j => raw33124 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33124step0 raw33124; decide +kernel
      have hl : raw33124step0Labels = raw33124Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33124 raw33124Labels permutation155 permutation3
    _ = mixedMoment B node2428 node2428Labels := by rfl

def raw33125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33125Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33125 raw33125Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw33125 raw33125Labels = mixedMoment B raw33125step0 raw33125step0Labels := by
      have ha : raw33125step0 = (fun i j => raw33125 (permutation165 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33125step0 raw33125; decide +kernel
      have hl : raw33125step0Labels = raw33125Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33125 raw33125Labels permutation165 permutation3
    _ = mixedMoment B node2452 node2452Labels := by rfl

def raw33126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33126Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33126step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33126 raw33126Labels = mixedMoment B node2479 node2479Labels := by
  calc
    mixedMoment B raw33126 raw33126Labels = mixedMoment B raw33126step0 raw33126step0Labels := by
      have ha : raw33126step0 = (fun i j => raw33126 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33126step0 raw33126; decide +kernel
      have hl : raw33126step0Labels = raw33126Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33126 raw33126Labels permutation155 permutation3
    _ = mixedMoment B node2479 node2479Labels := by rfl

def raw33127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33127Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw33127step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33127step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33127 raw33127Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw33127 raw33127Labels = mixedMoment B raw33127step0 raw33127step0Labels := by
      have hz : ∀ j, raw33127 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33127step0 = (fun i j => raw33127 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33127step0 raw33127; decide +kernel
      have hl : raw33127step0Labels = raw33127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33127 raw33127Labels permutation434 hz
    mixedMoment B raw33127step0 raw33127step0Labels = mixedMoment B raw33127step1 raw33127step1Labels := by
      have ha : raw33127step1 = (fun i j => raw33127step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33127step1 raw33127step0; decide +kernel
      have hl : raw33127step1Labels = raw33127step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33127step0 raw33127step0Labels permutation32 permutation3
    _ = mixedMoment B node2489 node2489Labels := by rfl

def raw33128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33128Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33128step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33128 raw33128Labels = mixedMoment B node865 node865Labels := by
  calc
    mixedMoment B raw33128 raw33128Labels = mixedMoment B raw33128step0 raw33128step0Labels := by
      have ha : raw33128step0 = (fun i j => raw33128 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33128step0 raw33128; decide +kernel
      have hl : raw33128step0Labels = raw33128Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33128 raw33128Labels permutation154 permutation3
    _ = mixedMoment B node865 node865Labels := by rfl

def raw33129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33129Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33129 raw33129Labels = mixedMoment B node2295 node2295Labels := by
  calc
    mixedMoment B raw33129 raw33129Labels = mixedMoment B raw33129step0 raw33129step0Labels := by
      have ha : raw33129step0 = (fun i j => raw33129 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33129step0 raw33129; decide +kernel
      have hl : raw33129step0Labels = raw33129Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33129 raw33129Labels permutation154 permutation3
    _ = mixedMoment B node2295 node2295Labels := by rfl

def raw33130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33130Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33130step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33130 raw33130Labels = mixedMoment B node2425 node2425Labels := by
  calc
    mixedMoment B raw33130 raw33130Labels = mixedMoment B raw33130step0 raw33130step0Labels := by
      have ha : raw33130step0 = (fun i j => raw33130 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33130step0 raw33130; decide +kernel
      have hl : raw33130step0Labels = raw33130Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33130 raw33130Labels permutation154 permutation3
    _ = mixedMoment B node2425 node2425Labels := by rfl

def raw33131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw33131Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33131step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33131 raw33131Labels = mixedMoment B node2449 node2449Labels := by
  calc
    mixedMoment B raw33131 raw33131Labels = mixedMoment B raw33131step0 raw33131step0Labels := by
      have ha : raw33131step0 = (fun i j => raw33131 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33131step0 raw33131; decide +kernel
      have hl : raw33131step0Labels = raw33131Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33131 raw33131Labels permutation164 permutation3
    _ = mixedMoment B node2449 node2449Labels := by rfl

def raw33132 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33132step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33132step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33132 raw33132Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw33132 raw33132Labels = mixedMoment B raw33132step0 raw33132step0Labels := by
      have ha : raw33132step0 = (fun i j => raw33132 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33132step0 raw33132; decide +kernel
      have hl : raw33132step0Labels = raw33132Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33132 raw33132Labels permutation152 permutation7
    mixedMoment B raw33132step0 raw33132step0Labels = mixedMoment B raw33132step1 raw33132step1Labels := by
      have ha : raw33132step1 = raw33132step0 := by apply Matrix.ext; unfold raw33132step1 raw33132step0; decide +kernel
      have hl : raw33132step0Labels = labelEmbedding10 ∘ raw33132step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33132step0 raw33132step0Labels raw33132step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw33133 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33133step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33133step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33133step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33133 raw33133Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw33133 raw33133Labels = mixedMoment B raw33133step0 raw33133step0Labels := by
      have hz : ∀ j, raw33133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33133step0 = (fun i j => raw33133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33133step0 raw33133; decide +kernel
      have hl : raw33133step0Labels = raw33133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33133 raw33133Labels permutation346 hz
    mixedMoment B raw33133step0 raw33133step0Labels = mixedMoment B raw33133step1 raw33133step1Labels := by
      have ha : raw33133step1 = (fun i j => raw33133step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33133step1 raw33133step0; decide +kernel
      have hl : raw33133step1Labels = raw33133step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33133step0 raw33133step0Labels permutation32 permutation7
    mixedMoment B raw33133step1 raw33133step1Labels = mixedMoment B raw33133step2 raw33133step2Labels := by
      have ha : raw33133step2 = raw33133step1 := by apply Matrix.ext; unfold raw33133step2 raw33133step1; decide +kernel
      have hl : raw33133step1Labels = labelEmbedding10 ∘ raw33133step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33133step1 raw33133step1Labels raw33133step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw33134 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw33134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33134step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33134step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33134step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33134 raw33134Labels = mixedMoment B node5135 node5135Labels := by
  calc
    mixedMoment B raw33134 raw33134Labels = mixedMoment B raw33134step0 raw33134step0Labels := by
      have ha : raw33134step0 = (fun i j => raw33134 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33134step0 raw33134; decide +kernel
      have hl : raw33134step0Labels = raw33134Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33134 raw33134Labels permutation152 permutation7
    mixedMoment B raw33134step0 raw33134step0Labels = mixedMoment B raw33134step1 raw33134step1Labels := by
      have ha : raw33134step1 = raw33134step0 := by apply Matrix.ext; unfold raw33134step1 raw33134step0; decide +kernel
      have hl : raw33134step0Labels = labelEmbedding10 ∘ raw33134step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33134step0 raw33134step0Labels raw33134step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5135 node5135Labels := by rfl

def raw33135 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33135step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33135step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33135step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33135 raw33135Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw33135 raw33135Labels = mixedMoment B raw33135step0 raw33135step0Labels := by
      have ha : raw33135step0 = (fun i j => raw33135 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33135step0 raw33135; decide +kernel
      have hl : raw33135step0Labels = raw33135Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33135 raw33135Labels permutation152 permutation7
    mixedMoment B raw33135step0 raw33135step0Labels = mixedMoment B raw33135step1 raw33135step1Labels := by
      have ha : raw33135step1 = raw33135step0 := by apply Matrix.ext; unfold raw33135step1 raw33135step0; decide +kernel
      have hl : raw33135step0Labels = labelEmbedding10 ∘ raw33135step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33135step0 raw33135step0Labels raw33135step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw33136 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw33136step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33136step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33136step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33136step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33136 raw33136Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw33136 raw33136Labels = mixedMoment B raw33136step0 raw33136step0Labels := by
      have ha : raw33136step0 = (fun i j => raw33136 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33136step0 raw33136; decide +kernel
      have hl : raw33136step0Labels = raw33136Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33136 raw33136Labels permutation167 permutation4
    mixedMoment B raw33136step0 raw33136step0Labels = mixedMoment B raw33136step1 raw33136step1Labels := by
      have ha : raw33136step1 = -raw33136step0 := by apply Matrix.ext; change ∀ i j, raw33136step1 i j = -(raw33136step0 i j); unfold raw33136step1 raw33136step0; decide +kernel
      have hl : raw33136step1Labels = raw33136step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33136step1 raw33136step1Labels = mixedMoment B raw33136step2 raw33136step2Labels := by
      have ha : raw33136step2 = raw33136step1 := by apply Matrix.ext; unfold raw33136step2 raw33136step1; decide +kernel
      have hl : raw33136step1Labels = labelEmbedding7 ∘ raw33136step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33136step1 raw33136step1Labels raw33136step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

def raw33137 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33137step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33137 raw33137Labels = mixedMoment B node5005 node5005Labels := by
  calc
    mixedMoment B raw33137 raw33137Labels = mixedMoment B raw33137step0 raw33137step0Labels := by
      have ha : raw33137step0 = (fun i j => raw33137 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33137step0 raw33137; decide +kernel
      have hl : raw33137step0Labels = raw33137Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33137 raw33137Labels permutation154 permutation6
    mixedMoment B raw33137step0 raw33137step0Labels = mixedMoment B raw33137step1 raw33137step1Labels := by
      have ha : raw33137step1 = raw33137step0 := by apply Matrix.ext; unfold raw33137step1 raw33137step0; decide +kernel
      have hl : raw33137step0Labels = labelEmbedding9 ∘ raw33137step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33137step0 raw33137step0Labels raw33137step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5005 node5005Labels := by rfl

def raw33138 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw33138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33138step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33138step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33138step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33138 raw33138Labels = mixedMoment B node5083 node5083Labels := by
  calc
    mixedMoment B raw33138 raw33138Labels = mixedMoment B raw33138step0 raw33138step0Labels := by
      have ha : raw33138step0 = (fun i j => raw33138 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33138step0 raw33138; decide +kernel
      have hl : raw33138step0Labels = raw33138Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33138 raw33138Labels permutation154 permutation6
    mixedMoment B raw33138step0 raw33138step0Labels = mixedMoment B raw33138step1 raw33138step1Labels := by
      have ha : raw33138step1 = raw33138step0 := by apply Matrix.ext; unfold raw33138step1 raw33138step0; decide +kernel
      have hl : raw33138step0Labels = labelEmbedding9 ∘ raw33138step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33138step0 raw33138step0Labels raw33138step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5083 node5083Labels := by rfl

def raw33139 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33139step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33139step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33139 raw33139Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw33139 raw33139Labels = mixedMoment B raw33139step0 raw33139step0Labels := by
      have ha : raw33139step0 = (fun i j => raw33139 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33139step0 raw33139; decide +kernel
      have hl : raw33139step0Labels = raw33139Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33139 raw33139Labels permutation154 permutation6
    mixedMoment B raw33139step0 raw33139step0Labels = mixedMoment B raw33139step1 raw33139step1Labels := by
      have ha : raw33139step1 = raw33139step0 := by apply Matrix.ext; unfold raw33139step1 raw33139step0; decide +kernel
      have hl : raw33139step0Labels = labelEmbedding9 ∘ raw33139step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33139step0 raw33139step0Labels raw33139step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5086 node5086Labels := by rfl

def raw33140 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw33140step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33140step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33140step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33140step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33140step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33140 raw33140Labels = mixedMoment B node4737 node4737Labels := by
  calc
    mixedMoment B raw33140 raw33140Labels = mixedMoment B raw33140step0 raw33140step0Labels := by
      have ha : raw33140step0 = (fun i j => raw33140 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33140step0 raw33140; decide +kernel
      have hl : raw33140step0Labels = raw33140Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33140 raw33140Labels permutation165 permutation4
    mixedMoment B raw33140step0 raw33140step0Labels = mixedMoment B raw33140step1 raw33140step1Labels := by
      have ha : raw33140step1 = -raw33140step0 := by apply Matrix.ext; change ∀ i j, raw33140step1 i j = -(raw33140step0 i j); unfold raw33140step1 raw33140step0; decide +kernel
      have hl : raw33140step1Labels = raw33140step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33140step1 raw33140step1Labels = mixedMoment B raw33140step2 raw33140step2Labels := by
      have ha : raw33140step2 = raw33140step1 := by apply Matrix.ext; unfold raw33140step2 raw33140step1; decide +kernel
      have hl : raw33140step1Labels = labelEmbedding7 ∘ raw33140step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33140step1 raw33140step1Labels raw33140step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4737 node4737Labels := by rfl

def raw33141 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33141step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33141step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33141 raw33141Labels = mixedMoment B node4997 node4997Labels := by
  calc
    mixedMoment B raw33141 raw33141Labels = mixedMoment B raw33141step0 raw33141step0Labels := by
      have ha : raw33141step0 = (fun i j => raw33141 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33141step0 raw33141; decide +kernel
      have hl : raw33141step0Labels = raw33141Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33141 raw33141Labels permutation154 permutation6
    mixedMoment B raw33141step0 raw33141step0Labels = mixedMoment B raw33141step1 raw33141step1Labels := by
      have ha : raw33141step1 = raw33141step0 := by apply Matrix.ext; unfold raw33141step1 raw33141step0; decide +kernel
      have hl : raw33141step0Labels = labelEmbedding9 ∘ raw33141step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33141step0 raw33141step0Labels raw33141step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4997 node4997Labels := by rfl

def raw33142 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33142step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33142step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33142 raw33142Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw33142 raw33142Labels = mixedMoment B raw33142step0 raw33142step0Labels := by
      have hz : ∀ j, raw33142 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33142step0 = (fun i j => raw33142 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33142step0 raw33142; decide +kernel
      have hl : raw33142step0Labels = raw33142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33142 raw33142Labels permutation346 hz
    mixedMoment B raw33142step0 raw33142step0Labels = mixedMoment B raw33142step1 raw33142step1Labels := by
      have ha : raw33142step1 = (fun i j => raw33142step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33142step1 raw33142step0; decide +kernel
      have hl : raw33142step1Labels = raw33142step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33142step0 raw33142step0Labels permutation34 permutation6
    mixedMoment B raw33142step1 raw33142step1Labels = mixedMoment B raw33142step2 raw33142step2Labels := by
      have ha : raw33142step2 = raw33142step1 := by apply Matrix.ext; unfold raw33142step2 raw33142step1; decide +kernel
      have hl : raw33142step1Labels = labelEmbedding9 ∘ raw33142step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33142step1 raw33142step1Labels raw33142step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw33143 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw33143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33143step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33143step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33143step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33143 raw33143Labels = mixedMoment B node5071 node5071Labels := by
  calc
    mixedMoment B raw33143 raw33143Labels = mixedMoment B raw33143step0 raw33143step0Labels := by
      have ha : raw33143step0 = (fun i j => raw33143 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33143step0 raw33143; decide +kernel
      have hl : raw33143step0Labels = raw33143Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33143 raw33143Labels permutation154 permutation6
    mixedMoment B raw33143step0 raw33143step0Labels = mixedMoment B raw33143step1 raw33143step1Labels := by
      have ha : raw33143step1 = raw33143step0 := by apply Matrix.ext; unfold raw33143step1 raw33143step0; decide +kernel
      have hl : raw33143step0Labels = labelEmbedding9 ∘ raw33143step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33143step0 raw33143step0Labels raw33143step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5071 node5071Labels := by rfl

def raw33144 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw33144step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33144step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw33144step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33144 raw33144Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw33144 raw33144Labels = mixedMoment B raw33144step0 raw33144step0Labels := by
      have ha : raw33144step0 = (fun i j => raw33144 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33144step0 raw33144; decide +kernel
      have hl : raw33144step0Labels = raw33144Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33144 raw33144Labels permutation154 permutation6
    mixedMoment B raw33144step0 raw33144step0Labels = mixedMoment B raw33144step1 raw33144step1Labels := by
      have ha : raw33144step1 = raw33144step0 := by apply Matrix.ext; unfold raw33144step1 raw33144step0; decide +kernel
      have hl : raw33144step0Labels = labelEmbedding9 ∘ raw33144step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33144step0 raw33144step0Labels raw33144step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw33145 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33145step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33145step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33145step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33145 raw33145Labels = mixedMoment B node4739 node4739Labels := by
  calc
    mixedMoment B raw33145 raw33145Labels = mixedMoment B raw33145step0 raw33145step0Labels := by
      have ha : raw33145step0 = (fun i j => raw33145 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33145step0 raw33145; decide +kernel
      have hl : raw33145step0Labels = raw33145Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33145 raw33145Labels permutation152 permutation6
    mixedMoment B raw33145step0 raw33145step0Labels = mixedMoment B raw33145step1 raw33145step1Labels := by
      have ha : raw33145step1 = raw33145step0 := by apply Matrix.ext; unfold raw33145step1 raw33145step0; decide +kernel
      have hl : raw33145step0Labels = labelEmbedding9 ∘ raw33145step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33145step0 raw33145step0Labels raw33145step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4739 node4739Labels := by rfl

def raw33146 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33146step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33146step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33146 raw33146Labels = mixedMoment B node4998 node4998Labels := by
  calc
    mixedMoment B raw33146 raw33146Labels = mixedMoment B raw33146step0 raw33146step0Labels := by
      have ha : raw33146step0 = (fun i j => raw33146 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33146step0 raw33146; decide +kernel
      have hl : raw33146step0Labels = raw33146Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33146 raw33146Labels permutation152 permutation6
    mixedMoment B raw33146step0 raw33146step0Labels = mixedMoment B raw33146step1 raw33146step1Labels := by
      have ha : raw33146step1 = raw33146step0 := by apply Matrix.ext; unfold raw33146step1 raw33146step0; decide +kernel
      have hl : raw33146step0Labels = labelEmbedding9 ∘ raw33146step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33146step0 raw33146step0Labels raw33146step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4998 node4998Labels := by rfl

def raw33147 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw33147step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33147step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33147step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33147step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33147step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33147 raw33147Labels = mixedMoment B node4736 node4736Labels := by
  calc
    mixedMoment B raw33147 raw33147Labels = mixedMoment B raw33147step0 raw33147step0Labels := by
      have ha : raw33147step0 = (fun i j => raw33147 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33147step0 raw33147; decide +kernel
      have hl : raw33147step0Labels = raw33147Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33147 raw33147Labels permutation164 permutation4
    mixedMoment B raw33147step0 raw33147step0Labels = mixedMoment B raw33147step1 raw33147step1Labels := by
      have ha : raw33147step1 = -raw33147step0 := by apply Matrix.ext; change ∀ i j, raw33147step1 i j = -(raw33147step0 i j); unfold raw33147step1 raw33147step0; decide +kernel
      have hl : raw33147step1Labels = raw33147step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33147step1 raw33147step1Labels = mixedMoment B raw33147step2 raw33147step2Labels := by
      have ha : raw33147step2 = raw33147step1 := by apply Matrix.ext; unfold raw33147step2 raw33147step1; decide +kernel
      have hl : raw33147step1Labels = labelEmbedding7 ∘ raw33147step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33147step1 raw33147step1Labels raw33147step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4736 node4736Labels := by rfl

def raw33148 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33148step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33148step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33148step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33148step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33148 raw33148Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw33148 raw33148Labels = mixedMoment B raw33148step0 raw33148step0Labels := by
      have ha : raw33148step0 = (fun i j => raw33148 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33148step0 raw33148; decide +kernel
      have hl : raw33148step0Labels = raw33148Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33148 raw33148Labels permutation154 permutation6
    mixedMoment B raw33148step0 raw33148step0Labels = mixedMoment B raw33148step1 raw33148step1Labels := by
      have ha : raw33148step1 = raw33148step0 := by apply Matrix.ext; unfold raw33148step1 raw33148step0; decide +kernel
      have hl : raw33148step0Labels = labelEmbedding9 ∘ raw33148step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33148step0 raw33148step0Labels raw33148step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

def raw33149 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw33149Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw33149step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33149step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33149 raw33149Labels = mixedMoment B node3444 node3444Labels := by
  calc
    mixedMoment B raw33149 raw33149Labels = mixedMoment B raw33149step0 raw33149step0Labels := by
      have ha : raw33149step0 = (fun i j => raw33149 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33149step0 raw33149; decide +kernel
      have hl : raw33149step0Labels = raw33149Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33149 raw33149Labels permutation164 permutation4
    mixedMoment B raw33149step0 raw33149step0Labels = mixedMoment B raw33149step1 raw33149step1Labels := by
      have ha : raw33149step1 = -raw33149step0 := by apply Matrix.ext; change ∀ i j, raw33149step1 i j = -(raw33149step0 i j); unfold raw33149step1 raw33149step0; decide +kernel
      have hl : raw33149step1Labels = raw33149step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3444 node3444Labels := by rfl

def raw33150 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw33150Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33150step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw33150step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33150step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33150step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33150 raw33150Labels = mixedMoment B node2075 node2075Labels := by
  calc
    mixedMoment B raw33150 raw33150Labels = mixedMoment B raw33150step0 raw33150step0Labels := by
      have ha : raw33150step0 = (fun i j => raw33150 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33150step0 raw33150; decide +kernel
      have hl : raw33150step0Labels = raw33150Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33150 raw33150Labels permutation224 permutation4
    mixedMoment B raw33150step0 raw33150step0Labels = mixedMoment B raw33150step1 raw33150step1Labels := by
      have ha : raw33150step1 = -raw33150step0 := by apply Matrix.ext; change ∀ i j, raw33150step1 i j = -(raw33150step0 i j); unfold raw33150step1 raw33150step0; decide +kernel
      have hl : raw33150step1Labels = raw33150step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2075 node2075Labels := by rfl

def raw33151 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw33151Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw33151step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33151step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33151step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33151 raw33151Labels = mixedMoment B node1878 node1878Labels := by
  calc
    mixedMoment B raw33151 raw33151Labels = mixedMoment B raw33151step0 raw33151step0Labels := by
      have ha : raw33151step0 = (fun i j => raw33151 (permutation166 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33151step0 raw33151; decide +kernel
      have hl : raw33151step0Labels = raw33151Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33151 raw33151Labels permutation166 permutation4
    mixedMoment B raw33151step0 raw33151step0Labels = mixedMoment B raw33151step1 raw33151step1Labels := by
      have ha : raw33151step1 = -raw33151step0 := by apply Matrix.ext; change ∀ i j, raw33151step1 i j = -(raw33151step0 i j); unfold raw33151step1 raw33151step0; decide +kernel
      have hl : raw33151step1Labels = raw33151step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1878 node1878Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
