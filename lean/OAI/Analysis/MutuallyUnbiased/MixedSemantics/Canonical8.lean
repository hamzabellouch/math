import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1024 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1024 raw1024Labels = mixedMoment B node865 node865Labels := by
  calc
    mixedMoment B raw1024 raw1024Labels = mixedMoment B raw1024step0 raw1024step0Labels := by
      have ha : raw1024step0 = (fun i j => raw1024 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1024step0 raw1024; decide +kernel
      have hl : raw1024step0Labels = raw1024Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1024 raw1024Labels permutation152 permutation4
    _ = mixedMoment B node865 node865Labels := by rfl

def raw1025 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1025Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw1025step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1025step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1025step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1025step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1025step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1025 raw1025Labels = mixedMoment B node1553 node1553Labels := by
  calc
    mixedMoment B raw1025 raw1025Labels = mixedMoment B raw1025step0 raw1025step0Labels := by
      have ha : raw1025step0 = (fun i j => raw1025 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1025step0 raw1025; decide +kernel
      have hl : raw1025step0Labels = raw1025Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1025 raw1025Labels permutation158 permutation6
    mixedMoment B raw1025step0 raw1025step0Labels = mixedMoment B raw1025step1 raw1025step1Labels := by
      have ha : raw1025step1 = -raw1025step0 := by apply Matrix.ext; change ∀ i j, raw1025step1 i j = -(raw1025step0 i j); unfold raw1025step1 raw1025step0; decide +kernel
      have hl : raw1025step1Labels = raw1025step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1025step1 raw1025step1Labels = mixedMoment B raw1025step2 raw1025step2Labels := by
      have ha : raw1025step2 = raw1025step1 := by apply Matrix.ext; unfold raw1025step2 raw1025step1; decide +kernel
      have hl : raw1025step1Labels = labelEmbedding1 ∘ raw1025step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1025step1 raw1025step1Labels raw1025step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1553 node1553Labels := by rfl

def raw1026 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1026step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1026step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1026step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1026 raw1026Labels = mixedMoment B node4288 node4288Labels := by
  calc
    mixedMoment B raw1026 raw1026Labels = mixedMoment B raw1026step0 raw1026step0Labels := by
      have ha : raw1026step0 = (fun i j => raw1026 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1026step0 raw1026; decide +kernel
      have hl : raw1026step0Labels = raw1026Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1026 raw1026Labels permutation152 permutation4
    mixedMoment B raw1026step0 raw1026step0Labels = mixedMoment B raw1026step1 raw1026step1Labels := by
      have ha : raw1026step1 = raw1026step0 := by apply Matrix.ext; unfold raw1026step1 raw1026step0; decide +kernel
      have hl : raw1026step0Labels = labelEmbedding7 ∘ raw1026step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1026step0 raw1026step0Labels raw1026step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4288 node4288Labels := by rfl

def raw1027 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1027 raw1027Labels = mixedMoment B node866 node866Labels := by
  calc
    mixedMoment B raw1027 raw1027Labels = mixedMoment B raw1027step0 raw1027step0Labels := by
      have ha : raw1027step0 = (fun i j => raw1027 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1027step0 raw1027; decide +kernel
      have hl : raw1027step0Labels = raw1027Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1027 raw1027Labels permutation152 permutation4
    _ = mixedMoment B node866 node866Labels := by rfl

def raw1028 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1028Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw1028step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1028step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1028step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1028step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1028 raw1028Labels = mixedMoment B node1554 node1554Labels := by
  calc
    mixedMoment B raw1028 raw1028Labels = mixedMoment B raw1028step0 raw1028step0Labels := by
      have ha : raw1028step0 = (fun i j => raw1028 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1028step0 raw1028; decide +kernel
      have hl : raw1028step0Labels = raw1028Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1028 raw1028Labels permutation158 permutation6
    mixedMoment B raw1028step0 raw1028step0Labels = mixedMoment B raw1028step1 raw1028step1Labels := by
      have ha : raw1028step1 = -raw1028step0 := by apply Matrix.ext; change ∀ i j, raw1028step1 i j = -(raw1028step0 i j); unfold raw1028step1 raw1028step0; decide +kernel
      have hl : raw1028step1Labels = raw1028step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1028step1 raw1028step1Labels = mixedMoment B raw1028step2 raw1028step2Labels := by
      have ha : raw1028step2 = raw1028step1 := by apply Matrix.ext; unfold raw1028step2 raw1028step1; decide +kernel
      have hl : raw1028step1Labels = labelEmbedding1 ∘ raw1028step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1028step1 raw1028step1Labels raw1028step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1554 node1554Labels := by rfl

def raw1029 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw1029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw1029step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw1029step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1029 raw1029Labels = mixedMoment B node4289 node4289Labels := by
  calc
    mixedMoment B raw1029 raw1029Labels = mixedMoment B raw1029step0 raw1029step0Labels := by
      have ha : raw1029step0 = (fun i j => raw1029 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1029step0 raw1029; decide +kernel
      have hl : raw1029step0Labels = raw1029Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1029 raw1029Labels permutation32 permutation4
    mixedMoment B raw1029step0 raw1029step0Labels = mixedMoment B raw1029step1 raw1029step1Labels := by
      have ha : raw1029step1 = raw1029step0 := by apply Matrix.ext; unfold raw1029step1 raw1029step0; decide +kernel
      have hl : raw1029step0Labels = labelEmbedding7 ∘ raw1029step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1029step0 raw1029step0Labels raw1029step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4289 node4289Labels := by rfl

def raw1030 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw1030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw1030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1030 raw1030Labels = mixedMoment B node867 node867Labels := by
  calc
    mixedMoment B raw1030 raw1030Labels = mixedMoment B raw1030step0 raw1030step0Labels := by
      have ha : raw1030step0 = (fun i j => raw1030 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1030step0 raw1030; decide +kernel
      have hl : raw1030step0Labels = raw1030Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1030 raw1030Labels permutation32 permutation4
    _ = mixedMoment B node867 node867Labels := by rfl

def raw1031 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw1031Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, -1, 4]]
def raw1031step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw1031step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw1031step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1031 raw1031Labels = mixedMoment B node1555 node1555Labels := by
  calc
    mixedMoment B raw1031 raw1031Labels = mixedMoment B raw1031step0 raw1031step0Labels := by
      have ha : raw1031step0 = (fun i j => raw1031 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1031step0 raw1031; decide +kernel
      have hl : raw1031step0Labels = raw1031Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1031 raw1031Labels permutation34 permutation6
    mixedMoment B raw1031step0 raw1031step0Labels = mixedMoment B raw1031step1 raw1031step1Labels := by
      have ha : raw1031step1 = -raw1031step0 := by apply Matrix.ext; change ∀ i j, raw1031step1 i j = -(raw1031step0 i j); unfold raw1031step1 raw1031step0; decide +kernel
      have hl : raw1031step1Labels = raw1031step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1031step1 raw1031step1Labels = mixedMoment B raw1031step2 raw1031step2Labels := by
      have ha : raw1031step2 = raw1031step1 := by apply Matrix.ext; unfold raw1031step2 raw1031step1; decide +kernel
      have hl : raw1031step1Labels = labelEmbedding1 ∘ raw1031step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1031step1 raw1031step1Labels raw1031step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1555 node1555Labels := by rfl

def raw1032 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1032step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1032step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1032 raw1032Labels = mixedMoment B node4290 node4290Labels := by
  calc
    mixedMoment B raw1032 raw1032Labels = mixedMoment B raw1032step0 raw1032step0Labels := by
      have ha : raw1032step0 = (fun i j => raw1032 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1032step0 raw1032; decide +kernel
      have hl : raw1032step0Labels = raw1032Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1032 raw1032Labels permutation152 permutation4
    mixedMoment B raw1032step0 raw1032step0Labels = mixedMoment B raw1032step1 raw1032step1Labels := by
      have ha : raw1032step1 = raw1032step0 := by apply Matrix.ext; unfold raw1032step1 raw1032step0; decide +kernel
      have hl : raw1032step0Labels = labelEmbedding7 ∘ raw1032step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1032step0 raw1032step0Labels raw1032step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4290 node4290Labels := by rfl

def raw1033 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1033 raw1033Labels = mixedMoment B node868 node868Labels := by
  calc
    mixedMoment B raw1033 raw1033Labels = mixedMoment B raw1033step0 raw1033step0Labels := by
      have ha : raw1033step0 = (fun i j => raw1033 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1033step0 raw1033; decide +kernel
      have hl : raw1033step0Labels = raw1033Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1033 raw1033Labels permutation152 permutation4
    _ = mixedMoment B node868 node868Labels := by rfl

def raw1034 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1034Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1034step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1034step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1034step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1034step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1034 raw1034Labels = mixedMoment B node1566 node1566Labels := by
  calc
    mixedMoment B raw1034 raw1034Labels = mixedMoment B raw1034step0 raw1034step0Labels := by
      have ha : raw1034step0 = (fun i j => raw1034 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1034step0 raw1034; decide +kernel
      have hl : raw1034step0Labels = raw1034Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1034 raw1034Labels permutation152 permutation6
    mixedMoment B raw1034step0 raw1034step0Labels = mixedMoment B raw1034step1 raw1034step1Labels := by
      have ha : raw1034step1 = -raw1034step0 := by apply Matrix.ext; change ∀ i j, raw1034step1 i j = -(raw1034step0 i j); unfold raw1034step1 raw1034step0; decide +kernel
      have hl : raw1034step1Labels = raw1034step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1034step1 raw1034step1Labels = mixedMoment B raw1034step2 raw1034step2Labels := by
      have ha : raw1034step2 = raw1034step1 := by apply Matrix.ext; unfold raw1034step2 raw1034step1; decide +kernel
      have hl : raw1034step1Labels = labelEmbedding1 ∘ raw1034step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1034step1 raw1034step1Labels raw1034step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1566 node1566Labels := by rfl

def raw1035 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1035step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1035step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1035 raw1035Labels = mixedMoment B node4291 node4291Labels := by
  calc
    mixedMoment B raw1035 raw1035Labels = mixedMoment B raw1035step0 raw1035step0Labels := by
      have ha : raw1035step0 = (fun i j => raw1035 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1035step0 raw1035; decide +kernel
      have hl : raw1035step0Labels = raw1035Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1035 raw1035Labels permutation152 permutation4
    mixedMoment B raw1035step0 raw1035step0Labels = mixedMoment B raw1035step1 raw1035step1Labels := by
      have ha : raw1035step1 = raw1035step0 := by apply Matrix.ext; unfold raw1035step1 raw1035step0; decide +kernel
      have hl : raw1035step0Labels = labelEmbedding7 ∘ raw1035step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1035step0 raw1035step0Labels raw1035step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4291 node4291Labels := by rfl

def raw1036 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1036 raw1036Labels = mixedMoment B node869 node869Labels := by
  calc
    mixedMoment B raw1036 raw1036Labels = mixedMoment B raw1036step0 raw1036step0Labels := by
      have ha : raw1036step0 = (fun i j => raw1036 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1036step0 raw1036; decide +kernel
      have hl : raw1036step0Labels = raw1036Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1036 raw1036Labels permutation152 permutation4
    _ = mixedMoment B node869 node869Labels := by rfl

def raw1037 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1037Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw1037step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1037step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1037step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1037step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1037 raw1037Labels = mixedMoment B node1561 node1561Labels := by
  calc
    mixedMoment B raw1037 raw1037Labels = mixedMoment B raw1037step0 raw1037step0Labels := by
      have ha : raw1037step0 = (fun i j => raw1037 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1037step0 raw1037; decide +kernel
      have hl : raw1037step0Labels = raw1037Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1037 raw1037Labels permutation164 permutation6
    mixedMoment B raw1037step0 raw1037step0Labels = mixedMoment B raw1037step1 raw1037step1Labels := by
      have ha : raw1037step1 = -raw1037step0 := by apply Matrix.ext; change ∀ i j, raw1037step1 i j = -(raw1037step0 i j); unfold raw1037step1 raw1037step0; decide +kernel
      have hl : raw1037step1Labels = raw1037step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1037step1 raw1037step1Labels = mixedMoment B raw1037step2 raw1037step2Labels := by
      have ha : raw1037step2 = raw1037step1 := by apply Matrix.ext; unfold raw1037step2 raw1037step1; decide +kernel
      have hl : raw1037step1Labels = labelEmbedding1 ∘ raw1037step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1037step1 raw1037step1Labels raw1037step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1561 node1561Labels := by rfl

def raw1038 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1038step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1038step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1038 raw1038Labels = mixedMoment B node4292 node4292Labels := by
  calc
    mixedMoment B raw1038 raw1038Labels = mixedMoment B raw1038step0 raw1038step0Labels := by
      have ha : raw1038step0 = (fun i j => raw1038 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1038step0 raw1038; decide +kernel
      have hl : raw1038step0Labels = raw1038Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1038 raw1038Labels permutation152 permutation4
    mixedMoment B raw1038step0 raw1038step0Labels = mixedMoment B raw1038step1 raw1038step1Labels := by
      have ha : raw1038step1 = raw1038step0 := by apply Matrix.ext; unfold raw1038step1 raw1038step0; decide +kernel
      have hl : raw1038step0Labels = labelEmbedding7 ∘ raw1038step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1038step0 raw1038step0Labels raw1038step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4292 node4292Labels := by rfl

def raw1039 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1039Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1039step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1039 raw1039Labels = mixedMoment B node870 node870Labels := by
  calc
    mixedMoment B raw1039 raw1039Labels = mixedMoment B raw1039step0 raw1039step0Labels := by
      have ha : raw1039step0 = (fun i j => raw1039 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1039step0 raw1039; decide +kernel
      have hl : raw1039step0Labels = raw1039Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1039 raw1039Labels permutation152 permutation4
    _ = mixedMoment B node870 node870Labels := by rfl

def raw1040 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1040Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1040step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1040step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1040step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1040step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1040step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1040 raw1040Labels = mixedMoment B node1567 node1567Labels := by
  calc
    mixedMoment B raw1040 raw1040Labels = mixedMoment B raw1040step0 raw1040step0Labels := by
      have ha : raw1040step0 = (fun i j => raw1040 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1040step0 raw1040; decide +kernel
      have hl : raw1040step0Labels = raw1040Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1040 raw1040Labels permutation152 permutation6
    mixedMoment B raw1040step0 raw1040step0Labels = mixedMoment B raw1040step1 raw1040step1Labels := by
      have ha : raw1040step1 = -raw1040step0 := by apply Matrix.ext; change ∀ i j, raw1040step1 i j = -(raw1040step0 i j); unfold raw1040step1 raw1040step0; decide +kernel
      have hl : raw1040step1Labels = raw1040step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1040step1 raw1040step1Labels = mixedMoment B raw1040step2 raw1040step2Labels := by
      have ha : raw1040step2 = raw1040step1 := by apply Matrix.ext; unfold raw1040step2 raw1040step1; decide +kernel
      have hl : raw1040step1Labels = labelEmbedding1 ∘ raw1040step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1040step1 raw1040step1Labels raw1040step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1567 node1567Labels := by rfl

def raw1041 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw1041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw1041step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw1041step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1041 raw1041Labels = mixedMoment B node4293 node4293Labels := by
  calc
    mixedMoment B raw1041 raw1041Labels = mixedMoment B raw1041step0 raw1041step0Labels := by
      have ha : raw1041step0 = (fun i j => raw1041 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1041step0 raw1041; decide +kernel
      have hl : raw1041step0Labels = raw1041Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1041 raw1041Labels permutation32 permutation4
    mixedMoment B raw1041step0 raw1041step0Labels = mixedMoment B raw1041step1 raw1041step1Labels := by
      have ha : raw1041step1 = raw1041step0 := by apply Matrix.ext; unfold raw1041step1 raw1041step0; decide +kernel
      have hl : raw1041step0Labels = labelEmbedding7 ∘ raw1041step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1041step0 raw1041step0Labels raw1041step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4293 node4293Labels := by rfl

def raw1042 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw1042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw1042step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1042 raw1042Labels = mixedMoment B node871 node871Labels := by
  calc
    mixedMoment B raw1042 raw1042Labels = mixedMoment B raw1042step0 raw1042step0Labels := by
      have ha : raw1042step0 = (fun i j => raw1042 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1042step0 raw1042; decide +kernel
      have hl : raw1042step0Labels = raw1042Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1042 raw1042Labels permutation32 permutation4
    _ = mixedMoment B node871 node871Labels := by rfl

def raw1043 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw1043Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw1043step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw1043step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw1043step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1043 raw1043Labels = mixedMoment B node1568 node1568Labels := by
  calc
    mixedMoment B raw1043 raw1043Labels = mixedMoment B raw1043step0 raw1043step0Labels := by
      have ha : raw1043step0 = (fun i j => raw1043 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1043step0 raw1043; decide +kernel
      have hl : raw1043step0Labels = raw1043Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1043 raw1043Labels permutation32 permutation6
    mixedMoment B raw1043step0 raw1043step0Labels = mixedMoment B raw1043step1 raw1043step1Labels := by
      have ha : raw1043step1 = -raw1043step0 := by apply Matrix.ext; change ∀ i j, raw1043step1 i j = -(raw1043step0 i j); unfold raw1043step1 raw1043step0; decide +kernel
      have hl : raw1043step1Labels = raw1043step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1043step1 raw1043step1Labels = mixedMoment B raw1043step2 raw1043step2Labels := by
      have ha : raw1043step2 = raw1043step1 := by apply Matrix.ext; unfold raw1043step2 raw1043step1; decide +kernel
      have hl : raw1043step1Labels = labelEmbedding1 ∘ raw1043step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1043step1 raw1043step1Labels raw1043step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1568 node1568Labels := by rfl

def raw1044 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw1044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw1044step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw1044step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1044 raw1044Labels = mixedMoment B node4294 node4294Labels := by
  calc
    mixedMoment B raw1044 raw1044Labels = mixedMoment B raw1044step0 raw1044step0Labels := by
      have ha : raw1044step0 = (fun i j => raw1044 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1044step0 raw1044; decide +kernel
      have hl : raw1044step0Labels = raw1044Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1044 raw1044Labels permutation32 permutation4
    mixedMoment B raw1044step0 raw1044step0Labels = mixedMoment B raw1044step1 raw1044step1Labels := by
      have ha : raw1044step1 = raw1044step0 := by apply Matrix.ext; unfold raw1044step1 raw1044step0; decide +kernel
      have hl : raw1044step0Labels = labelEmbedding7 ∘ raw1044step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1044step0 raw1044step0Labels raw1044step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4294 node4294Labels := by rfl

def raw1045 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw1045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw1045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1045 raw1045Labels = mixedMoment B node872 node872Labels := by
  calc
    mixedMoment B raw1045 raw1045Labels = mixedMoment B raw1045step0 raw1045step0Labels := by
      have ha : raw1045step0 = (fun i j => raw1045 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1045step0 raw1045; decide +kernel
      have hl : raw1045step0Labels = raw1045Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1045 raw1045Labels permutation32 permutation4
    _ = mixedMoment B node872 node872Labels := by rfl

def raw1046 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw1046Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw1046step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw1046step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw1046step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1046 raw1046Labels = mixedMoment B node1562 node1562Labels := by
  calc
    mixedMoment B raw1046 raw1046Labels = mixedMoment B raw1046step0 raw1046step0Labels := by
      have ha : raw1046step0 = (fun i j => raw1046 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1046step0 raw1046; decide +kernel
      have hl : raw1046step0Labels = raw1046Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1046 raw1046Labels permutation34 permutation6
    mixedMoment B raw1046step0 raw1046step0Labels = mixedMoment B raw1046step1 raw1046step1Labels := by
      have ha : raw1046step1 = -raw1046step0 := by apply Matrix.ext; change ∀ i j, raw1046step1 i j = -(raw1046step0 i j); unfold raw1046step1 raw1046step0; decide +kernel
      have hl : raw1046step1Labels = raw1046step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1046step1 raw1046step1Labels = mixedMoment B raw1046step2 raw1046step2Labels := by
      have ha : raw1046step2 = raw1046step1 := by apply Matrix.ext; unfold raw1046step2 raw1046step1; decide +kernel
      have hl : raw1046step1Labels = labelEmbedding1 ∘ raw1046step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1046step1 raw1046step1Labels raw1046step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1562 node1562Labels := by rfl

def raw1047 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1047step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1047step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1047 raw1047Labels = mixedMoment B node4295 node4295Labels := by
  calc
    mixedMoment B raw1047 raw1047Labels = mixedMoment B raw1047step0 raw1047step0Labels := by
      have ha : raw1047step0 = (fun i j => raw1047 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1047step0 raw1047; decide +kernel
      have hl : raw1047step0Labels = raw1047Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1047 raw1047Labels permutation32 permutation4
    mixedMoment B raw1047step0 raw1047step0Labels = mixedMoment B raw1047step1 raw1047step1Labels := by
      have ha : raw1047step1 = raw1047step0 := by apply Matrix.ext; unfold raw1047step1 raw1047step0; decide +kernel
      have hl : raw1047step0Labels = labelEmbedding7 ∘ raw1047step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1047step0 raw1047step0Labels raw1047step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4295 node4295Labels := by rfl

def raw1048 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1048 raw1048Labels = mixedMoment B node873 node873Labels := by
  calc
    mixedMoment B raw1048 raw1048Labels = mixedMoment B raw1048step0 raw1048step0Labels := by
      have ha : raw1048step0 = (fun i j => raw1048 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1048step0 raw1048; decide +kernel
      have hl : raw1048step0Labels = raw1048Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1048 raw1048Labels permutation32 permutation4
    _ = mixedMoment B node873 node873Labels := by rfl

def raw1049 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1049Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw1049step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw1049step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1049step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw1049step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1049 raw1049Labels = mixedMoment B node1569 node1569Labels := by
  calc
    mixedMoment B raw1049 raw1049Labels = mixedMoment B raw1049step0 raw1049step0Labels := by
      have ha : raw1049step0 = (fun i j => raw1049 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1049step0 raw1049; decide +kernel
      have hl : raw1049step0Labels = raw1049Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1049 raw1049Labels permutation32 permutation6
    mixedMoment B raw1049step0 raw1049step0Labels = mixedMoment B raw1049step1 raw1049step1Labels := by
      have ha : raw1049step1 = -raw1049step0 := by apply Matrix.ext; change ∀ i j, raw1049step1 i j = -(raw1049step0 i j); unfold raw1049step1 raw1049step0; decide +kernel
      have hl : raw1049step1Labels = raw1049step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1049step1 raw1049step1Labels = mixedMoment B raw1049step2 raw1049step2Labels := by
      have ha : raw1049step2 = raw1049step1 := by apply Matrix.ext; unfold raw1049step2 raw1049step1; decide +kernel
      have hl : raw1049step1Labels = labelEmbedding1 ∘ raw1049step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1049step1 raw1049step1Labels raw1049step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1569 node1569Labels := by rfl

def raw1050 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1050step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1050step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1050 raw1050Labels = mixedMoment B node4296 node4296Labels := by
  calc
    mixedMoment B raw1050 raw1050Labels = mixedMoment B raw1050step0 raw1050step0Labels := by
      have ha : raw1050step0 = (fun i j => raw1050 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1050step0 raw1050; decide +kernel
      have hl : raw1050step0Labels = raw1050Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1050 raw1050Labels permutation32 permutation4
    mixedMoment B raw1050step0 raw1050step0Labels = mixedMoment B raw1050step1 raw1050step1Labels := by
      have ha : raw1050step1 = raw1050step0 := by apply Matrix.ext; unfold raw1050step1 raw1050step0; decide +kernel
      have hl : raw1050step0Labels = labelEmbedding7 ∘ raw1050step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1050step0 raw1050step0Labels raw1050step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4296 node4296Labels := by rfl

def raw1051 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1051Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1051step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1051 raw1051Labels = mixedMoment B node874 node874Labels := by
  calc
    mixedMoment B raw1051 raw1051Labels = mixedMoment B raw1051step0 raw1051step0Labels := by
      have ha : raw1051step0 = (fun i j => raw1051 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1051step0 raw1051; decide +kernel
      have hl : raw1051step0Labels = raw1051Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1051 raw1051Labels permutation32 permutation4
    _ = mixedMoment B node874 node874Labels := by rfl

def raw1052 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1052Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw1052step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw1052step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw1052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1052 raw1052Labels = mixedMoment B node1570 node1570Labels := by
  calc
    mixedMoment B raw1052 raw1052Labels = mixedMoment B raw1052step0 raw1052step0Labels := by
      have ha : raw1052step0 = (fun i j => raw1052 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1052step0 raw1052; decide +kernel
      have hl : raw1052step0Labels = raw1052Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1052 raw1052Labels permutation33 permutation6
    mixedMoment B raw1052step0 raw1052step0Labels = mixedMoment B raw1052step1 raw1052step1Labels := by
      have ha : raw1052step1 = -raw1052step0 := by apply Matrix.ext; change ∀ i j, raw1052step1 i j = -(raw1052step0 i j); unfold raw1052step1 raw1052step0; decide +kernel
      have hl : raw1052step1Labels = raw1052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1052step1 raw1052step1Labels = mixedMoment B raw1052step2 raw1052step2Labels := by
      have ha : raw1052step2 = raw1052step1 := by apply Matrix.ext; unfold raw1052step2 raw1052step1; decide +kernel
      have hl : raw1052step1Labels = labelEmbedding1 ∘ raw1052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1052step1 raw1052step1Labels raw1052step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1570 node1570Labels := by rfl

def raw1053 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw1053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1053step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1053step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1053step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1053 raw1053Labels = mixedMoment B node4297 node4297Labels := by
  calc
    mixedMoment B raw1053 raw1053Labels = mixedMoment B raw1053step0 raw1053step0Labels := by
      have ha : raw1053step0 = (fun i j => raw1053 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1053step0 raw1053; decide +kernel
      have hl : raw1053step0Labels = raw1053Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1053 raw1053Labels permutation152 permutation4
    mixedMoment B raw1053step0 raw1053step0Labels = mixedMoment B raw1053step1 raw1053step1Labels := by
      have ha : raw1053step1 = raw1053step0 := by apply Matrix.ext; unfold raw1053step1 raw1053step0; decide +kernel
      have hl : raw1053step0Labels = labelEmbedding7 ∘ raw1053step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1053step0 raw1053step0Labels raw1053step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4297 node4297Labels := by rfl

def raw1054 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw1054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1054 raw1054Labels = mixedMoment B node875 node875Labels := by
  calc
    mixedMoment B raw1054 raw1054Labels = mixedMoment B raw1054step0 raw1054step0Labels := by
      have ha : raw1054step0 = (fun i j => raw1054 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1054step0 raw1054; decide +kernel
      have hl : raw1054step0Labels = raw1054Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1054 raw1054Labels permutation152 permutation4
    _ = mixedMoment B node875 node875Labels := by rfl

def raw1055 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw1055Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw1055step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1055step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1055step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1055step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1055 raw1055Labels = mixedMoment B node1551 node1551Labels := by
  calc
    mixedMoment B raw1055 raw1055Labels = mixedMoment B raw1055step0 raw1055step0Labels := by
      have ha : raw1055step0 = (fun i j => raw1055 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1055step0 raw1055; decide +kernel
      have hl : raw1055step0Labels = raw1055Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1055 raw1055Labels permutation152 permutation6
    mixedMoment B raw1055step0 raw1055step0Labels = mixedMoment B raw1055step1 raw1055step1Labels := by
      have ha : raw1055step1 = -raw1055step0 := by apply Matrix.ext; change ∀ i j, raw1055step1 i j = -(raw1055step0 i j); unfold raw1055step1 raw1055step0; decide +kernel
      have hl : raw1055step1Labels = raw1055step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1055step1 raw1055step1Labels = mixedMoment B raw1055step2 raw1055step2Labels := by
      have ha : raw1055step2 = raw1055step1 := by apply Matrix.ext; unfold raw1055step2 raw1055step1; decide +kernel
      have hl : raw1055step1Labels = labelEmbedding1 ∘ raw1055step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1055step1 raw1055step1Labels raw1055step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1551 node1551Labels := by rfl

def raw1056 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1056step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1056step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1056step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1056 raw1056Labels = mixedMoment B node4298 node4298Labels := by
  calc
    mixedMoment B raw1056 raw1056Labels = mixedMoment B raw1056step0 raw1056step0Labels := by
      have ha : raw1056step0 = (fun i j => raw1056 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1056step0 raw1056; decide +kernel
      have hl : raw1056step0Labels = raw1056Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1056 raw1056Labels permutation152 permutation4
    mixedMoment B raw1056step0 raw1056step0Labels = mixedMoment B raw1056step1 raw1056step1Labels := by
      have ha : raw1056step1 = raw1056step0 := by apply Matrix.ext; unfold raw1056step1 raw1056step0; decide +kernel
      have hl : raw1056step0Labels = labelEmbedding7 ∘ raw1056step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1056step0 raw1056step0Labels raw1056step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4298 node4298Labels := by rfl

def raw1057 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1057 raw1057Labels = mixedMoment B node876 node876Labels := by
  calc
    mixedMoment B raw1057 raw1057Labels = mixedMoment B raw1057step0 raw1057step0Labels := by
      have ha : raw1057step0 = (fun i j => raw1057 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1057step0 raw1057; decide +kernel
      have hl : raw1057step0Labels = raw1057Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1057 raw1057Labels permutation152 permutation4
    _ = mixedMoment B node876 node876Labels := by rfl

def raw1058 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1058Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw1058step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1058step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1058step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1058step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1058 raw1058Labels = mixedMoment B node1552 node1552Labels := by
  calc
    mixedMoment B raw1058 raw1058Labels = mixedMoment B raw1058step0 raw1058step0Labels := by
      have ha : raw1058step0 = (fun i j => raw1058 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1058step0 raw1058; decide +kernel
      have hl : raw1058step0Labels = raw1058Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1058 raw1058Labels permutation152 permutation6
    mixedMoment B raw1058step0 raw1058step0Labels = mixedMoment B raw1058step1 raw1058step1Labels := by
      have ha : raw1058step1 = -raw1058step0 := by apply Matrix.ext; change ∀ i j, raw1058step1 i j = -(raw1058step0 i j); unfold raw1058step1 raw1058step0; decide +kernel
      have hl : raw1058step1Labels = raw1058step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1058step1 raw1058step1Labels = mixedMoment B raw1058step2 raw1058step2Labels := by
      have ha : raw1058step2 = raw1058step1 := by apply Matrix.ext; unfold raw1058step2 raw1058step1; decide +kernel
      have hl : raw1058step1Labels = labelEmbedding1 ∘ raw1058step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1058step1 raw1058step1Labels raw1058step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1552 node1552Labels := by rfl

def raw1059 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 3, -4]]
def raw1059Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw1059step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw1059step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1059 raw1059Labels = mixedMoment B node4299 node4299Labels := by
  calc
    mixedMoment B raw1059 raw1059Labels = mixedMoment B raw1059step0 raw1059step0Labels := by
      have ha : raw1059step0 = (fun i j => raw1059 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1059step0 raw1059; decide +kernel
      have hl : raw1059step0Labels = raw1059Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1059 raw1059Labels permutation32 permutation4
    mixedMoment B raw1059step0 raw1059step0Labels = mixedMoment B raw1059step1 raw1059step1Labels := by
      have ha : raw1059step1 = raw1059step0 := by apply Matrix.ext; unfold raw1059step1 raw1059step0; decide +kernel
      have hl : raw1059step0Labels = labelEmbedding7 ∘ raw1059step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1059step0 raw1059step0Labels raw1059step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4299 node4299Labels := by rfl

def raw1060 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 3, -4]]
def raw1060Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw1060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1060 raw1060Labels = mixedMoment B node877 node877Labels := by
  calc
    mixedMoment B raw1060 raw1060Labels = mixedMoment B raw1060step0 raw1060step0Labels := by
      have ha : raw1060step0 = (fun i j => raw1060 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1060step0 raw1060; decide +kernel
      have hl : raw1060step0Labels = raw1060Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1060 raw1060Labels permutation32 permutation4
    _ = mixedMoment B node877 node877Labels := by rfl

def raw1061 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 3, -4]]
def raw1061Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def raw1061step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def raw1061step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1061 raw1061Labels = mixedMoment B node968 node968Labels := by
  calc
    mixedMoment B raw1061 raw1061Labels = mixedMoment B raw1061step0 raw1061step0Labels := by
      have ha : raw1061step0 = (fun i j => raw1061 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1061step0 raw1061; decide +kernel
      have hl : raw1061step0Labels = raw1061Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1061 raw1061Labels permutation145 permutation6
    mixedMoment B raw1061step0 raw1061step0Labels = mixedMoment B raw1061step1 raw1061step1Labels := by
      have ha : raw1061step1 = raw1061step0 := by apply Matrix.ext; unfold raw1061step1 raw1061step0; decide +kernel
      have hl : raw1061step0Labels = labelEmbedding1 ∘ raw1061step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1061step0 raw1061step0Labels raw1061step1Labels labelEmbedding1 hl
    _ = mixedMoment B node968 node968Labels := by rfl

def raw1062 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1062step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1062step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1062step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1062 raw1062Labels = mixedMoment B node4301 node4301Labels := by
  calc
    mixedMoment B raw1062 raw1062Labels = mixedMoment B raw1062step0 raw1062step0Labels := by
      have ha : raw1062step0 = (fun i j => raw1062 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1062step0 raw1062; decide +kernel
      have hl : raw1062step0Labels = raw1062Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1062 raw1062Labels permutation152 permutation4
    mixedMoment B raw1062step0 raw1062step0Labels = mixedMoment B raw1062step1 raw1062step1Labels := by
      have ha : raw1062step1 = raw1062step0 := by apply Matrix.ext; unfold raw1062step1 raw1062step0; decide +kernel
      have hl : raw1062step0Labels = labelEmbedding7 ∘ raw1062step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1062step0 raw1062step0Labels raw1062step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4301 node4301Labels := by rfl

def raw1063 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1063step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1063 raw1063Labels = mixedMoment B node879 node879Labels := by
  calc
    mixedMoment B raw1063 raw1063Labels = mixedMoment B raw1063step0 raw1063step0Labels := by
      have ha : raw1063step0 = (fun i j => raw1063 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1063step0 raw1063; decide +kernel
      have hl : raw1063step0Labels = raw1063Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1063 raw1063Labels permutation152 permutation4
    _ = mixedMoment B node879 node879Labels := by rfl

def raw1064 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1064Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw1064step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1064step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1064step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1064step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1064step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1064 raw1064Labels = mixedMoment B node1556 node1556Labels := by
  calc
    mixedMoment B raw1064 raw1064Labels = mixedMoment B raw1064step0 raw1064step0Labels := by
      have ha : raw1064step0 = (fun i j => raw1064 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1064step0 raw1064; decide +kernel
      have hl : raw1064step0Labels = raw1064Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1064 raw1064Labels permutation153 permutation6
    mixedMoment B raw1064step0 raw1064step0Labels = mixedMoment B raw1064step1 raw1064step1Labels := by
      have ha : raw1064step1 = -raw1064step0 := by apply Matrix.ext; change ∀ i j, raw1064step1 i j = -(raw1064step0 i j); unfold raw1064step1 raw1064step0; decide +kernel
      have hl : raw1064step1Labels = raw1064step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1064step1 raw1064step1Labels = mixedMoment B raw1064step2 raw1064step2Labels := by
      have ha : raw1064step2 = raw1064step1 := by apply Matrix.ext; unfold raw1064step2 raw1064step1; decide +kernel
      have hl : raw1064step1Labels = labelEmbedding1 ∘ raw1064step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1064step1 raw1064step1Labels raw1064step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1556 node1556Labels := by rfl

def raw1065 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1065step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1065 raw1065Labels = mixedMoment B node4303 node4303Labels := by
  calc
    mixedMoment B raw1065 raw1065Labels = mixedMoment B raw1065step0 raw1065step0Labels := by
      have ha : raw1065step0 = (fun i j => raw1065 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1065step0 raw1065; decide +kernel
      have hl : raw1065step0Labels = raw1065Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1065 raw1065Labels permutation32 permutation4
    mixedMoment B raw1065step0 raw1065step0Labels = mixedMoment B raw1065step1 raw1065step1Labels := by
      have ha : raw1065step1 = raw1065step0 := by apply Matrix.ext; unfold raw1065step1 raw1065step0; decide +kernel
      have hl : raw1065step0Labels = labelEmbedding7 ∘ raw1065step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1065step0 raw1065step0Labels raw1065step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4303 node4303Labels := by rfl

def raw1066 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1066 raw1066Labels = mixedMoment B node881 node881Labels := by
  calc
    mixedMoment B raw1066 raw1066Labels = mixedMoment B raw1066step0 raw1066step0Labels := by
      have ha : raw1066step0 = (fun i j => raw1066 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1066step0 raw1066; decide +kernel
      have hl : raw1066step0Labels = raw1066Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1066 raw1066Labels permutation32 permutation4
    _ = mixedMoment B node881 node881Labels := by rfl

def raw1067 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1067Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw1067step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw1067step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1067step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw1067step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1067 raw1067Labels = mixedMoment B node1559 node1559Labels := by
  calc
    mixedMoment B raw1067 raw1067Labels = mixedMoment B raw1067step0 raw1067step0Labels := by
      have ha : raw1067step0 = (fun i j => raw1067 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1067step0 raw1067; decide +kernel
      have hl : raw1067step0Labels = raw1067Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1067 raw1067Labels permutation32 permutation6
    mixedMoment B raw1067step0 raw1067step0Labels = mixedMoment B raw1067step1 raw1067step1Labels := by
      have ha : raw1067step1 = -raw1067step0 := by apply Matrix.ext; change ∀ i j, raw1067step1 i j = -(raw1067step0 i j); unfold raw1067step1 raw1067step0; decide +kernel
      have hl : raw1067step1Labels = raw1067step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1067step1 raw1067step1Labels = mixedMoment B raw1067step2 raw1067step2Labels := by
      have ha : raw1067step2 = raw1067step1 := by apply Matrix.ext; unfold raw1067step2 raw1067step1; decide +kernel
      have hl : raw1067step1Labels = labelEmbedding1 ∘ raw1067step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1067step1 raw1067step1Labels raw1067step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1559 node1559Labels := by rfl

def raw1068 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1068step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1068step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1068 raw1068Labels = mixedMoment B node4304 node4304Labels := by
  calc
    mixedMoment B raw1068 raw1068Labels = mixedMoment B raw1068step0 raw1068step0Labels := by
      have ha : raw1068step0 = (fun i j => raw1068 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1068step0 raw1068; decide +kernel
      have hl : raw1068step0Labels = raw1068Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1068 raw1068Labels permutation32 permutation4
    mixedMoment B raw1068step0 raw1068step0Labels = mixedMoment B raw1068step1 raw1068step1Labels := by
      have ha : raw1068step1 = raw1068step0 := by apply Matrix.ext; unfold raw1068step1 raw1068step0; decide +kernel
      have hl : raw1068step0Labels = labelEmbedding7 ∘ raw1068step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1068step0 raw1068step0Labels raw1068step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4304 node4304Labels := by rfl

def raw1069 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1069step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1069 raw1069Labels = mixedMoment B node882 node882Labels := by
  calc
    mixedMoment B raw1069 raw1069Labels = mixedMoment B raw1069step0 raw1069step0Labels := by
      have ha : raw1069step0 = (fun i j => raw1069 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1069step0 raw1069; decide +kernel
      have hl : raw1069step0Labels = raw1069Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1069 raw1069Labels permutation32 permutation4
    _ = mixedMoment B node882 node882Labels := by rfl

def raw1070 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1070Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 1, 2]]
def raw1070step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw1070step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw1070step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1070 raw1070Labels = mixedMoment B node1558 node1558Labels := by
  calc
    mixedMoment B raw1070 raw1070Labels = mixedMoment B raw1070step0 raw1070step0Labels := by
      have ha : raw1070step0 = (fun i j => raw1070 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1070step0 raw1070; decide +kernel
      have hl : raw1070step0Labels = raw1070Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1070 raw1070Labels permutation32 permutation6
    mixedMoment B raw1070step0 raw1070step0Labels = mixedMoment B raw1070step1 raw1070step1Labels := by
      have ha : raw1070step1 = -raw1070step0 := by apply Matrix.ext; change ∀ i j, raw1070step1 i j = -(raw1070step0 i j); unfold raw1070step1 raw1070step0; decide +kernel
      have hl : raw1070step1Labels = raw1070step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1070step1 raw1070step1Labels = mixedMoment B raw1070step2 raw1070step2Labels := by
      have ha : raw1070step2 = raw1070step1 := by apply Matrix.ext; unfold raw1070step2 raw1070step1; decide +kernel
      have hl : raw1070step1Labels = labelEmbedding1 ∘ raw1070step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1070step1 raw1070step1Labels raw1070step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1558 node1558Labels := by rfl

def raw1071 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1071step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1071 raw1071Labels = mixedMoment B node4307 node4307Labels := by
  calc
    mixedMoment B raw1071 raw1071Labels = mixedMoment B raw1071step0 raw1071step0Labels := by
      have ha : raw1071step0 = (fun i j => raw1071 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1071step0 raw1071; decide +kernel
      have hl : raw1071step0Labels = raw1071Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1071 raw1071Labels permutation152 permutation4
    mixedMoment B raw1071step0 raw1071step0Labels = mixedMoment B raw1071step1 raw1071step1Labels := by
      have ha : raw1071step1 = raw1071step0 := by apply Matrix.ext; unfold raw1071step1 raw1071step0; decide +kernel
      have hl : raw1071step0Labels = labelEmbedding7 ∘ raw1071step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1071step0 raw1071step0Labels raw1071step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4307 node4307Labels := by rfl

def raw1072 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1072 raw1072Labels = mixedMoment B node885 node885Labels := by
  calc
    mixedMoment B raw1072 raw1072Labels = mixedMoment B raw1072step0 raw1072step0Labels := by
      have ha : raw1072step0 = (fun i j => raw1072 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1072step0 raw1072; decide +kernel
      have hl : raw1072step0Labels = raw1072Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1072 raw1072Labels permutation152 permutation4
    _ = mixedMoment B node885 node885Labels := by rfl

def raw1073 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1073Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw1073step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1073step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1073step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1073 raw1073Labels = mixedMoment B node1563 node1563Labels := by
  calc
    mixedMoment B raw1073 raw1073Labels = mixedMoment B raw1073step0 raw1073step0Labels := by
      have ha : raw1073step0 = (fun i j => raw1073 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1073step0 raw1073; decide +kernel
      have hl : raw1073step0Labels = raw1073Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1073 raw1073Labels permutation170 permutation6
    mixedMoment B raw1073step0 raw1073step0Labels = mixedMoment B raw1073step1 raw1073step1Labels := by
      have ha : raw1073step1 = -raw1073step0 := by apply Matrix.ext; change ∀ i j, raw1073step1 i j = -(raw1073step0 i j); unfold raw1073step1 raw1073step0; decide +kernel
      have hl : raw1073step1Labels = raw1073step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1073step1 raw1073step1Labels = mixedMoment B raw1073step2 raw1073step2Labels := by
      have ha : raw1073step2 = raw1073step1 := by apply Matrix.ext; unfold raw1073step2 raw1073step1; decide +kernel
      have hl : raw1073step1Labels = labelEmbedding1 ∘ raw1073step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1073step1 raw1073step1Labels raw1073step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1563 node1563Labels := by rfl

def raw1074 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1074step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1074step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1074 raw1074Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw1074 raw1074Labels = mixedMoment B raw1074step0 raw1074step0Labels := by
      have ha : raw1074step0 = (fun i j => raw1074 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1074step0 raw1074; decide +kernel
      have hl : raw1074step0Labels = raw1074Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1074 raw1074Labels permutation32 permutation4
    mixedMoment B raw1074step0 raw1074step0Labels = mixedMoment B raw1074step1 raw1074step1Labels := by
      have ha : raw1074step1 = raw1074step0 := by apply Matrix.ext; unfold raw1074step1 raw1074step0; decide +kernel
      have hl : raw1074step0Labels = labelEmbedding7 ∘ raw1074step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1074step0 raw1074step0Labels raw1074step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

def raw1075 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1075 raw1075Labels = mixedMoment B node887 node887Labels := by
  calc
    mixedMoment B raw1075 raw1075Labels = mixedMoment B raw1075step0 raw1075step0Labels := by
      have ha : raw1075step0 = (fun i j => raw1075 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1075step0 raw1075; decide +kernel
      have hl : raw1075step0Labels = raw1075Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1075 raw1075Labels permutation32 permutation4
    _ = mixedMoment B node887 node887Labels := by rfl

def raw1076 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1076Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw1076step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw1076step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1076step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw1076step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1076 raw1076Labels = mixedMoment B node1573 node1573Labels := by
  calc
    mixedMoment B raw1076 raw1076Labels = mixedMoment B raw1076step0 raw1076step0Labels := by
      have ha : raw1076step0 = (fun i j => raw1076 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1076step0 raw1076; decide +kernel
      have hl : raw1076step0Labels = raw1076Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1076 raw1076Labels permutation33 permutation6
    mixedMoment B raw1076step0 raw1076step0Labels = mixedMoment B raw1076step1 raw1076step1Labels := by
      have ha : raw1076step1 = -raw1076step0 := by apply Matrix.ext; change ∀ i j, raw1076step1 i j = -(raw1076step0 i j); unfold raw1076step1 raw1076step0; decide +kernel
      have hl : raw1076step1Labels = raw1076step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1076step1 raw1076step1Labels = mixedMoment B raw1076step2 raw1076step2Labels := by
      have ha : raw1076step2 = raw1076step1 := by apply Matrix.ext; unfold raw1076step2 raw1076step1; decide +kernel
      have hl : raw1076step1Labels = labelEmbedding1 ∘ raw1076step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1076step1 raw1076step1Labels raw1076step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1573 node1573Labels := by rfl

def raw1077 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1077step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1077step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1077 raw1077Labels = mixedMoment B node4310 node4310Labels := by
  calc
    mixedMoment B raw1077 raw1077Labels = mixedMoment B raw1077step0 raw1077step0Labels := by
      have ha : raw1077step0 = (fun i j => raw1077 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1077step0 raw1077; decide +kernel
      have hl : raw1077step0Labels = raw1077Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1077 raw1077Labels permutation32 permutation4
    mixedMoment B raw1077step0 raw1077step0Labels = mixedMoment B raw1077step1 raw1077step1Labels := by
      have ha : raw1077step1 = raw1077step0 := by apply Matrix.ext; unfold raw1077step1 raw1077step0; decide +kernel
      have hl : raw1077step0Labels = labelEmbedding7 ∘ raw1077step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1077step0 raw1077step0Labels raw1077step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4310 node4310Labels := by rfl

def raw1078 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1078Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1078 raw1078Labels = mixedMoment B node888 node888Labels := by
  calc
    mixedMoment B raw1078 raw1078Labels = mixedMoment B raw1078step0 raw1078step0Labels := by
      have ha : raw1078step0 = (fun i j => raw1078 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1078step0 raw1078; decide +kernel
      have hl : raw1078step0Labels = raw1078Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1078 raw1078Labels permutation32 permutation4
    _ = mixedMoment B node888 node888Labels := by rfl

def raw1079 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1079Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 1, 2]]
def raw1079step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw1079step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1079step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw1079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1079 raw1079Labels = mixedMoment B node1564 node1564Labels := by
  calc
    mixedMoment B raw1079 raw1079Labels = mixedMoment B raw1079step0 raw1079step0Labels := by
      have ha : raw1079step0 = (fun i j => raw1079 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1079step0 raw1079; decide +kernel
      have hl : raw1079step0Labels = raw1079Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1079 raw1079Labels permutation34 permutation6
    mixedMoment B raw1079step0 raw1079step0Labels = mixedMoment B raw1079step1 raw1079step1Labels := by
      have ha : raw1079step1 = -raw1079step0 := by apply Matrix.ext; change ∀ i j, raw1079step1 i j = -(raw1079step0 i j); unfold raw1079step1 raw1079step0; decide +kernel
      have hl : raw1079step1Labels = raw1079step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1079step1 raw1079step1Labels = mixedMoment B raw1079step2 raw1079step2Labels := by
      have ha : raw1079step2 = raw1079step1 := by apply Matrix.ext; unfold raw1079step2 raw1079step1; decide +kernel
      have hl : raw1079step1Labels = labelEmbedding1 ∘ raw1079step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1079step1 raw1079step1Labels raw1079step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1564 node1564Labels := by rfl

def raw1080 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1080step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1080step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1080 raw1080Labels = mixedMoment B node4313 node4313Labels := by
  calc
    mixedMoment B raw1080 raw1080Labels = mixedMoment B raw1080step0 raw1080step0Labels := by
      have ha : raw1080step0 = (fun i j => raw1080 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1080step0 raw1080; decide +kernel
      have hl : raw1080step0Labels = raw1080Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1080 raw1080Labels permutation32 permutation4
    mixedMoment B raw1080step0 raw1080step0Labels = mixedMoment B raw1080step1 raw1080step1Labels := by
      have ha : raw1080step1 = raw1080step0 := by apply Matrix.ext; unfold raw1080step1 raw1080step0; decide +kernel
      have hl : raw1080step0Labels = labelEmbedding7 ∘ raw1080step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1080step0 raw1080step0Labels raw1080step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4313 node4313Labels := by rfl

def raw1081 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1081 raw1081Labels = mixedMoment B node891 node891Labels := by
  calc
    mixedMoment B raw1081 raw1081Labels = mixedMoment B raw1081step0 raw1081step0Labels := by
      have ha : raw1081step0 = (fun i j => raw1081 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1081step0 raw1081; decide +kernel
      have hl : raw1081step0Labels = raw1081Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1081 raw1081Labels permutation32 permutation4
    _ = mixedMoment B node891 node891Labels := by rfl

def raw1082 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1082Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw1082step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw1082step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw1082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1082 raw1082Labels = mixedMoment B node1565 node1565Labels := by
  calc
    mixedMoment B raw1082 raw1082Labels = mixedMoment B raw1082step0 raw1082step0Labels := by
      have ha : raw1082step0 = (fun i j => raw1082 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1082step0 raw1082; decide +kernel
      have hl : raw1082step0Labels = raw1082Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1082 raw1082Labels permutation34 permutation6
    mixedMoment B raw1082step0 raw1082step0Labels = mixedMoment B raw1082step1 raw1082step1Labels := by
      have ha : raw1082step1 = -raw1082step0 := by apply Matrix.ext; change ∀ i j, raw1082step1 i j = -(raw1082step0 i j); unfold raw1082step1 raw1082step0; decide +kernel
      have hl : raw1082step1Labels = raw1082step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1082step1 raw1082step1Labels = mixedMoment B raw1082step2 raw1082step2Labels := by
      have ha : raw1082step2 = raw1082step1 := by apply Matrix.ext; unfold raw1082step2 raw1082step1; decide +kernel
      have hl : raw1082step1Labels = labelEmbedding1 ∘ raw1082step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1082step1 raw1082step1Labels raw1082step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1565 node1565Labels := by rfl

def raw1083 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1083step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1083 raw1083Labels = mixedMoment B node4314 node4314Labels := by
  calc
    mixedMoment B raw1083 raw1083Labels = mixedMoment B raw1083step0 raw1083step0Labels := by
      have ha : raw1083step0 = (fun i j => raw1083 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1083step0 raw1083; decide +kernel
      have hl : raw1083step0Labels = raw1083Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1083 raw1083Labels permutation32 permutation4
    mixedMoment B raw1083step0 raw1083step0Labels = mixedMoment B raw1083step1 raw1083step1Labels := by
      have ha : raw1083step1 = raw1083step0 := by apply Matrix.ext; unfold raw1083step1 raw1083step0; decide +kernel
      have hl : raw1083step0Labels = labelEmbedding7 ∘ raw1083step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1083step0 raw1083step0Labels raw1083step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4314 node4314Labels := by rfl

def raw1084 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1084Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1084step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1084 raw1084Labels = mixedMoment B node892 node892Labels := by
  calc
    mixedMoment B raw1084 raw1084Labels = mixedMoment B raw1084step0 raw1084step0Labels := by
      have ha : raw1084step0 = (fun i j => raw1084 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1084step0 raw1084; decide +kernel
      have hl : raw1084step0Labels = raw1084Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1084 raw1084Labels permutation32 permutation4
    _ = mixedMoment B node892 node892Labels := by rfl

def raw1085 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1085Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw1085step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw1085step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1085step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw1085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1085 raw1085Labels = mixedMoment B node1575 node1575Labels := by
  calc
    mixedMoment B raw1085 raw1085Labels = mixedMoment B raw1085step0 raw1085step0Labels := by
      have ha : raw1085step0 = (fun i j => raw1085 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1085step0 raw1085; decide +kernel
      have hl : raw1085step0Labels = raw1085Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1085 raw1085Labels permutation35 permutation6
    mixedMoment B raw1085step0 raw1085step0Labels = mixedMoment B raw1085step1 raw1085step1Labels := by
      have ha : raw1085step1 = -raw1085step0 := by apply Matrix.ext; change ∀ i j, raw1085step1 i j = -(raw1085step0 i j); unfold raw1085step1 raw1085step0; decide +kernel
      have hl : raw1085step1Labels = raw1085step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1085step1 raw1085step1Labels = mixedMoment B raw1085step2 raw1085step2Labels := by
      have ha : raw1085step2 = raw1085step1 := by apply Matrix.ext; unfold raw1085step2 raw1085step1; decide +kernel
      have hl : raw1085step1Labels = labelEmbedding1 ∘ raw1085step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1085step1 raw1085step1Labels raw1085step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1575 node1575Labels := by rfl

def raw1086 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 1, -2], ![-2, 4, -2]]
def raw1086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1086step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw1086step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1086step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw1086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1086 raw1086Labels = mixedMoment B node4315 node4315Labels := by
  calc
    mixedMoment B raw1086 raw1086Labels = mixedMoment B raw1086step0 raw1086step0Labels := by
      have ha : raw1086step0 = (fun i j => raw1086 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1086step0 raw1086; decide +kernel
      have hl : raw1086step0Labels = raw1086Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1086 raw1086Labels permutation8 permutation4
    mixedMoment B raw1086step0 raw1086step0Labels = mixedMoment B raw1086step1 raw1086step1Labels := by
      have ha : raw1086step1 = raw1086step0 := by apply Matrix.ext; unfold raw1086step1 raw1086step0; decide +kernel
      have hl : raw1086step0Labels = labelEmbedding7 ∘ raw1086step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1086step0 raw1086step0Labels raw1086step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4315 node4315Labels := by rfl

def raw1087 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 1, -2], ![-2, 4, -2]]
def raw1087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1087step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw1087step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1087 raw1087Labels = mixedMoment B node893 node893Labels := by
  calc
    mixedMoment B raw1087 raw1087Labels = mixedMoment B raw1087step0 raw1087step0Labels := by
      have ha : raw1087step0 = (fun i j => raw1087 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1087step0 raw1087; decide +kernel
      have hl : raw1087step0Labels = raw1087Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1087 raw1087Labels permutation8 permutation4
    _ = mixedMoment B node893 node893Labels := by rfl

def raw1088 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 1, -2], ![-2, 4, -2]]
def raw1088Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1088step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-2, 1, 1], ![-2, -2, 4]]
def raw1088step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![2, -1, -1], ![2, 2, -4]]
def raw1088step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1088step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![2, -1, -1], ![2, 2, -4]]
def raw1088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1088 raw1088Labels = mixedMoment B node1578 node1578Labels := by
  calc
    mixedMoment B raw1088 raw1088Labels = mixedMoment B raw1088step0 raw1088step0Labels := by
      have ha : raw1088step0 = (fun i j => raw1088 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1088step0 raw1088; decide +kernel
      have hl : raw1088step0Labels = raw1088Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1088 raw1088Labels permutation8 permutation6
    mixedMoment B raw1088step0 raw1088step0Labels = mixedMoment B raw1088step1 raw1088step1Labels := by
      have ha : raw1088step1 = -raw1088step0 := by apply Matrix.ext; change ∀ i j, raw1088step1 i j = -(raw1088step0 i j); unfold raw1088step1 raw1088step0; decide +kernel
      have hl : raw1088step1Labels = raw1088step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1088step1 raw1088step1Labels = mixedMoment B raw1088step2 raw1088step2Labels := by
      have ha : raw1088step2 = raw1088step1 := by apply Matrix.ext; unfold raw1088step2 raw1088step1; decide +kernel
      have hl : raw1088step1Labels = labelEmbedding1 ∘ raw1088step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1088step1 raw1088step1Labels raw1088step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1578 node1578Labels := by rfl

def raw1089 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-2, 2, 0], ![1, 3, -4]]
def raw1089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1089step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def raw1089step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def raw1089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1089 raw1089Labels = mixedMoment B node4316 node4316Labels := by
  calc
    mixedMoment B raw1089 raw1089Labels = mixedMoment B raw1089step0 raw1089step0Labels := by
      have ha : raw1089step0 = (fun i j => raw1089 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1089step0 raw1089; decide +kernel
      have hl : raw1089step0Labels = raw1089Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1089 raw1089Labels permutation8 permutation4
    mixedMoment B raw1089step0 raw1089step0Labels = mixedMoment B raw1089step1 raw1089step1Labels := by
      have ha : raw1089step1 = raw1089step0 := by apply Matrix.ext; unfold raw1089step1 raw1089step0; decide +kernel
      have hl : raw1089step0Labels = labelEmbedding7 ∘ raw1089step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1089step0 raw1089step0Labels raw1089step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4316 node4316Labels := by rfl

def raw1090 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-2, 2, 0], ![1, 3, -4]]
def raw1090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1090step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def raw1090step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1090 raw1090Labels = mixedMoment B node894 node894Labels := by
  calc
    mixedMoment B raw1090 raw1090Labels = mixedMoment B raw1090step0 raw1090step0Labels := by
      have ha : raw1090step0 = (fun i j => raw1090 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1090step0 raw1090; decide +kernel
      have hl : raw1090step0Labels = raw1090Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1090 raw1090Labels permutation8 permutation4
    _ = mixedMoment B node894 node894Labels := by rfl

def raw1091 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![-2, 2, 0], ![1, 3, -4]]
def raw1091Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1091step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![3, 1, -4]]
def raw1091step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![3, 1, -4]]
def raw1091step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1091 raw1091Labels = mixedMoment B node961 node961Labels := by
  calc
    mixedMoment B raw1091 raw1091Labels = mixedMoment B raw1091step0 raw1091step0Labels := by
      have ha : raw1091step0 = (fun i j => raw1091 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1091step0 raw1091; decide +kernel
      have hl : raw1091step0Labels = raw1091Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1091 raw1091Labels permutation31 permutation6
    mixedMoment B raw1091step0 raw1091step0Labels = mixedMoment B raw1091step1 raw1091step1Labels := by
      have ha : raw1091step1 = raw1091step0 := by apply Matrix.ext; unfold raw1091step1 raw1091step0; decide +kernel
      have hl : raw1091step0Labels = labelEmbedding1 ∘ raw1091step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1091step0 raw1091step0Labels raw1091step1Labels labelEmbedding1 hl
    _ = mixedMoment B node961 node961Labels := by rfl

def raw1092 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 2, -3], ![-2, 3, -1]]
def raw1092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1092step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw1092step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw1092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1092 raw1092Labels = mixedMoment B node4319 node4319Labels := by
  calc
    mixedMoment B raw1092 raw1092Labels = mixedMoment B raw1092step0 raw1092step0Labels := by
      have ha : raw1092step0 = (fun i j => raw1092 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1092step0 raw1092; decide +kernel
      have hl : raw1092step0Labels = raw1092Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1092 raw1092Labels permutation8 permutation4
    mixedMoment B raw1092step0 raw1092step0Labels = mixedMoment B raw1092step1 raw1092step1Labels := by
      have ha : raw1092step1 = raw1092step0 := by apply Matrix.ext; unfold raw1092step1 raw1092step0; decide +kernel
      have hl : raw1092step0Labels = labelEmbedding7 ∘ raw1092step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1092step0 raw1092step0Labels raw1092step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4319 node4319Labels := by rfl

def raw1093 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 2, -3], ![-2, 3, -1]]
def raw1093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1093step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw1093step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1093 raw1093Labels = mixedMoment B node897 node897Labels := by
  calc
    mixedMoment B raw1093 raw1093Labels = mixedMoment B raw1093step0 raw1093step0Labels := by
      have ha : raw1093step0 = (fun i j => raw1093 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1093step0 raw1093; decide +kernel
      have hl : raw1093step0Labels = raw1093Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1093 raw1093Labels permutation8 permutation4
    _ = mixedMoment B node897 node897Labels := by rfl

def raw1094 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 2, -3], ![-2, 3, -1]]
def raw1094Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1094step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, -2, 3], ![-3, 1, 2]]
def raw1094step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 2, -3], ![3, -1, -2]]
def raw1094step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1094step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 2, -3], ![3, -1, -2]]
def raw1094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1094 raw1094Labels = mixedMoment B node1577 node1577Labels := by
  calc
    mixedMoment B raw1094 raw1094Labels = mixedMoment B raw1094step0 raw1094step0Labels := by
      have ha : raw1094step0 = (fun i j => raw1094 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1094step0 raw1094; decide +kernel
      have hl : raw1094step0Labels = raw1094Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1094 raw1094Labels permutation9 permutation6
    mixedMoment B raw1094step0 raw1094step0Labels = mixedMoment B raw1094step1 raw1094step1Labels := by
      have ha : raw1094step1 = -raw1094step0 := by apply Matrix.ext; change ∀ i j, raw1094step1 i j = -(raw1094step0 i j); unfold raw1094step1 raw1094step0; decide +kernel
      have hl : raw1094step1Labels = raw1094step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1094step1 raw1094step1Labels = mixedMoment B raw1094step2 raw1094step2Labels := by
      have ha : raw1094step2 = raw1094step1 := by apply Matrix.ext; unfold raw1094step2 raw1094step1; decide +kernel
      have hl : raw1094step1Labels = labelEmbedding1 ∘ raw1094step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1094step1 raw1094step1Labels raw1094step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1577 node1577Labels := by rfl

def raw1095 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1095step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1095 raw1095Labels = mixedMoment B node4320 node4320Labels := by
  calc
    mixedMoment B raw1095 raw1095Labels = mixedMoment B raw1095step0 raw1095step0Labels := by
      have ha : raw1095step0 = (fun i j => raw1095 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1095step0 raw1095; decide +kernel
      have hl : raw1095step0Labels = raw1095Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1095 raw1095Labels permutation152 permutation4
    mixedMoment B raw1095step0 raw1095step0Labels = mixedMoment B raw1095step1 raw1095step1Labels := by
      have ha : raw1095step1 = raw1095step0 := by apply Matrix.ext; unfold raw1095step1 raw1095step0; decide +kernel
      have hl : raw1095step0Labels = labelEmbedding7 ∘ raw1095step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1095step0 raw1095step0Labels raw1095step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4320 node4320Labels := by rfl

def raw1096 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1096 raw1096Labels = mixedMoment B node898 node898Labels := by
  calc
    mixedMoment B raw1096 raw1096Labels = mixedMoment B raw1096step0 raw1096step0Labels := by
      have ha : raw1096step0 = (fun i j => raw1096 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1096step0 raw1096; decide +kernel
      have hl : raw1096step0Labels = raw1096Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1096 raw1096Labels permutation152 permutation4
    _ = mixedMoment B node898 node898Labels := by rfl

def raw1097 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1097Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw1097step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw1097step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1097step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw1097step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1097 raw1097Labels = mixedMoment B node1586 node1586Labels := by
  calc
    mixedMoment B raw1097 raw1097Labels = mixedMoment B raw1097step0 raw1097step0Labels := by
      have ha : raw1097step0 = (fun i j => raw1097 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1097step0 raw1097; decide +kernel
      have hl : raw1097step0Labels = raw1097Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1097 raw1097Labels permutation176 permutation6
    mixedMoment B raw1097step0 raw1097step0Labels = mixedMoment B raw1097step1 raw1097step1Labels := by
      have ha : raw1097step1 = -raw1097step0 := by apply Matrix.ext; change ∀ i j, raw1097step1 i j = -(raw1097step0 i j); unfold raw1097step1 raw1097step0; decide +kernel
      have hl : raw1097step1Labels = raw1097step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1097step1 raw1097step1Labels = mixedMoment B raw1097step2 raw1097step2Labels := by
      have ha : raw1097step2 = raw1097step1 := by apply Matrix.ext; unfold raw1097step2 raw1097step1; decide +kernel
      have hl : raw1097step1Labels = labelEmbedding1 ∘ raw1097step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1097step1 raw1097step1Labels raw1097step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1586 node1586Labels := by rfl

def raw1098 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1098step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1098step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1098 raw1098Labels = mixedMoment B node4321 node4321Labels := by
  calc
    mixedMoment B raw1098 raw1098Labels = mixedMoment B raw1098step0 raw1098step0Labels := by
      have ha : raw1098step0 = (fun i j => raw1098 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1098step0 raw1098; decide +kernel
      have hl : raw1098step0Labels = raw1098Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1098 raw1098Labels permutation152 permutation4
    mixedMoment B raw1098step0 raw1098step0Labels = mixedMoment B raw1098step1 raw1098step1Labels := by
      have ha : raw1098step1 = raw1098step0 := by apply Matrix.ext; unfold raw1098step1 raw1098step0; decide +kernel
      have hl : raw1098step0Labels = labelEmbedding7 ∘ raw1098step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1098step0 raw1098step0Labels raw1098step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4321 node4321Labels := by rfl

def raw1099 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1099 raw1099Labels = mixedMoment B node899 node899Labels := by
  calc
    mixedMoment B raw1099 raw1099Labels = mixedMoment B raw1099step0 raw1099step0Labels := by
      have ha : raw1099step0 = (fun i j => raw1099 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1099step0 raw1099; decide +kernel
      have hl : raw1099step0Labels = raw1099Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1099 raw1099Labels permutation152 permutation4
    _ = mixedMoment B node899 node899Labels := by rfl

def raw1100 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1100Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw1100step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1100step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1100step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1100 raw1100Labels = mixedMoment B node1587 node1587Labels := by
  calc
    mixedMoment B raw1100 raw1100Labels = mixedMoment B raw1100step0 raw1100step0Labels := by
      have ha : raw1100step0 = (fun i j => raw1100 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1100step0 raw1100; decide +kernel
      have hl : raw1100step0Labels = raw1100Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1100 raw1100Labels permutation176 permutation6
    mixedMoment B raw1100step0 raw1100step0Labels = mixedMoment B raw1100step1 raw1100step1Labels := by
      have ha : raw1100step1 = -raw1100step0 := by apply Matrix.ext; change ∀ i j, raw1100step1 i j = -(raw1100step0 i j); unfold raw1100step1 raw1100step0; decide +kernel
      have hl : raw1100step1Labels = raw1100step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1100step1 raw1100step1Labels = mixedMoment B raw1100step2 raw1100step2Labels := by
      have ha : raw1100step2 = raw1100step1 := by apply Matrix.ext; unfold raw1100step2 raw1100step1; decide +kernel
      have hl : raw1100step1Labels = labelEmbedding1 ∘ raw1100step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1100step1 raw1100step1Labels raw1100step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1587 node1587Labels := by rfl

def raw1101 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1101step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1101step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1101step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1101 raw1101Labels = mixedMoment B node4322 node4322Labels := by
  calc
    mixedMoment B raw1101 raw1101Labels = mixedMoment B raw1101step0 raw1101step0Labels := by
      have ha : raw1101step0 = (fun i j => raw1101 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1101step0 raw1101; decide +kernel
      have hl : raw1101step0Labels = raw1101Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1101 raw1101Labels permutation152 permutation4
    mixedMoment B raw1101step0 raw1101step0Labels = mixedMoment B raw1101step1 raw1101step1Labels := by
      have ha : raw1101step1 = raw1101step0 := by apply Matrix.ext; unfold raw1101step1 raw1101step0; decide +kernel
      have hl : raw1101step0Labels = labelEmbedding7 ∘ raw1101step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1101step0 raw1101step0Labels raw1101step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4322 node4322Labels := by rfl

def raw1102 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1102step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1102 raw1102Labels = mixedMoment B node900 node900Labels := by
  calc
    mixedMoment B raw1102 raw1102Labels = mixedMoment B raw1102step0 raw1102step0Labels := by
      have ha : raw1102step0 = (fun i j => raw1102 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1102step0 raw1102; decide +kernel
      have hl : raw1102step0Labels = raw1102Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1102 raw1102Labels permutation152 permutation4
    _ = mixedMoment B node900 node900Labels := by rfl

def raw1103 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1103Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1103step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1103step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1103step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1103step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1103step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1103 raw1103Labels = mixedMoment B node1588 node1588Labels := by
  calc
    mixedMoment B raw1103 raw1103Labels = mixedMoment B raw1103step0 raw1103step0Labels := by
      have ha : raw1103step0 = (fun i j => raw1103 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1103step0 raw1103; decide +kernel
      have hl : raw1103step0Labels = raw1103Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1103 raw1103Labels permutation176 permutation6
    mixedMoment B raw1103step0 raw1103step0Labels = mixedMoment B raw1103step1 raw1103step1Labels := by
      have ha : raw1103step1 = -raw1103step0 := by apply Matrix.ext; change ∀ i j, raw1103step1 i j = -(raw1103step0 i j); unfold raw1103step1 raw1103step0; decide +kernel
      have hl : raw1103step1Labels = raw1103step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1103step1 raw1103step1Labels = mixedMoment B raw1103step2 raw1103step2Labels := by
      have ha : raw1103step2 = raw1103step1 := by apply Matrix.ext; unfold raw1103step2 raw1103step1; decide +kernel
      have hl : raw1103step1Labels = labelEmbedding1 ∘ raw1103step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1103step1 raw1103step1Labels raw1103step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1588 node1588Labels := by rfl

def raw1104 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1104step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1104step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1104 raw1104Labels = mixedMoment B node4323 node4323Labels := by
  calc
    mixedMoment B raw1104 raw1104Labels = mixedMoment B raw1104step0 raw1104step0Labels := by
      have ha : raw1104step0 = (fun i j => raw1104 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1104step0 raw1104; decide +kernel
      have hl : raw1104step0Labels = raw1104Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1104 raw1104Labels permutation152 permutation4
    mixedMoment B raw1104step0 raw1104step0Labels = mixedMoment B raw1104step1 raw1104step1Labels := by
      have ha : raw1104step1 = raw1104step0 := by apply Matrix.ext; unfold raw1104step1 raw1104step0; decide +kernel
      have hl : raw1104step0Labels = labelEmbedding7 ∘ raw1104step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1104step0 raw1104step0Labels raw1104step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4323 node4323Labels := by rfl

def raw1105 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1105step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1105 raw1105Labels = mixedMoment B node901 node901Labels := by
  calc
    mixedMoment B raw1105 raw1105Labels = mixedMoment B raw1105step0 raw1105step0Labels := by
      have ha : raw1105step0 = (fun i j => raw1105 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1105step0 raw1105; decide +kernel
      have hl : raw1105step0Labels = raw1105Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1105 raw1105Labels permutation152 permutation4
    _ = mixedMoment B node901 node901Labels := by rfl

def raw1106 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1106Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1106step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1106step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1106step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1106step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1106step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1106 raw1106Labels = mixedMoment B node1589 node1589Labels := by
  calc
    mixedMoment B raw1106 raw1106Labels = mixedMoment B raw1106step0 raw1106step0Labels := by
      have ha : raw1106step0 = (fun i j => raw1106 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1106step0 raw1106; decide +kernel
      have hl : raw1106step0Labels = raw1106Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1106 raw1106Labels permutation176 permutation6
    mixedMoment B raw1106step0 raw1106step0Labels = mixedMoment B raw1106step1 raw1106step1Labels := by
      have ha : raw1106step1 = -raw1106step0 := by apply Matrix.ext; change ∀ i j, raw1106step1 i j = -(raw1106step0 i j); unfold raw1106step1 raw1106step0; decide +kernel
      have hl : raw1106step1Labels = raw1106step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1106step1 raw1106step1Labels = mixedMoment B raw1106step2 raw1106step2Labels := by
      have ha : raw1106step2 = raw1106step1 := by apply Matrix.ext; unfold raw1106step2 raw1106step1; decide +kernel
      have hl : raw1106step1Labels = labelEmbedding1 ∘ raw1106step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1106step1 raw1106step1Labels raw1106step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1589 node1589Labels := by rfl

def raw1107 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, 3, -3]]
def raw1107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw1107step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw1107step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1107 raw1107Labels = mixedMoment B node4324 node4324Labels := by
  calc
    mixedMoment B raw1107 raw1107Labels = mixedMoment B raw1107step0 raw1107step0Labels := by
      have ha : raw1107step0 = (fun i j => raw1107 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1107step0 raw1107; decide +kernel
      have hl : raw1107step0Labels = raw1107Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1107 raw1107Labels permutation32 permutation4
    mixedMoment B raw1107step0 raw1107step0Labels = mixedMoment B raw1107step1 raw1107step1Labels := by
      have ha : raw1107step1 = raw1107step0 := by apply Matrix.ext; unfold raw1107step1 raw1107step0; decide +kernel
      have hl : raw1107step0Labels = labelEmbedding7 ∘ raw1107step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1107step0 raw1107step0Labels raw1107step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4324 node4324Labels := by rfl

def raw1108 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, 3, -3]]
def raw1108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw1108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1108 raw1108Labels = mixedMoment B node902 node902Labels := by
  calc
    mixedMoment B raw1108 raw1108Labels = mixedMoment B raw1108step0 raw1108step0Labels := by
      have ha : raw1108step0 = (fun i j => raw1108 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1108step0 raw1108; decide +kernel
      have hl : raw1108step0Labels = raw1108Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1108 raw1108Labels permutation32 permutation4
    _ = mixedMoment B node902 node902Labels := by rfl

def raw1109 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, 3, -3]]
def raw1109Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 0, 3]]
def raw1109step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw1109step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw1109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1109 raw1109Labels = mixedMoment B node1590 node1590Labels := by
  calc
    mixedMoment B raw1109 raw1109Labels = mixedMoment B raw1109step0 raw1109step0Labels := by
      have ha : raw1109step0 = (fun i j => raw1109 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1109step0 raw1109; decide +kernel
      have hl : raw1109step0Labels = raw1109Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1109 raw1109Labels permutation38 permutation6
    mixedMoment B raw1109step0 raw1109step0Labels = mixedMoment B raw1109step1 raw1109step1Labels := by
      have ha : raw1109step1 = -raw1109step0 := by apply Matrix.ext; change ∀ i j, raw1109step1 i j = -(raw1109step0 i j); unfold raw1109step1 raw1109step0; decide +kernel
      have hl : raw1109step1Labels = raw1109step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1109step1 raw1109step1Labels = mixedMoment B raw1109step2 raw1109step2Labels := by
      have ha : raw1109step2 = raw1109step1 := by apply Matrix.ext; unfold raw1109step2 raw1109step1; decide +kernel
      have hl : raw1109step1Labels = labelEmbedding1 ∘ raw1109step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1109step1 raw1109step1Labels raw1109step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1590 node1590Labels := by rfl

def raw1110 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw1110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw1110step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw1110step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1110 raw1110Labels = mixedMoment B node4325 node4325Labels := by
  calc
    mixedMoment B raw1110 raw1110Labels = mixedMoment B raw1110step0 raw1110step0Labels := by
      have ha : raw1110step0 = (fun i j => raw1110 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1110step0 raw1110; decide +kernel
      have hl : raw1110step0Labels = raw1110Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1110 raw1110Labels permutation32 permutation4
    mixedMoment B raw1110step0 raw1110step0Labels = mixedMoment B raw1110step1 raw1110step1Labels := by
      have ha : raw1110step1 = raw1110step0 := by apply Matrix.ext; unfold raw1110step1 raw1110step0; decide +kernel
      have hl : raw1110step0Labels = labelEmbedding7 ∘ raw1110step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1110step0 raw1110step0Labels raw1110step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4325 node4325Labels := by rfl

def raw1111 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw1111Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw1111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1111 raw1111Labels = mixedMoment B node903 node903Labels := by
  calc
    mixedMoment B raw1111 raw1111Labels = mixedMoment B raw1111step0 raw1111step0Labels := by
      have ha : raw1111step0 = (fun i j => raw1111 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1111step0 raw1111; decide +kernel
      have hl : raw1111step0Labels = raw1111Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1111 raw1111Labels permutation32 permutation4
    _ = mixedMoment B node903 node903Labels := by rfl

def raw1112 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw1112Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw1112step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw1112step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw1112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1112 raw1112Labels = mixedMoment B node1591 node1591Labels := by
  calc
    mixedMoment B raw1112 raw1112Labels = mixedMoment B raw1112step0 raw1112step0Labels := by
      have ha : raw1112step0 = (fun i j => raw1112 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1112step0 raw1112; decide +kernel
      have hl : raw1112step0Labels = raw1112Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1112 raw1112Labels permutation38 permutation6
    mixedMoment B raw1112step0 raw1112step0Labels = mixedMoment B raw1112step1 raw1112step1Labels := by
      have ha : raw1112step1 = -raw1112step0 := by apply Matrix.ext; change ∀ i j, raw1112step1 i j = -(raw1112step0 i j); unfold raw1112step1 raw1112step0; decide +kernel
      have hl : raw1112step1Labels = raw1112step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1112step1 raw1112step1Labels = mixedMoment B raw1112step2 raw1112step2Labels := by
      have ha : raw1112step2 = raw1112step1 := by apply Matrix.ext; unfold raw1112step2 raw1112step1; decide +kernel
      have hl : raw1112step1Labels = labelEmbedding1 ∘ raw1112step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1112step1 raw1112step1Labels raw1112step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1591 node1591Labels := by rfl

def raw1113 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1113step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1113step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1113step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1113 raw1113Labels = mixedMoment B node4337 node4337Labels := by
  calc
    mixedMoment B raw1113 raw1113Labels = mixedMoment B raw1113step0 raw1113step0Labels := by
      have ha : raw1113step0 = (fun i j => raw1113 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1113step0 raw1113; decide +kernel
      have hl : raw1113step0Labels = raw1113Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1113 raw1113Labels permutation152 permutation4
    mixedMoment B raw1113step0 raw1113step0Labels = mixedMoment B raw1113step1 raw1113step1Labels := by
      have ha : raw1113step1 = raw1113step0 := by apply Matrix.ext; unfold raw1113step1 raw1113step0; decide +kernel
      have hl : raw1113step0Labels = labelEmbedding7 ∘ raw1113step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1113step0 raw1113step0Labels raw1113step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4337 node4337Labels := by rfl

def raw1114 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1114Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1114step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1114 raw1114Labels = mixedMoment B node915 node915Labels := by
  calc
    mixedMoment B raw1114 raw1114Labels = mixedMoment B raw1114step0 raw1114step0Labels := by
      have ha : raw1114step0 = (fun i j => raw1114 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1114step0 raw1114; decide +kernel
      have hl : raw1114step0Labels = raw1114Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1114 raw1114Labels permutation152 permutation4
    _ = mixedMoment B node915 node915Labels := by rfl

def raw1115 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1115Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1115step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1115step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1115step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1115step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1115 raw1115Labels = mixedMoment B node1632 node1632Labels := by
  calc
    mixedMoment B raw1115 raw1115Labels = mixedMoment B raw1115step0 raw1115step0Labels := by
      have ha : raw1115step0 = (fun i j => raw1115 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1115step0 raw1115; decide +kernel
      have hl : raw1115step0Labels = raw1115Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1115 raw1115Labels permutation176 permutation6
    mixedMoment B raw1115step0 raw1115step0Labels = mixedMoment B raw1115step1 raw1115step1Labels := by
      have ha : raw1115step1 = -raw1115step0 := by apply Matrix.ext; change ∀ i j, raw1115step1 i j = -(raw1115step0 i j); unfold raw1115step1 raw1115step0; decide +kernel
      have hl : raw1115step1Labels = raw1115step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1115step1 raw1115step1Labels = mixedMoment B raw1115step2 raw1115step2Labels := by
      have ha : raw1115step2 = raw1115step1 := by apply Matrix.ext; unfold raw1115step2 raw1115step1; decide +kernel
      have hl : raw1115step1Labels = labelEmbedding1 ∘ raw1115step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1115step1 raw1115step1Labels raw1115step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1632 node1632Labels := by rfl

def raw1116 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1116step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1116step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1116 raw1116Labels = mixedMoment B node4338 node4338Labels := by
  calc
    mixedMoment B raw1116 raw1116Labels = mixedMoment B raw1116step0 raw1116step0Labels := by
      have ha : raw1116step0 = (fun i j => raw1116 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1116step0 raw1116; decide +kernel
      have hl : raw1116step0Labels = raw1116Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1116 raw1116Labels permutation32 permutation4
    mixedMoment B raw1116step0 raw1116step0Labels = mixedMoment B raw1116step1 raw1116step1Labels := by
      have ha : raw1116step1 = raw1116step0 := by apply Matrix.ext; unfold raw1116step1 raw1116step0; decide +kernel
      have hl : raw1116step0Labels = labelEmbedding7 ∘ raw1116step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1116step0 raw1116step0Labels raw1116step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4338 node4338Labels := by rfl

def raw1117 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1117 raw1117Labels = mixedMoment B node916 node916Labels := by
  calc
    mixedMoment B raw1117 raw1117Labels = mixedMoment B raw1117step0 raw1117step0Labels := by
      have ha : raw1117step0 = (fun i j => raw1117 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1117step0 raw1117; decide +kernel
      have hl : raw1117step0Labels = raw1117Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1117 raw1117Labels permutation32 permutation4
    _ = mixedMoment B node916 node916Labels := by rfl

def raw1118 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1118Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw1118step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1118step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1118 raw1118Labels = mixedMoment B node1633 node1633Labels := by
  calc
    mixedMoment B raw1118 raw1118Labels = mixedMoment B raw1118step0 raw1118step0Labels := by
      have ha : raw1118step0 = (fun i j => raw1118 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1118step0 raw1118; decide +kernel
      have hl : raw1118step0Labels = raw1118Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1118 raw1118Labels permutation38 permutation6
    mixedMoment B raw1118step0 raw1118step0Labels = mixedMoment B raw1118step1 raw1118step1Labels := by
      have ha : raw1118step1 = -raw1118step0 := by apply Matrix.ext; change ∀ i j, raw1118step1 i j = -(raw1118step0 i j); unfold raw1118step1 raw1118step0; decide +kernel
      have hl : raw1118step1Labels = raw1118step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1118step1 raw1118step1Labels = mixedMoment B raw1118step2 raw1118step2Labels := by
      have ha : raw1118step2 = raw1118step1 := by apply Matrix.ext; unfold raw1118step2 raw1118step1; decide +kernel
      have hl : raw1118step1Labels = labelEmbedding1 ∘ raw1118step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1118step1 raw1118step1Labels raw1118step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1633 node1633Labels := by rfl

def raw1119 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1119step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1119step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1119 raw1119Labels = mixedMoment B node4339 node4339Labels := by
  calc
    mixedMoment B raw1119 raw1119Labels = mixedMoment B raw1119step0 raw1119step0Labels := by
      have ha : raw1119step0 = (fun i j => raw1119 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1119step0 raw1119; decide +kernel
      have hl : raw1119step0Labels = raw1119Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1119 raw1119Labels permutation32 permutation4
    mixedMoment B raw1119step0 raw1119step0Labels = mixedMoment B raw1119step1 raw1119step1Labels := by
      have ha : raw1119step1 = raw1119step0 := by apply Matrix.ext; unfold raw1119step1 raw1119step0; decide +kernel
      have hl : raw1119step0Labels = labelEmbedding7 ∘ raw1119step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1119step0 raw1119step0Labels raw1119step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4339 node4339Labels := by rfl

def raw1120 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1120Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1120step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1120 raw1120Labels = mixedMoment B node917 node917Labels := by
  calc
    mixedMoment B raw1120 raw1120Labels = mixedMoment B raw1120step0 raw1120step0Labels := by
      have ha : raw1120step0 = (fun i j => raw1120 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1120step0 raw1120; decide +kernel
      have hl : raw1120step0Labels = raw1120Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1120 raw1120Labels permutation32 permutation4
    _ = mixedMoment B node917 node917Labels := by rfl

def raw1121 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1121Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw1121step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1121step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1121step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1121 raw1121Labels = mixedMoment B node1634 node1634Labels := by
  calc
    mixedMoment B raw1121 raw1121Labels = mixedMoment B raw1121step0 raw1121step0Labels := by
      have ha : raw1121step0 = (fun i j => raw1121 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1121step0 raw1121; decide +kernel
      have hl : raw1121step0Labels = raw1121Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1121 raw1121Labels permutation38 permutation6
    mixedMoment B raw1121step0 raw1121step0Labels = mixedMoment B raw1121step1 raw1121step1Labels := by
      have ha : raw1121step1 = -raw1121step0 := by apply Matrix.ext; change ∀ i j, raw1121step1 i j = -(raw1121step0 i j); unfold raw1121step1 raw1121step0; decide +kernel
      have hl : raw1121step1Labels = raw1121step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1121step1 raw1121step1Labels = mixedMoment B raw1121step2 raw1121step2Labels := by
      have ha : raw1121step2 = raw1121step1 := by apply Matrix.ext; unfold raw1121step2 raw1121step1; decide +kernel
      have hl : raw1121step1Labels = labelEmbedding1 ∘ raw1121step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1121step1 raw1121step1Labels raw1121step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1634 node1634Labels := by rfl

def raw1122 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1122step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1122step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1122step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1122 raw1122Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw1122 raw1122Labels = mixedMoment B raw1122step0 raw1122step0Labels := by
      have ha : raw1122step0 = (fun i j => raw1122 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1122step0 raw1122; decide +kernel
      have hl : raw1122step0Labels = raw1122Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1122 raw1122Labels permutation152 permutation4
    mixedMoment B raw1122step0 raw1122step0Labels = mixedMoment B raw1122step1 raw1122step1Labels := by
      have ha : raw1122step1 = raw1122step0 := by apply Matrix.ext; unfold raw1122step1 raw1122step0; decide +kernel
      have hl : raw1122step0Labels = labelEmbedding7 ∘ raw1122step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1122step0 raw1122step0Labels raw1122step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4341 node4341Labels := by rfl

def raw1123 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1123 raw1123Labels = mixedMoment B node919 node919Labels := by
  calc
    mixedMoment B raw1123 raw1123Labels = mixedMoment B raw1123step0 raw1123step0Labels := by
      have ha : raw1123step0 = (fun i j => raw1123 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1123step0 raw1123; decide +kernel
      have hl : raw1123step0Labels = raw1123Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1123 raw1123Labels permutation152 permutation4
    _ = mixedMoment B node919 node919Labels := by rfl

def raw1124 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1124Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1124step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1124step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1124step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1124step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1124step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1124 raw1124Labels = mixedMoment B node1664 node1664Labels := by
  calc
    mixedMoment B raw1124 raw1124Labels = mixedMoment B raw1124step0 raw1124step0Labels := by
      have ha : raw1124step0 = (fun i j => raw1124 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1124step0 raw1124; decide +kernel
      have hl : raw1124step0Labels = raw1124Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1124 raw1124Labels permutation152 permutation6
    mixedMoment B raw1124step0 raw1124step0Labels = mixedMoment B raw1124step1 raw1124step1Labels := by
      have ha : raw1124step1 = -raw1124step0 := by apply Matrix.ext; change ∀ i j, raw1124step1 i j = -(raw1124step0 i j); unfold raw1124step1 raw1124step0; decide +kernel
      have hl : raw1124step1Labels = raw1124step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1124step1 raw1124step1Labels = mixedMoment B raw1124step2 raw1124step2Labels := by
      have ha : raw1124step2 = raw1124step1 := by apply Matrix.ext; unfold raw1124step2 raw1124step1; decide +kernel
      have hl : raw1124step1Labels = labelEmbedding1 ∘ raw1124step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1124step1 raw1124step1Labels raw1124step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1664 node1664Labels := by rfl

def raw1125 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1125step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1125 raw1125Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw1125 raw1125Labels = mixedMoment B raw1125step0 raw1125step0Labels := by
      have ha : raw1125step0 = (fun i j => raw1125 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1125step0 raw1125; decide +kernel
      have hl : raw1125step0Labels = raw1125Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1125 raw1125Labels permutation32 permutation4
    mixedMoment B raw1125step0 raw1125step0Labels = mixedMoment B raw1125step1 raw1125step1Labels := by
      have ha : raw1125step1 = raw1125step0 := by apply Matrix.ext; unfold raw1125step1 raw1125step0; decide +kernel
      have hl : raw1125step0Labels = labelEmbedding7 ∘ raw1125step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1125step0 raw1125step0Labels raw1125step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4343 node4343Labels := by rfl

def raw1126 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1126step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1126 raw1126Labels = mixedMoment B node921 node921Labels := by
  calc
    mixedMoment B raw1126 raw1126Labels = mixedMoment B raw1126step0 raw1126step0Labels := by
      have ha : raw1126step0 = (fun i j => raw1126 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1126step0 raw1126; decide +kernel
      have hl : raw1126step0Labels = raw1126Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1126 raw1126Labels permutation32 permutation4
    _ = mixedMoment B node921 node921Labels := by rfl

def raw1127 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1127Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw1127step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw1127step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw1127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1127 raw1127Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw1127 raw1127Labels = mixedMoment B raw1127step0 raw1127step0Labels := by
      have ha : raw1127step0 = (fun i j => raw1127 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1127step0 raw1127; decide +kernel
      have hl : raw1127step0Labels = raw1127Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1127 raw1127Labels permutation32 permutation6
    mixedMoment B raw1127step0 raw1127step0Labels = mixedMoment B raw1127step1 raw1127step1Labels := by
      have ha : raw1127step1 = -raw1127step0 := by apply Matrix.ext; change ∀ i j, raw1127step1 i j = -(raw1127step0 i j); unfold raw1127step1 raw1127step0; decide +kernel
      have hl : raw1127step1Labels = raw1127step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1127step1 raw1127step1Labels = mixedMoment B raw1127step2 raw1127step2Labels := by
      have ha : raw1127step2 = raw1127step1 := by apply Matrix.ext; unfold raw1127step2 raw1127step1; decide +kernel
      have hl : raw1127step1Labels = labelEmbedding1 ∘ raw1127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1127step1 raw1127step1Labels raw1127step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

def raw1128 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1128step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1128step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1128step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1128 raw1128Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw1128 raw1128Labels = mixedMoment B raw1128step0 raw1128step0Labels := by
      have ha : raw1128step0 = (fun i j => raw1128 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1128step0 raw1128; decide +kernel
      have hl : raw1128step0Labels = raw1128Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1128 raw1128Labels permutation152 permutation4
    mixedMoment B raw1128step0 raw1128step0Labels = mixedMoment B raw1128step1 raw1128step1Labels := by
      have ha : raw1128step1 = raw1128step0 := by apply Matrix.ext; unfold raw1128step1 raw1128step0; decide +kernel
      have hl : raw1128step0Labels = labelEmbedding7 ∘ raw1128step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1128step0 raw1128step0Labels raw1128step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4344 node4344Labels := by rfl

def raw1129 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1129Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1129 raw1129Labels = mixedMoment B node922 node922Labels := by
  calc
    mixedMoment B raw1129 raw1129Labels = mixedMoment B raw1129step0 raw1129step0Labels := by
      have ha : raw1129step0 = (fun i j => raw1129 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1129step0 raw1129; decide +kernel
      have hl : raw1129step0Labels = raw1129Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1129 raw1129Labels permutation152 permutation4
    _ = mixedMoment B node922 node922Labels := by rfl

def raw1130 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1130Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1130step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1130step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1130step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1130step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1130step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1130 raw1130Labels = mixedMoment B node1673 node1673Labels := by
  calc
    mixedMoment B raw1130 raw1130Labels = mixedMoment B raw1130step0 raw1130step0Labels := by
      have ha : raw1130step0 = (fun i j => raw1130 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1130step0 raw1130; decide +kernel
      have hl : raw1130step0Labels = raw1130Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1130 raw1130Labels permutation152 permutation6
    mixedMoment B raw1130step0 raw1130step0Labels = mixedMoment B raw1130step1 raw1130step1Labels := by
      have ha : raw1130step1 = -raw1130step0 := by apply Matrix.ext; change ∀ i j, raw1130step1 i j = -(raw1130step0 i j); unfold raw1130step1 raw1130step0; decide +kernel
      have hl : raw1130step1Labels = raw1130step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1130step1 raw1130step1Labels = mixedMoment B raw1130step2 raw1130step2Labels := by
      have ha : raw1130step2 = raw1130step1 := by apply Matrix.ext; unfold raw1130step2 raw1130step1; decide +kernel
      have hl : raw1130step1Labels = labelEmbedding1 ∘ raw1130step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1130step1 raw1130step1Labels raw1130step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1673 node1673Labels := by rfl

def raw1131 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1131step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1131step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1131 raw1131Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw1131 raw1131Labels = mixedMoment B raw1131step0 raw1131step0Labels := by
      have ha : raw1131step0 = (fun i j => raw1131 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1131step0 raw1131; decide +kernel
      have hl : raw1131step0Labels = raw1131Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1131 raw1131Labels permutation32 permutation4
    mixedMoment B raw1131step0 raw1131step0Labels = mixedMoment B raw1131step1 raw1131step1Labels := by
      have ha : raw1131step1 = raw1131step0 := by apply Matrix.ext; unfold raw1131step1 raw1131step0; decide +kernel
      have hl : raw1131step0Labels = labelEmbedding7 ∘ raw1131step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1131step0 raw1131step0Labels raw1131step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4346 node4346Labels := by rfl

def raw1132 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1132Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1132step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1132 raw1132Labels = mixedMoment B node924 node924Labels := by
  calc
    mixedMoment B raw1132 raw1132Labels = mixedMoment B raw1132step0 raw1132step0Labels := by
      have ha : raw1132step0 = (fun i j => raw1132 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1132step0 raw1132; decide +kernel
      have hl : raw1132step0Labels = raw1132Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1132 raw1132Labels permutation32 permutation4
    _ = mixedMoment B node924 node924Labels := by rfl

def raw1133 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1133Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1133step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1133step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1133step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1133step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1133 raw1133Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw1133 raw1133Labels = mixedMoment B raw1133step0 raw1133step0Labels := by
      have ha : raw1133step0 = (fun i j => raw1133 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1133step0 raw1133; decide +kernel
      have hl : raw1133step0Labels = raw1133Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1133 raw1133Labels permutation32 permutation6
    mixedMoment B raw1133step0 raw1133step0Labels = mixedMoment B raw1133step1 raw1133step1Labels := by
      have ha : raw1133step1 = -raw1133step0 := by apply Matrix.ext; change ∀ i j, raw1133step1 i j = -(raw1133step0 i j); unfold raw1133step1 raw1133step0; decide +kernel
      have hl : raw1133step1Labels = raw1133step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1133step1 raw1133step1Labels = mixedMoment B raw1133step2 raw1133step2Labels := by
      have ha : raw1133step2 = raw1133step1 := by apply Matrix.ext; unfold raw1133step2 raw1133step1; decide +kernel
      have hl : raw1133step1Labels = labelEmbedding1 ∘ raw1133step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1133step1 raw1133step1Labels raw1133step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

def raw1134 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1134step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1134step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1134 raw1134Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw1134 raw1134Labels = mixedMoment B raw1134step0 raw1134step0Labels := by
      have ha : raw1134step0 = (fun i j => raw1134 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1134step0 raw1134; decide +kernel
      have hl : raw1134step0Labels = raw1134Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1134 raw1134Labels permutation32 permutation4
    mixedMoment B raw1134step0 raw1134step0Labels = mixedMoment B raw1134step1 raw1134step1Labels := by
      have ha : raw1134step1 = raw1134step0 := by apply Matrix.ext; unfold raw1134step1 raw1134step0; decide +kernel
      have hl : raw1134step0Labels = labelEmbedding7 ∘ raw1134step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1134step0 raw1134step0Labels raw1134step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4349 node4349Labels := by rfl

def raw1135 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1135Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1135step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1135 raw1135Labels = mixedMoment B node927 node927Labels := by
  calc
    mixedMoment B raw1135 raw1135Labels = mixedMoment B raw1135step0 raw1135step0Labels := by
      have ha : raw1135step0 = (fun i j => raw1135 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1135step0 raw1135; decide +kernel
      have hl : raw1135step0Labels = raw1135Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1135 raw1135Labels permutation32 permutation4
    _ = mixedMoment B node927 node927Labels := by rfl

def raw1136 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1136Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1136step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1136step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1136step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1136step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1136 raw1136Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw1136 raw1136Labels = mixedMoment B raw1136step0 raw1136step0Labels := by
      have ha : raw1136step0 = (fun i j => raw1136 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1136step0 raw1136; decide +kernel
      have hl : raw1136step0Labels = raw1136Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1136 raw1136Labels permutation32 permutation6
    mixedMoment B raw1136step0 raw1136step0Labels = mixedMoment B raw1136step1 raw1136step1Labels := by
      have ha : raw1136step1 = -raw1136step0 := by apply Matrix.ext; change ∀ i j, raw1136step1 i j = -(raw1136step0 i j); unfold raw1136step1 raw1136step0; decide +kernel
      have hl : raw1136step1Labels = raw1136step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1136step1 raw1136step1Labels = mixedMoment B raw1136step2 raw1136step2Labels := by
      have ha : raw1136step2 = raw1136step1 := by apply Matrix.ext; unfold raw1136step2 raw1136step1; decide +kernel
      have hl : raw1136step1Labels = labelEmbedding1 ∘ raw1136step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1136step1 raw1136step1Labels raw1136step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

def raw1137 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 4, -3]]
def raw1137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1137step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw1137step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1137step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw1137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1137 raw1137Labels = mixedMoment B node4350 node4350Labels := by
  calc
    mixedMoment B raw1137 raw1137Labels = mixedMoment B raw1137step0 raw1137step0Labels := by
      have ha : raw1137step0 = (fun i j => raw1137 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1137step0 raw1137; decide +kernel
      have hl : raw1137step0Labels = raw1137Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1137 raw1137Labels permutation8 permutation4
    mixedMoment B raw1137step0 raw1137step0Labels = mixedMoment B raw1137step1 raw1137step1Labels := by
      have ha : raw1137step1 = raw1137step0 := by apply Matrix.ext; unfold raw1137step1 raw1137step0; decide +kernel
      have hl : raw1137step0Labels = labelEmbedding7 ∘ raw1137step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1137step0 raw1137step0Labels raw1137step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4350 node4350Labels := by rfl

def raw1138 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 4, -3]]
def raw1138Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1138step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw1138step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1138 raw1138Labels = mixedMoment B node928 node928Labels := by
  calc
    mixedMoment B raw1138 raw1138Labels = mixedMoment B raw1138step0 raw1138step0Labels := by
      have ha : raw1138step0 = (fun i j => raw1138 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1138step0 raw1138; decide +kernel
      have hl : raw1138step0Labels = raw1138Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1138 raw1138Labels permutation8 permutation4
    _ = mixedMoment B node928 node928Labels := by rfl

def raw1139 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 4, -3]]
def raw1139Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1139step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw1139step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw1139step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1139 raw1139Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw1139 raw1139Labels = mixedMoment B raw1139step0 raw1139step0Labels := by
      have ha : raw1139step0 = (fun i j => raw1139 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1139step0 raw1139; decide +kernel
      have hl : raw1139step0Labels = raw1139Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1139 raw1139Labels permutation31 permutation6
    mixedMoment B raw1139step0 raw1139step0Labels = mixedMoment B raw1139step1 raw1139step1Labels := by
      have ha : raw1139step1 = raw1139step0 := by apply Matrix.ext; unfold raw1139step1 raw1139step0; decide +kernel
      have hl : raw1139step0Labels = labelEmbedding1 ∘ raw1139step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1139step0 raw1139step0Labels raw1139step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

def raw1140 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1140step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1140step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1140 raw1140Labels = mixedMoment B node4351 node4351Labels := by
  calc
    mixedMoment B raw1140 raw1140Labels = mixedMoment B raw1140step0 raw1140step0Labels := by
      have ha : raw1140step0 = (fun i j => raw1140 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1140step0 raw1140; decide +kernel
      have hl : raw1140step0Labels = raw1140Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1140 raw1140Labels permutation152 permutation4
    mixedMoment B raw1140step0 raw1140step0Labels = mixedMoment B raw1140step1 raw1140step1Labels := by
      have ha : raw1140step1 = raw1140step0 := by apply Matrix.ext; unfold raw1140step1 raw1140step0; decide +kernel
      have hl : raw1140step0Labels = labelEmbedding7 ∘ raw1140step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1140step0 raw1140step0Labels raw1140step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4351 node4351Labels := by rfl

def raw1141 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1141Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1141step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1141 raw1141Labels = mixedMoment B node929 node929Labels := by
  calc
    mixedMoment B raw1141 raw1141Labels = mixedMoment B raw1141step0 raw1141step0Labels := by
      have ha : raw1141step0 = (fun i j => raw1141 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1141step0 raw1141; decide +kernel
      have hl : raw1141step0Labels = raw1141Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1141 raw1141Labels permutation152 permutation4
    _ = mixedMoment B node929 node929Labels := by rfl

def raw1142 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1142Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1142step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1142step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1142step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1142step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1142step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1142step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1142 raw1142Labels = mixedMoment B node1680 node1680Labels := by
  calc
    mixedMoment B raw1142 raw1142Labels = mixedMoment B raw1142step0 raw1142step0Labels := by
      have ha : raw1142step0 = (fun i j => raw1142 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1142step0 raw1142; decide +kernel
      have hl : raw1142step0Labels = raw1142Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1142 raw1142Labels permutation170 permutation6
    mixedMoment B raw1142step0 raw1142step0Labels = mixedMoment B raw1142step1 raw1142step1Labels := by
      have ha : raw1142step1 = -raw1142step0 := by apply Matrix.ext; change ∀ i j, raw1142step1 i j = -(raw1142step0 i j); unfold raw1142step1 raw1142step0; decide +kernel
      have hl : raw1142step1Labels = raw1142step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1142step1 raw1142step1Labels = mixedMoment B raw1142step2 raw1142step2Labels := by
      have ha : raw1142step2 = raw1142step1 := by apply Matrix.ext; unfold raw1142step2 raw1142step1; decide +kernel
      have hl : raw1142step1Labels = labelEmbedding1 ∘ raw1142step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1142step1 raw1142step1Labels raw1142step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1680 node1680Labels := by rfl

def raw1143 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1143step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1143step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1143 raw1143Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw1143 raw1143Labels = mixedMoment B raw1143step0 raw1143step0Labels := by
      have ha : raw1143step0 = (fun i j => raw1143 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1143step0 raw1143; decide +kernel
      have hl : raw1143step0Labels = raw1143Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1143 raw1143Labels permutation32 permutation4
    mixedMoment B raw1143step0 raw1143step0Labels = mixedMoment B raw1143step1 raw1143step1Labels := by
      have ha : raw1143step1 = raw1143step0 := by apply Matrix.ext; unfold raw1143step1 raw1143step0; decide +kernel
      have hl : raw1143step0Labels = labelEmbedding7 ∘ raw1143step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1143step0 raw1143step0Labels raw1143step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4352 node4352Labels := by rfl

def raw1144 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1144Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1144step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1144 raw1144Labels = mixedMoment B node930 node930Labels := by
  calc
    mixedMoment B raw1144 raw1144Labels = mixedMoment B raw1144step0 raw1144step0Labels := by
      have ha : raw1144step0 = (fun i j => raw1144 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1144step0 raw1144; decide +kernel
      have hl : raw1144step0Labels = raw1144Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1144 raw1144Labels permutation32 permutation4
    _ = mixedMoment B node930 node930Labels := by rfl

def raw1145 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1145Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1145step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1145step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1145step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1145step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1145 raw1145Labels = mixedMoment B node1690 node1690Labels := by
  calc
    mixedMoment B raw1145 raw1145Labels = mixedMoment B raw1145step0 raw1145step0Labels := by
      have ha : raw1145step0 = (fun i j => raw1145 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1145step0 raw1145; decide +kernel
      have hl : raw1145step0Labels = raw1145Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1145 raw1145Labels permutation32 permutation6
    mixedMoment B raw1145step0 raw1145step0Labels = mixedMoment B raw1145step1 raw1145step1Labels := by
      have ha : raw1145step1 = -raw1145step0 := by apply Matrix.ext; change ∀ i j, raw1145step1 i j = -(raw1145step0 i j); unfold raw1145step1 raw1145step0; decide +kernel
      have hl : raw1145step1Labels = raw1145step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1145step1 raw1145step1Labels = mixedMoment B raw1145step2 raw1145step2Labels := by
      have ha : raw1145step2 = raw1145step1 := by apply Matrix.ext; unfold raw1145step2 raw1145step1; decide +kernel
      have hl : raw1145step1Labels = labelEmbedding1 ∘ raw1145step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1145step1 raw1145step1Labels raw1145step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1690 node1690Labels := by rfl

def raw1146 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1146step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1146 raw1146Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw1146 raw1146Labels = mixedMoment B raw1146step0 raw1146step0Labels := by
      have ha : raw1146step0 = (fun i j => raw1146 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1146step0 raw1146; decide +kernel
      have hl : raw1146step0Labels = raw1146Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1146 raw1146Labels permutation32 permutation4
    mixedMoment B raw1146step0 raw1146step0Labels = mixedMoment B raw1146step1 raw1146step1Labels := by
      have ha : raw1146step1 = raw1146step0 := by apply Matrix.ext; unfold raw1146step1 raw1146step0; decide +kernel
      have hl : raw1146step0Labels = labelEmbedding7 ∘ raw1146step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1146step0 raw1146step0Labels raw1146step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4354 node4354Labels := by rfl

def raw1147 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1147Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1147step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1147 raw1147Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw1147 raw1147Labels = mixedMoment B raw1147step0 raw1147step0Labels := by
      have ha : raw1147step0 = (fun i j => raw1147 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1147step0 raw1147; decide +kernel
      have hl : raw1147step0Labels = raw1147Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1147 raw1147Labels permutation32 permutation4
    _ = mixedMoment B node932 node932Labels := by rfl

def raw1148 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1148Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw1148step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1148step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1148step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1148 raw1148Labels = mixedMoment B node1681 node1681Labels := by
  calc
    mixedMoment B raw1148 raw1148Labels = mixedMoment B raw1148step0 raw1148step0Labels := by
      have ha : raw1148step0 = (fun i j => raw1148 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1148step0 raw1148; decide +kernel
      have hl : raw1148step0Labels = raw1148Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1148 raw1148Labels permutation34 permutation6
    mixedMoment B raw1148step0 raw1148step0Labels = mixedMoment B raw1148step1 raw1148step1Labels := by
      have ha : raw1148step1 = -raw1148step0 := by apply Matrix.ext; change ∀ i j, raw1148step1 i j = -(raw1148step0 i j); unfold raw1148step1 raw1148step0; decide +kernel
      have hl : raw1148step1Labels = raw1148step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1148step1 raw1148step1Labels = mixedMoment B raw1148step2 raw1148step2Labels := by
      have ha : raw1148step2 = raw1148step1 := by apply Matrix.ext; unfold raw1148step2 raw1148step1; decide +kernel
      have hl : raw1148step1Labels = labelEmbedding1 ∘ raw1148step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1148step1 raw1148step1Labels raw1148step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1681 node1681Labels := by rfl

def raw1149 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1149step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1149step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1149 raw1149Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw1149 raw1149Labels = mixedMoment B raw1149step0 raw1149step0Labels := by
      have ha : raw1149step0 = (fun i j => raw1149 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1149step0 raw1149; decide +kernel
      have hl : raw1149step0Labels = raw1149Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1149 raw1149Labels permutation32 permutation4
    mixedMoment B raw1149step0 raw1149step0Labels = mixedMoment B raw1149step1 raw1149step1Labels := by
      have ha : raw1149step1 = raw1149step0 := by apply Matrix.ext; unfold raw1149step1 raw1149step0; decide +kernel
      have hl : raw1149step0Labels = labelEmbedding7 ∘ raw1149step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1149step0 raw1149step0Labels raw1149step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4355 node4355Labels := by rfl

def raw1150 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1150Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1150step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1150 raw1150Labels = mixedMoment B node933 node933Labels := by
  calc
    mixedMoment B raw1150 raw1150Labels = mixedMoment B raw1150step0 raw1150step0Labels := by
      have ha : raw1150step0 = (fun i j => raw1150 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1150step0 raw1150; decide +kernel
      have hl : raw1150step0Labels = raw1150Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1150 raw1150Labels permutation32 permutation4
    _ = mixedMoment B node933 node933Labels := by rfl

def raw1151 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1151Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1151step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1151step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1151step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1151step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1151 raw1151Labels = mixedMoment B node1691 node1691Labels := by
  calc
    mixedMoment B raw1151 raw1151Labels = mixedMoment B raw1151step0 raw1151step0Labels := by
      have ha : raw1151step0 = (fun i j => raw1151 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1151step0 raw1151; decide +kernel
      have hl : raw1151step0Labels = raw1151Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1151 raw1151Labels permutation32 permutation6
    mixedMoment B raw1151step0 raw1151step0Labels = mixedMoment B raw1151step1 raw1151step1Labels := by
      have ha : raw1151step1 = -raw1151step0 := by apply Matrix.ext; change ∀ i j, raw1151step1 i j = -(raw1151step0 i j); unfold raw1151step1 raw1151step0; decide +kernel
      have hl : raw1151step1Labels = raw1151step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1151step1 raw1151step1Labels = mixedMoment B raw1151step2 raw1151step2Labels := by
      have ha : raw1151step2 = raw1151step1 := by apply Matrix.ext; unfold raw1151step2 raw1151step1; decide +kernel
      have hl : raw1151step1Labels = labelEmbedding1 ∘ raw1151step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1151step1 raw1151step1Labels raw1151step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1691 node1691Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
