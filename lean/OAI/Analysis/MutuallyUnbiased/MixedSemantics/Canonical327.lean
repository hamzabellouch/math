import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw41856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw41856Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw41856step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw41856step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw41856step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41856 raw41856Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw41856 raw41856Labels = mixedMoment B raw41856step0 raw41856step0Labels := by
      have hz : ∀ j, raw41856 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41856step0 = (fun i j => raw41856 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41856step0 raw41856; decide +kernel
      have hl : raw41856step0Labels = raw41856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41856 raw41856Labels permutation265 hz
    mixedMoment B raw41856step0 raw41856step0Labels = mixedMoment B raw41856step1 raw41856step1Labels := by
      have ha : raw41856step1 = (fun i j => raw41856step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41856step1 raw41856step0; decide +kernel
      have hl : raw41856step1Labels = raw41856step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41856step0 raw41856step0Labels permutation37 permutation2
    mixedMoment B raw41856step1 raw41856step1Labels = mixedMoment B raw41856step2 raw41856step2Labels := by
      have ha : raw41856step2 = raw41856step1 := by apply Matrix.ext; unfold raw41856step2 raw41856step1; decide +kernel
      have hl : raw41856step1Labels = labelEmbedding1 ∘ raw41856step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41856step1 raw41856step1Labels raw41856step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

def raw41857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw41857Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw41857step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw41857step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41857step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41857step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41857step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41857 raw41857Labels = mixedMoment B node4777 node4777Labels := by
  calc
    mixedMoment B raw41857 raw41857Labels = mixedMoment B raw41857step0 raw41857step0Labels := by
      have hz : ∀ j, raw41857 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41857step0 = (fun i j => raw41857 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41857step0 raw41857; decide +kernel
      have hl : raw41857step0Labels = raw41857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41857 raw41857Labels permutation265 hz
    mixedMoment B raw41857step0 raw41857step0Labels = mixedMoment B raw41857step1 raw41857step1Labels := by
      have ha : raw41857step1 = (fun i j => raw41857step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41857step1 raw41857step0; decide +kernel
      have hl : raw41857step1Labels = raw41857step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41857step0 raw41857step0Labels permutation37 permutation7
    mixedMoment B raw41857step1 raw41857step1Labels = mixedMoment B raw41857step2 raw41857step2Labels := by
      have ha : raw41857step2 = -raw41857step1 := by apply Matrix.ext; change ∀ i j, raw41857step2 i j = -(raw41857step1 i j); unfold raw41857step2 raw41857step1; decide +kernel
      have hl : raw41857step2Labels = raw41857step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41857step2 raw41857step2Labels = mixedMoment B raw41857step3 raw41857step3Labels := by
      have ha : raw41857step3 = raw41857step2 := by apply Matrix.ext; unfold raw41857step3 raw41857step2; decide +kernel
      have hl : raw41857step2Labels = labelEmbedding6 ∘ raw41857step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41857step2 raw41857step2Labels raw41857step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4777 node4777Labels := by rfl

def raw41858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41858Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41858step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw41858step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41858step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41858step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41858step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41858 raw41858Labels = mixedMoment B node1685 node1685Labels := by
  calc
    mixedMoment B raw41858 raw41858Labels = mixedMoment B raw41858step0 raw41858step0Labels := by
      have hz : ∀ j, raw41858 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41858step0 = (fun i j => raw41858 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41858step0 raw41858; decide +kernel
      have hl : raw41858step0Labels = raw41858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41858 raw41858Labels permutation265 hz
    mixedMoment B raw41858step0 raw41858step0Labels = mixedMoment B raw41858step1 raw41858step1Labels := by
      have ha : raw41858step1 = (fun i j => raw41858step0 (permutation93 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41858step1 raw41858step0; decide +kernel
      have hl : raw41858step1Labels = raw41858step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41858step0 raw41858step0Labels permutation93 permutation4
    mixedMoment B raw41858step1 raw41858step1Labels = mixedMoment B raw41858step2 raw41858step2Labels := by
      have ha : raw41858step2 = -raw41858step1 := by apply Matrix.ext; change ∀ i j, raw41858step2 i j = -(raw41858step1 i j); unfold raw41858step2 raw41858step1; decide +kernel
      have hl : raw41858step2Labels = raw41858step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41858step2 raw41858step2Labels = mixedMoment B raw41858step3 raw41858step3Labels := by
      have ha : raw41858step3 = raw41858step2 := by apply Matrix.ext; unfold raw41858step3 raw41858step2; decide +kernel
      have hl : raw41858step2Labels = labelEmbedding1 ∘ raw41858step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41858step2 raw41858step2Labels raw41858step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1685 node1685Labels := by rfl

def raw41859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41859Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41859step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw41859step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41859 raw41859Labels = mixedMoment B node4336 node4336Labels := by
  calc
    mixedMoment B raw41859 raw41859Labels = mixedMoment B raw41859step0 raw41859step0Labels := by
      have hz : ∀ j, raw41859 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41859step0 = (fun i j => raw41859 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41859step0 raw41859; decide +kernel
      have hl : raw41859step0Labels = raw41859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41859 raw41859Labels permutation265 hz
    mixedMoment B raw41859step0 raw41859step0Labels = mixedMoment B raw41859step1 raw41859step1Labels := by
      have ha : raw41859step1 = (fun i j => raw41859step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41859step1 raw41859step0; decide +kernel
      have hl : raw41859step1Labels = raw41859step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41859step0 raw41859step0Labels permutation97 permutation6
    _ = mixedMoment B node4336 node4336Labels := by rfl

def raw41860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41860Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41860step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw41860step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw41860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41860 raw41860Labels = mixedMoment B node2164 node2164Labels := by
  calc
    mixedMoment B raw41860 raw41860Labels = mixedMoment B raw41860step0 raw41860step0Labels := by
      have hz : ∀ j, raw41860 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41860step0 = (fun i j => raw41860 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41860step0 raw41860; decide +kernel
      have hl : raw41860step0Labels = raw41860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41860 raw41860Labels permutation265 hz
    mixedMoment B raw41860step0 raw41860step0Labels = mixedMoment B raw41860step1 raw41860step1Labels := by
      have ha : raw41860step1 = (fun i j => raw41860step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41860step1 raw41860step0; decide +kernel
      have hl : raw41860step1Labels = raw41860step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41860step0 raw41860step0Labels permutation37 permutation2
    mixedMoment B raw41860step1 raw41860step1Labels = mixedMoment B raw41860step2 raw41860step2Labels := by
      have ha : raw41860step2 = raw41860step1 := by apply Matrix.ext; unfold raw41860step2 raw41860step1; decide +kernel
      have hl : raw41860step1Labels = labelEmbedding1 ∘ raw41860step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41860step1 raw41860step1Labels raw41860step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2164 node2164Labels := by rfl

def raw41861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41861Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41861step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw41861step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41861step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41861step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41861step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41861 raw41861Labels = mixedMoment B node4670 node4670Labels := by
  calc
    mixedMoment B raw41861 raw41861Labels = mixedMoment B raw41861step0 raw41861step0Labels := by
      have hz : ∀ j, raw41861 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41861step0 = (fun i j => raw41861 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41861step0 raw41861; decide +kernel
      have hl : raw41861step0Labels = raw41861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41861 raw41861Labels permutation265 hz
    mixedMoment B raw41861step0 raw41861step0Labels = mixedMoment B raw41861step1 raw41861step1Labels := by
      have ha : raw41861step1 = (fun i j => raw41861step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41861step1 raw41861step0; decide +kernel
      have hl : raw41861step1Labels = raw41861step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41861step0 raw41861step0Labels permutation37 permutation7
    mixedMoment B raw41861step1 raw41861step1Labels = mixedMoment B raw41861step2 raw41861step2Labels := by
      have ha : raw41861step2 = -raw41861step1 := by apply Matrix.ext; change ∀ i j, raw41861step2 i j = -(raw41861step1 i j); unfold raw41861step2 raw41861step1; decide +kernel
      have hl : raw41861step2Labels = raw41861step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41861step2 raw41861step2Labels = mixedMoment B raw41861step3 raw41861step3Labels := by
      have ha : raw41861step3 = raw41861step2 := by apply Matrix.ext; unfold raw41861step3 raw41861step2; decide +kernel
      have hl : raw41861step2Labels = labelEmbedding6 ∘ raw41861step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41861step2 raw41861step2Labels raw41861step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4670 node4670Labels := by rfl

def raw41862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41862Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw41862step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41862step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41862step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41862step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41862 raw41862Labels = mixedMoment B node1684 node1684Labels := by
  calc
    mixedMoment B raw41862 raw41862Labels = mixedMoment B raw41862step0 raw41862step0Labels := by
      have ha : raw41862step0 = (fun i j => raw41862 (permutation487 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41862step0 raw41862; decide +kernel
      have hl : raw41862step0Labels = raw41862Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41862 raw41862Labels permutation487 permutation4
    mixedMoment B raw41862step0 raw41862step0Labels = mixedMoment B raw41862step1 raw41862step1Labels := by
      have ha : raw41862step1 = -raw41862step0 := by apply Matrix.ext; change ∀ i j, raw41862step1 i j = -(raw41862step0 i j); unfold raw41862step1 raw41862step0; decide +kernel
      have hl : raw41862step1Labels = raw41862step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41862step1 raw41862step1Labels = mixedMoment B raw41862step2 raw41862step2Labels := by
      have ha : raw41862step2 = raw41862step1 := by apply Matrix.ext; unfold raw41862step2 raw41862step1; decide +kernel
      have hl : raw41862step1Labels = labelEmbedding1 ∘ raw41862step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41862step1 raw41862step1Labels raw41862step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1684 node1684Labels := by rfl

def raw41863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41863Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41863 raw41863Labels = mixedMoment B node4331 node4331Labels := by
  calc
    mixedMoment B raw41863 raw41863Labels = mixedMoment B raw41863step0 raw41863step0Labels := by
      have ha : raw41863step0 = (fun i j => raw41863 (permutation502 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41863step0 raw41863; decide +kernel
      have hl : raw41863step0Labels = raw41863Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41863 raw41863Labels permutation502 permutation6
    _ = mixedMoment B node4331 node4331Labels := by rfl

def raw41864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41864Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw41864step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw41864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41864 raw41864Labels = mixedMoment B node2181 node2181Labels := by
  calc
    mixedMoment B raw41864 raw41864Labels = mixedMoment B raw41864step0 raw41864step0Labels := by
      have ha : raw41864step0 = (fun i j => raw41864 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41864step0 raw41864; decide +kernel
      have hl : raw41864step0Labels = raw41864Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41864 raw41864Labels permutation157 permutation2
    mixedMoment B raw41864step0 raw41864step0Labels = mixedMoment B raw41864step1 raw41864step1Labels := by
      have ha : raw41864step1 = raw41864step0 := by apply Matrix.ext; unfold raw41864step1 raw41864step0; decide +kernel
      have hl : raw41864step0Labels = labelEmbedding1 ∘ raw41864step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41864step0 raw41864step0Labels raw41864step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2181 node2181Labels := by rfl

def raw41865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41865Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw41865step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41865step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41865step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41865step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41865 raw41865Labels = mixedMoment B node4757 node4757Labels := by
  calc
    mixedMoment B raw41865 raw41865Labels = mixedMoment B raw41865step0 raw41865step0Labels := by
      have ha : raw41865step0 = (fun i j => raw41865 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41865step0 raw41865; decide +kernel
      have hl : raw41865step0Labels = raw41865Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41865 raw41865Labels permutation157 permutation7
    mixedMoment B raw41865step0 raw41865step0Labels = mixedMoment B raw41865step1 raw41865step1Labels := by
      have ha : raw41865step1 = -raw41865step0 := by apply Matrix.ext; change ∀ i j, raw41865step1 i j = -(raw41865step0 i j); unfold raw41865step1 raw41865step0; decide +kernel
      have hl : raw41865step1Labels = raw41865step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41865step1 raw41865step1Labels = mixedMoment B raw41865step2 raw41865step2Labels := by
      have ha : raw41865step2 = raw41865step1 := by apply Matrix.ext; unfold raw41865step2 raw41865step1; decide +kernel
      have hl : raw41865step1Labels = labelEmbedding6 ∘ raw41865step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41865step1 raw41865step1Labels raw41865step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4757 node4757Labels := by rfl

def raw41866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41866Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41866step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw41866step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41866step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw41866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41866 raw41866Labels = mixedMoment B node1746 node1746Labels := by
  calc
    mixedMoment B raw41866 raw41866Labels = mixedMoment B raw41866step0 raw41866step0Labels := by
      have hz : ∀ j, raw41866 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41866step0 = (fun i j => raw41866 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41866step0 raw41866; decide +kernel
      have hl : raw41866step0Labels = raw41866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41866 raw41866Labels permutation434 hz
    mixedMoment B raw41866step0 raw41866step0Labels = mixedMoment B raw41866step1 raw41866step1Labels := by
      have hz : ∀ j, raw41866step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41866step1 = (fun i j => raw41866step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41866step1 raw41866step0; decide +kernel
      have hl : raw41866step1Labels = raw41866step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41866step0 raw41866step0Labels permutation80 hz
    mixedMoment B raw41866step1 raw41866step1Labels = mixedMoment B raw41866step2 raw41866step2Labels := by
      have ha : raw41866step2 = raw41866step1 := by apply Matrix.ext; unfold raw41866step2 raw41866step1; decide +kernel
      have hl : raw41866step1Labels = labelEmbedding1 ∘ raw41866step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41866step1 raw41866step1Labels raw41866step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1746 node1746Labels := by rfl

def raw41867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41867Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41867step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41867step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw41867step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41867step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw41867step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41867step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw41867step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41867step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw41867step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41867 raw41867Labels = mixedMoment B node4478 node4478Labels := by
  calc
    mixedMoment B raw41867 raw41867Labels = mixedMoment B raw41867step0 raw41867step0Labels := by
      have hz : ∀ j, raw41867 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41867step0 = (fun i j => raw41867 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41867step0 raw41867; decide +kernel
      have hl : raw41867step0Labels = raw41867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41867 raw41867Labels permutation434 hz
    mixedMoment B raw41867step0 raw41867step0Labels = mixedMoment B raw41867step1 raw41867step1Labels := by
      have hz : ∀ j, raw41867step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41867step1 = (fun i j => raw41867step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41867step1 raw41867step0; decide +kernel
      have hl : raw41867step1Labels = raw41867step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41867step0 raw41867step0Labels permutation80 hz
    mixedMoment B raw41867step1 raw41867step1Labels = mixedMoment B raw41867step2 raw41867step2Labels := by
      have ha : raw41867step2 = (fun i j => raw41867step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41867step2 raw41867step1; decide +kernel
      have hl : raw41867step2Labels = raw41867step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41867step1 raw41867step1Labels permutation13 permutation7
    mixedMoment B raw41867step2 raw41867step2Labels = mixedMoment B raw41867step3 raw41867step3Labels := by
      have ha : raw41867step3 = -raw41867step2 := by apply Matrix.ext; change ∀ i j, raw41867step3 i j = -(raw41867step2 i j); unfold raw41867step3 raw41867step2; decide +kernel
      have hl : raw41867step3Labels = raw41867step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41867step3 raw41867step3Labels = mixedMoment B raw41867step4 raw41867step4Labels := by
      have ha : raw41867step4 = raw41867step3 := by apply Matrix.ext; unfold raw41867step4 raw41867step3; decide +kernel
      have hl : raw41867step3Labels = labelEmbedding6 ∘ raw41867step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41867step3 raw41867step3Labels raw41867step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4478 node4478Labels := by rfl

def raw41868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41868Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41868step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41868step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41868step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41868 raw41868Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw41868 raw41868Labels = mixedMoment B raw41868step0 raw41868step0Labels := by
      have hz : ∀ j, raw41868 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41868step0 = (fun i j => raw41868 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41868step0 raw41868; decide +kernel
      have hl : raw41868step0Labels = raw41868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41868 raw41868Labels permutation434 hz
    mixedMoment B raw41868step0 raw41868step0Labels = mixedMoment B raw41868step1 raw41868step1Labels := by
      have hz : ∀ j, raw41868step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41868step1 = (fun i j => raw41868step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41868step1 raw41868step0; decide +kernel
      have hl : raw41868step1Labels = raw41868step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41868step0 raw41868step0Labels permutation80 hz
    mixedMoment B raw41868step1 raw41868step1Labels = mixedMoment B raw41868step2 raw41868step2Labels := by
      have ha : raw41868step2 = raw41868step1 := by apply Matrix.ext; unfold raw41868step2 raw41868step1; decide +kernel
      have hl : raw41868step1Labels = labelEmbedding1 ∘ raw41868step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41868step1 raw41868step1Labels raw41868step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1745 node1745Labels := by rfl

def raw41869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41869Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41869step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw41869step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw41869step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41869step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41869step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41869step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw41869step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41869 raw41869Labels = mixedMoment B node4464 node4464Labels := by
  calc
    mixedMoment B raw41869 raw41869Labels = mixedMoment B raw41869step0 raw41869step0Labels := by
      have hz : ∀ j, raw41869 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41869step0 = (fun i j => raw41869 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41869step0 raw41869; decide +kernel
      have hl : raw41869step0Labels = raw41869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41869 raw41869Labels permutation434 hz
    mixedMoment B raw41869step0 raw41869step0Labels = mixedMoment B raw41869step1 raw41869step1Labels := by
      have hz : ∀ j, raw41869step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41869step1 = (fun i j => raw41869step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41869step1 raw41869step0; decide +kernel
      have hl : raw41869step1Labels = raw41869step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41869step0 raw41869step0Labels permutation80 hz
    mixedMoment B raw41869step1 raw41869step1Labels = mixedMoment B raw41869step2 raw41869step2Labels := by
      have ha : raw41869step2 = (fun i j => raw41869step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41869step2 raw41869step1; decide +kernel
      have hl : raw41869step2Labels = raw41869step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41869step1 raw41869step1Labels permutation11 permutation7
    mixedMoment B raw41869step2 raw41869step2Labels = mixedMoment B raw41869step3 raw41869step3Labels := by
      have ha : raw41869step3 = -raw41869step2 := by apply Matrix.ext; change ∀ i j, raw41869step3 i j = -(raw41869step2 i j); unfold raw41869step3 raw41869step2; decide +kernel
      have hl : raw41869step3Labels = raw41869step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41869step3 raw41869step3Labels = mixedMoment B raw41869step4 raw41869step4Labels := by
      have ha : raw41869step4 = raw41869step3 := by apply Matrix.ext; unfold raw41869step4 raw41869step3; decide +kernel
      have hl : raw41869step3Labels = labelEmbedding6 ∘ raw41869step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41869step3 raw41869step3Labels raw41869step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4464 node4464Labels := by rfl

def raw41870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41870Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41870step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw41870step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw41870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41870 raw41870Labels = mixedMoment B node1743 node1743Labels := by
  calc
    mixedMoment B raw41870 raw41870Labels = mixedMoment B raw41870step0 raw41870step0Labels := by
      have hz : ∀ j, raw41870 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41870step0 = (fun i j => raw41870 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41870step0 raw41870; decide +kernel
      have hl : raw41870step0Labels = raw41870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41870 raw41870Labels permutation434 hz
    mixedMoment B raw41870step0 raw41870step0Labels = mixedMoment B raw41870step1 raw41870step1Labels := by
      have hz : ∀ j, raw41870step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41870step1 = (fun i j => raw41870step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41870step1 raw41870step0; decide +kernel
      have hl : raw41870step1Labels = raw41870step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41870step0 raw41870step0Labels permutation80 hz
    mixedMoment B raw41870step1 raw41870step1Labels = mixedMoment B raw41870step2 raw41870step2Labels := by
      have ha : raw41870step2 = raw41870step1 := by apply Matrix.ext; unfold raw41870step2 raw41870step1; decide +kernel
      have hl : raw41870step1Labels = labelEmbedding1 ∘ raw41870step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41870step1 raw41870step1Labels raw41870step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1743 node1743Labels := by rfl

def raw41871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41871Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41871step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41871step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw41871step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41871step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw41871step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41871step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw41871step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41871step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw41871step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41871 raw41871Labels = mixedMoment B node4375 node4375Labels := by
  calc
    mixedMoment B raw41871 raw41871Labels = mixedMoment B raw41871step0 raw41871step0Labels := by
      have hz : ∀ j, raw41871 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41871step0 = (fun i j => raw41871 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41871step0 raw41871; decide +kernel
      have hl : raw41871step0Labels = raw41871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41871 raw41871Labels permutation434 hz
    mixedMoment B raw41871step0 raw41871step0Labels = mixedMoment B raw41871step1 raw41871step1Labels := by
      have hz : ∀ j, raw41871step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41871step1 = (fun i j => raw41871step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41871step1 raw41871step0; decide +kernel
      have hl : raw41871step1Labels = raw41871step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41871step0 raw41871step0Labels permutation80 hz
    mixedMoment B raw41871step1 raw41871step1Labels = mixedMoment B raw41871step2 raw41871step2Labels := by
      have ha : raw41871step2 = (fun i j => raw41871step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41871step2 raw41871step1; decide +kernel
      have hl : raw41871step2Labels = raw41871step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41871step1 raw41871step1Labels permutation11 permutation7
    mixedMoment B raw41871step2 raw41871step2Labels = mixedMoment B raw41871step3 raw41871step3Labels := by
      have ha : raw41871step3 = -raw41871step2 := by apply Matrix.ext; change ∀ i j, raw41871step3 i j = -(raw41871step2 i j); unfold raw41871step3 raw41871step2; decide +kernel
      have hl : raw41871step3Labels = raw41871step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41871step3 raw41871step3Labels = mixedMoment B raw41871step4 raw41871step4Labels := by
      have ha : raw41871step4 = raw41871step3 := by apply Matrix.ext; unfold raw41871step4 raw41871step3; decide +kernel
      have hl : raw41871step3Labels = labelEmbedding6 ∘ raw41871step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41871step3 raw41871step3Labels raw41871step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4375 node4375Labels := by rfl

def raw41872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41872Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41872step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41872step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41872step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41872 raw41872Labels = mixedMoment B node1685 node1685Labels := by
  calc
    mixedMoment B raw41872 raw41872Labels = mixedMoment B raw41872step0 raw41872step0Labels := by
      have hz : ∀ j, raw41872 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41872step0 = (fun i j => raw41872 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41872step0 raw41872; decide +kernel
      have hl : raw41872step0Labels = raw41872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41872 raw41872Labels permutation346 hz
    mixedMoment B raw41872step0 raw41872step0Labels = mixedMoment B raw41872step1 raw41872step1Labels := by
      have ha : raw41872step1 = (fun i j => raw41872step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41872step1 raw41872step0; decide +kernel
      have hl : raw41872step1Labels = raw41872step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41872step0 raw41872step0Labels permutation38 permutation2
    mixedMoment B raw41872step1 raw41872step1Labels = mixedMoment B raw41872step2 raw41872step2Labels := by
      have ha : raw41872step2 = raw41872step1 := by apply Matrix.ext; unfold raw41872step2 raw41872step1; decide +kernel
      have hl : raw41872step1Labels = labelEmbedding1 ∘ raw41872step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41872step1 raw41872step1Labels raw41872step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1685 node1685Labels := by rfl

def raw41873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41873Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41873step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw41873step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw41873step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41873step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw41873step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41873 raw41873Labels = mixedMoment B node4336 node4336Labels := by
  calc
    mixedMoment B raw41873 raw41873Labels = mixedMoment B raw41873step0 raw41873step0Labels := by
      have hz : ∀ j, raw41873 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41873step0 = (fun i j => raw41873 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41873step0 raw41873; decide +kernel
      have hl : raw41873step0Labels = raw41873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41873 raw41873Labels permutation346 hz
    mixedMoment B raw41873step0 raw41873step0Labels = mixedMoment B raw41873step1 raw41873step1Labels := by
      have ha : raw41873step1 = (fun i j => raw41873step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41873step1 raw41873step0; decide +kernel
      have hl : raw41873step1Labels = raw41873step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41873step0 raw41873step0Labels permutation41 permutation7
    mixedMoment B raw41873step1 raw41873step1Labels = mixedMoment B raw41873step2 raw41873step2Labels := by
      have ha : raw41873step2 = -raw41873step1 := by apply Matrix.ext; change ∀ i j, raw41873step2 i j = -(raw41873step1 i j); unfold raw41873step2 raw41873step1; decide +kernel
      have hl : raw41873step2Labels = raw41873step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41873step2 raw41873step2Labels = mixedMoment B raw41873step3 raw41873step3Labels := by
      have ha : raw41873step3 = raw41873step2 := by apply Matrix.ext; unfold raw41873step3 raw41873step2; decide +kernel
      have hl : raw41873step2Labels = labelEmbedding6 ∘ raw41873step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41873step2 raw41873step2Labels raw41873step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4336 node4336Labels := by rfl

def raw41874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41874Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41874step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41874step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41874step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41874step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41874 raw41874Labels = mixedMoment B node1742 node1742Labels := by
  calc
    mixedMoment B raw41874 raw41874Labels = mixedMoment B raw41874step0 raw41874step0Labels := by
      have hz : ∀ j, raw41874 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41874step0 = (fun i j => raw41874 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41874step0 raw41874; decide +kernel
      have hl : raw41874step0Labels = raw41874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41874 raw41874Labels permutation346 hz
    mixedMoment B raw41874step0 raw41874step0Labels = mixedMoment B raw41874step1 raw41874step1Labels := by
      have ha : raw41874step1 = (fun i j => raw41874step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41874step1 raw41874step0; decide +kernel
      have hl : raw41874step1Labels = raw41874step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41874step0 raw41874step0Labels permutation36 permutation2
    mixedMoment B raw41874step1 raw41874step1Labels = mixedMoment B raw41874step2 raw41874step2Labels := by
      have ha : raw41874step2 = raw41874step1 := by apply Matrix.ext; unfold raw41874step2 raw41874step1; decide +kernel
      have hl : raw41874step1Labels = labelEmbedding1 ∘ raw41874step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41874step1 raw41874step1Labels raw41874step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1742 node1742Labels := by rfl

def raw41875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41875Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41875step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw41875step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41875step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41875step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41875step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41875step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41875 raw41875Labels = mixedMoment B node4371 node4371Labels := by
  calc
    mixedMoment B raw41875 raw41875Labels = mixedMoment B raw41875step0 raw41875step0Labels := by
      have hz : ∀ j, raw41875 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41875step0 = (fun i j => raw41875 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41875step0 raw41875; decide +kernel
      have hl : raw41875step0Labels = raw41875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41875 raw41875Labels permutation346 hz
    mixedMoment B raw41875step0 raw41875step0Labels = mixedMoment B raw41875step1 raw41875step1Labels := by
      have ha : raw41875step1 = (fun i j => raw41875step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41875step1 raw41875step0; decide +kernel
      have hl : raw41875step1Labels = raw41875step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41875step0 raw41875step0Labels permutation53 permutation7
    mixedMoment B raw41875step1 raw41875step1Labels = mixedMoment B raw41875step2 raw41875step2Labels := by
      have ha : raw41875step2 = -raw41875step1 := by apply Matrix.ext; change ∀ i j, raw41875step2 i j = -(raw41875step1 i j); unfold raw41875step2 raw41875step1; decide +kernel
      have hl : raw41875step2Labels = raw41875step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41875step2 raw41875step2Labels = mixedMoment B raw41875step3 raw41875step3Labels := by
      have ha : raw41875step3 = raw41875step2 := by apply Matrix.ext; unfold raw41875step3 raw41875step2; decide +kernel
      have hl : raw41875step2Labels = labelEmbedding6 ∘ raw41875step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41875step2 raw41875step2Labels raw41875step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4371 node4371Labels := by rfl

def raw41876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41876Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41876step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41876step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41876step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41876step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41876 raw41876Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw41876 raw41876Labels = mixedMoment B raw41876step0 raw41876step0Labels := by
      have hz : ∀ j, raw41876 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41876step0 = (fun i j => raw41876 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41876step0 raw41876; decide +kernel
      have hl : raw41876step0Labels = raw41876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41876 raw41876Labels permutation346 hz
    mixedMoment B raw41876step0 raw41876step0Labels = mixedMoment B raw41876step1 raw41876step1Labels := by
      have ha : raw41876step1 = (fun i j => raw41876step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41876step1 raw41876step0; decide +kernel
      have hl : raw41876step1Labels = raw41876step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41876step0 raw41876step0Labels permutation35 permutation2
    mixedMoment B raw41876step1 raw41876step1Labels = mixedMoment B raw41876step2 raw41876step2Labels := by
      have ha : raw41876step2 = raw41876step1 := by apply Matrix.ext; unfold raw41876step2 raw41876step1; decide +kernel
      have hl : raw41876step1Labels = labelEmbedding1 ∘ raw41876step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41876step1 raw41876step1Labels raw41876step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1744 node1744Labels := by rfl

def raw41877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41877Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41877step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw41877step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41877step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41877step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41877step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41877step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41877 raw41877Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw41877 raw41877Labels = mixedMoment B raw41877step0 raw41877step0Labels := by
      have hz : ∀ j, raw41877 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41877step0 = (fun i j => raw41877 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41877step0 raw41877; decide +kernel
      have hl : raw41877step0Labels = raw41877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41877 raw41877Labels permutation346 hz
    mixedMoment B raw41877step0 raw41877step0Labels = mixedMoment B raw41877step1 raw41877step1Labels := by
      have ha : raw41877step1 = (fun i j => raw41877step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41877step1 raw41877step0; decide +kernel
      have hl : raw41877step1Labels = raw41877step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41877step0 raw41877step0Labels permutation49 permutation7
    mixedMoment B raw41877step1 raw41877step1Labels = mixedMoment B raw41877step2 raw41877step2Labels := by
      have ha : raw41877step2 = -raw41877step1 := by apply Matrix.ext; change ∀ i j, raw41877step2 i j = -(raw41877step1 i j); unfold raw41877step2 raw41877step1; decide +kernel
      have hl : raw41877step2Labels = raw41877step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41877step2 raw41877step2Labels = mixedMoment B raw41877step3 raw41877step3Labels := by
      have ha : raw41877step3 = raw41877step2 := by apply Matrix.ext; unfold raw41877step3 raw41877step2; decide +kernel
      have hl : raw41877step2Labels = labelEmbedding6 ∘ raw41877step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41877step2 raw41877step2Labels raw41877step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4442 node4442Labels := by rfl

def raw41878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41878Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41878step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41878step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41878step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41878 raw41878Labels = mixedMoment B node1684 node1684Labels := by
  calc
    mixedMoment B raw41878 raw41878Labels = mixedMoment B raw41878step0 raw41878step0Labels := by
      have ha : raw41878step0 = (fun i j => raw41878 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41878step0 raw41878; decide +kernel
      have hl : raw41878step0Labels = raw41878Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41878 raw41878Labels permutation180 permutation2
    mixedMoment B raw41878step0 raw41878step0Labels = mixedMoment B raw41878step1 raw41878step1Labels := by
      have ha : raw41878step1 = raw41878step0 := by apply Matrix.ext; unfold raw41878step1 raw41878step0; decide +kernel
      have hl : raw41878step0Labels = labelEmbedding1 ∘ raw41878step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41878step0 raw41878step0Labels raw41878step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1684 node1684Labels := by rfl

def raw41879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41879Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw41879step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41879step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41879step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41879step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41879step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41879 raw41879Labels = mixedMoment B node4331 node4331Labels := by
  calc
    mixedMoment B raw41879 raw41879Labels = mixedMoment B raw41879step0 raw41879step0Labels := by
      have ha : raw41879step0 = (fun i j => raw41879 (permutation197 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41879step0 raw41879; decide +kernel
      have hl : raw41879step0Labels = raw41879Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41879 raw41879Labels permutation197 permutation7
    mixedMoment B raw41879step0 raw41879step0Labels = mixedMoment B raw41879step1 raw41879step1Labels := by
      have ha : raw41879step1 = -raw41879step0 := by apply Matrix.ext; change ∀ i j, raw41879step1 i j = -(raw41879step0 i j); unfold raw41879step1 raw41879step0; decide +kernel
      have hl : raw41879step1Labels = raw41879step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41879step1 raw41879step1Labels = mixedMoment B raw41879step2 raw41879step2Labels := by
      have ha : raw41879step2 = raw41879step1 := by apply Matrix.ext; unfold raw41879step2 raw41879step1; decide +kernel
      have hl : raw41879step1Labels = labelEmbedding6 ∘ raw41879step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41879step1 raw41879step1Labels raw41879step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4331 node4331Labels := by rfl

def raw41880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41880Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41880step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41880step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41880step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41880 raw41880Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw41880 raw41880Labels = mixedMoment B raw41880step0 raw41880step0Labels := by
      have hz : ∀ j, raw41880 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41880step0 = (fun i j => raw41880 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41880step0 raw41880; decide +kernel
      have hl : raw41880step0Labels = raw41880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41880 raw41880Labels permutation434 hz
    mixedMoment B raw41880step0 raw41880step0Labels = mixedMoment B raw41880step1 raw41880step1Labels := by
      have ha : raw41880step1 = (fun i j => raw41880step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41880step1 raw41880step0; decide +kernel
      have hl : raw41880step1Labels = raw41880step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41880step0 raw41880step0Labels permutation38 permutation2
    mixedMoment B raw41880step1 raw41880step1Labels = mixedMoment B raw41880step2 raw41880step2Labels := by
      have ha : raw41880step2 = raw41880step1 := by apply Matrix.ext; unfold raw41880step2 raw41880step1; decide +kernel
      have hl : raw41880step1Labels = labelEmbedding1 ∘ raw41880step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41880step1 raw41880step1Labels raw41880step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

def raw41881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41881Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41881step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw41881step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41881step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41881step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41881step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41881step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41881 raw41881Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw41881 raw41881Labels = mixedMoment B raw41881step0 raw41881step0Labels := by
      have hz : ∀ j, raw41881 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41881step0 = (fun i j => raw41881 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41881step0 raw41881; decide +kernel
      have hl : raw41881step0Labels = raw41881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41881 raw41881Labels permutation434 hz
    mixedMoment B raw41881step0 raw41881step0Labels = mixedMoment B raw41881step1 raw41881step1Labels := by
      have ha : raw41881step1 = (fun i j => raw41881step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41881step1 raw41881step0; decide +kernel
      have hl : raw41881step1Labels = raw41881step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41881step0 raw41881step0Labels permutation53 permutation7
    mixedMoment B raw41881step1 raw41881step1Labels = mixedMoment B raw41881step2 raw41881step2Labels := by
      have ha : raw41881step2 = -raw41881step1 := by apply Matrix.ext; change ∀ i j, raw41881step2 i j = -(raw41881step1 i j); unfold raw41881step2 raw41881step1; decide +kernel
      have hl : raw41881step2Labels = raw41881step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41881step2 raw41881step2Labels = mixedMoment B raw41881step3 raw41881step3Labels := by
      have ha : raw41881step3 = raw41881step2 := by apply Matrix.ext; unfold raw41881step3 raw41881step2; decide +kernel
      have hl : raw41881step2Labels = labelEmbedding6 ∘ raw41881step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41881step2 raw41881step2Labels raw41881step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4475 node4475Labels := by rfl

def raw41882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41882Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41882step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41882step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41882 raw41882Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw41882 raw41882Labels = mixedMoment B raw41882step0 raw41882step0Labels := by
      have hz : ∀ j, raw41882 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41882step0 = (fun i j => raw41882 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41882step0 raw41882; decide +kernel
      have hl : raw41882step0Labels = raw41882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41882 raw41882Labels permutation434 hz
    mixedMoment B raw41882step0 raw41882step0Labels = mixedMoment B raw41882step1 raw41882step1Labels := by
      have ha : raw41882step1 = (fun i j => raw41882step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41882step1 raw41882step0; decide +kernel
      have hl : raw41882step1Labels = raw41882step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41882step0 raw41882step0Labels permutation38 permutation2
    mixedMoment B raw41882step1 raw41882step1Labels = mixedMoment B raw41882step2 raw41882step2Labels := by
      have ha : raw41882step2 = raw41882step1 := by apply Matrix.ext; unfold raw41882step2 raw41882step1; decide +kernel
      have hl : raw41882step1Labels = labelEmbedding1 ∘ raw41882step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41882step1 raw41882step1Labels raw41882step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw41883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41883Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41883step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw41883step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41883step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41883step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41883step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41883 raw41883Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw41883 raw41883Labels = mixedMoment B raw41883step0 raw41883step0Labels := by
      have hz : ∀ j, raw41883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41883step0 = (fun i j => raw41883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41883step0 raw41883; decide +kernel
      have hl : raw41883step0Labels = raw41883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41883 raw41883Labels permutation434 hz
    mixedMoment B raw41883step0 raw41883step0Labels = mixedMoment B raw41883step1 raw41883step1Labels := by
      have ha : raw41883step1 = (fun i j => raw41883step0 (permutation47 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41883step1 raw41883step0; decide +kernel
      have hl : raw41883step1Labels = raw41883step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41883step0 raw41883step0Labels permutation47 permutation7
    mixedMoment B raw41883step1 raw41883step1Labels = mixedMoment B raw41883step2 raw41883step2Labels := by
      have ha : raw41883step2 = -raw41883step1 := by apply Matrix.ext; change ∀ i j, raw41883step2 i j = -(raw41883step1 i j); unfold raw41883step2 raw41883step1; decide +kernel
      have hl : raw41883step2Labels = raw41883step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41883step2 raw41883step2Labels = mixedMoment B raw41883step3 raw41883step3Labels := by
      have ha : raw41883step3 = raw41883step2 := by apply Matrix.ext; unfold raw41883step3 raw41883step2; decide +kernel
      have hl : raw41883step2Labels = labelEmbedding6 ∘ raw41883step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41883step2 raw41883step2Labels raw41883step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw41884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41884Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41884step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41884step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw41884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41884 raw41884Labels = mixedMoment B node1712 node1712Labels := by
  calc
    mixedMoment B raw41884 raw41884Labels = mixedMoment B raw41884step0 raw41884step0Labels := by
      have hz : ∀ j, raw41884 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41884step0 = (fun i j => raw41884 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41884step0 raw41884; decide +kernel
      have hl : raw41884step0Labels = raw41884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41884 raw41884Labels permutation434 hz
    mixedMoment B raw41884step0 raw41884step0Labels = mixedMoment B raw41884step1 raw41884step1Labels := by
      have ha : raw41884step1 = (fun i j => raw41884step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41884step1 raw41884step0; decide +kernel
      have hl : raw41884step1Labels = raw41884step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41884step0 raw41884step0Labels permutation38 permutation2
    mixedMoment B raw41884step1 raw41884step1Labels = mixedMoment B raw41884step2 raw41884step2Labels := by
      have ha : raw41884step2 = raw41884step1 := by apply Matrix.ext; unfold raw41884step2 raw41884step1; decide +kernel
      have hl : raw41884step1Labels = labelEmbedding1 ∘ raw41884step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41884step1 raw41884step1Labels raw41884step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1712 node1712Labels := by rfl

def raw41885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41885Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41885step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw41885step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41885step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41885step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41885step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41885 raw41885Labels = mixedMoment B node4368 node4368Labels := by
  calc
    mixedMoment B raw41885 raw41885Labels = mixedMoment B raw41885step0 raw41885step0Labels := by
      have hz : ∀ j, raw41885 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41885step0 = (fun i j => raw41885 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41885step0 raw41885; decide +kernel
      have hl : raw41885step0Labels = raw41885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41885 raw41885Labels permutation434 hz
    mixedMoment B raw41885step0 raw41885step0Labels = mixedMoment B raw41885step1 raw41885step1Labels := by
      have ha : raw41885step1 = (fun i j => raw41885step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41885step1 raw41885step0; decide +kernel
      have hl : raw41885step1Labels = raw41885step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41885step0 raw41885step0Labels permutation46 permutation7
    mixedMoment B raw41885step1 raw41885step1Labels = mixedMoment B raw41885step2 raw41885step2Labels := by
      have ha : raw41885step2 = -raw41885step1 := by apply Matrix.ext; change ∀ i j, raw41885step2 i j = -(raw41885step1 i j); unfold raw41885step2 raw41885step1; decide +kernel
      have hl : raw41885step2Labels = raw41885step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41885step2 raw41885step2Labels = mixedMoment B raw41885step3 raw41885step3Labels := by
      have ha : raw41885step3 = raw41885step2 := by apply Matrix.ext; unfold raw41885step3 raw41885step2; decide +kernel
      have hl : raw41885step2Labels = labelEmbedding6 ∘ raw41885step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41885step2 raw41885step2Labels raw41885step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4368 node4368Labels := by rfl

def raw41886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41886Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41886step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41886 raw41886Labels = mixedMoment B node1667 node1667Labels := by
  calc
    mixedMoment B raw41886 raw41886Labels = mixedMoment B raw41886step0 raw41886step0Labels := by
      have ha : raw41886step0 = (fun i j => raw41886 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41886step0 raw41886; decide +kernel
      have hl : raw41886step0Labels = raw41886Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41886 raw41886Labels permutation206 permutation2
    mixedMoment B raw41886step0 raw41886step0Labels = mixedMoment B raw41886step1 raw41886step1Labels := by
      have ha : raw41886step1 = raw41886step0 := by apply Matrix.ext; unfold raw41886step1 raw41886step0; decide +kernel
      have hl : raw41886step0Labels = labelEmbedding1 ∘ raw41886step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41886step0 raw41886step0Labels raw41886step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1667 node1667Labels := by rfl

def raw41887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41887Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw41887step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41887step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41887step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41887step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41887 raw41887Labels = mixedMoment B node4328 node4328Labels := by
  calc
    mixedMoment B raw41887 raw41887Labels = mixedMoment B raw41887step0 raw41887step0Labels := by
      have ha : raw41887step0 = (fun i j => raw41887 (permutation214 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41887step0 raw41887; decide +kernel
      have hl : raw41887step0Labels = raw41887Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41887 raw41887Labels permutation214 permutation7
    mixedMoment B raw41887step0 raw41887step0Labels = mixedMoment B raw41887step1 raw41887step1Labels := by
      have ha : raw41887step1 = -raw41887step0 := by apply Matrix.ext; change ∀ i j, raw41887step1 i j = -(raw41887step0 i j); unfold raw41887step1 raw41887step0; decide +kernel
      have hl : raw41887step1Labels = raw41887step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41887step1 raw41887step1Labels = mixedMoment B raw41887step2 raw41887step2Labels := by
      have ha : raw41887step2 = raw41887step1 := by apply Matrix.ext; unfold raw41887step2 raw41887step1; decide +kernel
      have hl : raw41887step1Labels = labelEmbedding6 ∘ raw41887step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41887step1 raw41887step1Labels raw41887step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4328 node4328Labels := by rfl

def raw41888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41888Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41888step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41888step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41888 raw41888Labels = mixedMoment B node1711 node1711Labels := by
  calc
    mixedMoment B raw41888 raw41888Labels = mixedMoment B raw41888step0 raw41888step0Labels := by
      have ha : raw41888step0 = (fun i j => raw41888 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41888step0 raw41888; decide +kernel
      have hl : raw41888step0Labels = raw41888Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41888 raw41888Labels permutation180 permutation2
    mixedMoment B raw41888step0 raw41888step0Labels = mixedMoment B raw41888step1 raw41888step1Labels := by
      have ha : raw41888step1 = raw41888step0 := by apply Matrix.ext; unfold raw41888step1 raw41888step0; decide +kernel
      have hl : raw41888step0Labels = labelEmbedding1 ∘ raw41888step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41888step0 raw41888step0Labels raw41888step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1711 node1711Labels := by rfl

def raw41889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41889Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41889step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41889step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41889step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41889 raw41889Labels = mixedMoment B node4366 node4366Labels := by
  calc
    mixedMoment B raw41889 raw41889Labels = mixedMoment B raw41889step0 raw41889step0Labels := by
      have ha : raw41889step0 = (fun i j => raw41889 (permutation255 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41889step0 raw41889; decide +kernel
      have hl : raw41889step0Labels = raw41889Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41889 raw41889Labels permutation255 permutation7
    mixedMoment B raw41889step0 raw41889step0Labels = mixedMoment B raw41889step1 raw41889step1Labels := by
      have ha : raw41889step1 = -raw41889step0 := by apply Matrix.ext; change ∀ i j, raw41889step1 i j = -(raw41889step0 i j); unfold raw41889step1 raw41889step0; decide +kernel
      have hl : raw41889step1Labels = raw41889step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41889step1 raw41889step1Labels = mixedMoment B raw41889step2 raw41889step2Labels := by
      have ha : raw41889step2 = raw41889step1 := by apply Matrix.ext; unfold raw41889step2 raw41889step1; decide +kernel
      have hl : raw41889step1Labels = labelEmbedding6 ∘ raw41889step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41889step1 raw41889step1Labels raw41889step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4366 node4366Labels := by rfl

def raw41890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41890Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41890step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41890 raw41890Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw41890 raw41890Labels = mixedMoment B raw41890step0 raw41890step0Labels := by
      have ha : raw41890step0 = (fun i j => raw41890 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41890step0 raw41890; decide +kernel
      have hl : raw41890step0Labels = raw41890Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41890 raw41890Labels permutation179 permutation2
    mixedMoment B raw41890step0 raw41890step0Labels = mixedMoment B raw41890step1 raw41890step1Labels := by
      have ha : raw41890step1 = raw41890step0 := by apply Matrix.ext; unfold raw41890step1 raw41890step0; decide +kernel
      have hl : raw41890step0Labels = labelEmbedding1 ∘ raw41890step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41890step0 raw41890step0Labels raw41890step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

def raw41891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41891Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw41891step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41891step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41891step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw41891step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41891 raw41891Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw41891 raw41891Labels = mixedMoment B raw41891step0 raw41891step0Labels := by
      have ha : raw41891step0 = (fun i j => raw41891 (permutation243 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41891step0 raw41891; decide +kernel
      have hl : raw41891step0Labels = raw41891Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41891 raw41891Labels permutation243 permutation7
    mixedMoment B raw41891step0 raw41891step0Labels = mixedMoment B raw41891step1 raw41891step1Labels := by
      have ha : raw41891step1 = -raw41891step0 := by apply Matrix.ext; change ∀ i j, raw41891step1 i j = -(raw41891step0 i j); unfold raw41891step1 raw41891step0; decide +kernel
      have hl : raw41891step1Labels = raw41891step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41891step1 raw41891step1Labels = mixedMoment B raw41891step2 raw41891step2Labels := by
      have ha : raw41891step2 = raw41891step1 := by apply Matrix.ext; unfold raw41891step2 raw41891step1; decide +kernel
      have hl : raw41891step1Labels = labelEmbedding6 ∘ raw41891step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41891step1 raw41891step1Labels raw41891step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4439 node4439Labels := by rfl

def raw41892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41892Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41892step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41892step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw41892step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41892step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw41892step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41892 raw41892Labels = mixedMoment B node1740 node1740Labels := by
  calc
    mixedMoment B raw41892 raw41892Labels = mixedMoment B raw41892step0 raw41892step0Labels := by
      have hz : ∀ j, raw41892 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41892step0 = (fun i j => raw41892 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41892step0 raw41892; decide +kernel
      have hl : raw41892step0Labels = raw41892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41892 raw41892Labels permutation434 hz
    mixedMoment B raw41892step0 raw41892step0Labels = mixedMoment B raw41892step1 raw41892step1Labels := by
      have hz : ∀ j, raw41892step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41892step1 = (fun i j => raw41892step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41892step1 raw41892step0; decide +kernel
      have hl : raw41892step1Labels = raw41892step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41892step0 raw41892step0Labels permutation80 hz
    mixedMoment B raw41892step1 raw41892step1Labels = mixedMoment B raw41892step2 raw41892step2Labels := by
      have ha : raw41892step2 = raw41892step1 := by apply Matrix.ext; unfold raw41892step2 raw41892step1; decide +kernel
      have hl : raw41892step1Labels = labelEmbedding1 ∘ raw41892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41892step1 raw41892step1Labels raw41892step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1740 node1740Labels := by rfl

def raw41893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41893Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41893step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw41893step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41893step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw41893step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41893step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw41893step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41893step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw41893step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41893 raw41893Labels = mixedMoment B node4480 node4480Labels := by
  calc
    mixedMoment B raw41893 raw41893Labels = mixedMoment B raw41893step0 raw41893step0Labels := by
      have hz : ∀ j, raw41893 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41893step0 = (fun i j => raw41893 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41893step0 raw41893; decide +kernel
      have hl : raw41893step0Labels = raw41893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41893 raw41893Labels permutation434 hz
    mixedMoment B raw41893step0 raw41893step0Labels = mixedMoment B raw41893step1 raw41893step1Labels := by
      have hz : ∀ j, raw41893step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41893step1 = (fun i j => raw41893step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41893step1 raw41893step0; decide +kernel
      have hl : raw41893step1Labels = raw41893step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41893step0 raw41893step0Labels permutation80 hz
    mixedMoment B raw41893step1 raw41893step1Labels = mixedMoment B raw41893step2 raw41893step2Labels := by
      have ha : raw41893step2 = (fun i j => raw41893step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41893step2 raw41893step1; decide +kernel
      have hl : raw41893step2Labels = raw41893step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41893step1 raw41893step1Labels permutation12 permutation7
    mixedMoment B raw41893step2 raw41893step2Labels = mixedMoment B raw41893step3 raw41893step3Labels := by
      have ha : raw41893step3 = -raw41893step2 := by apply Matrix.ext; change ∀ i j, raw41893step3 i j = -(raw41893step2 i j); unfold raw41893step3 raw41893step2; decide +kernel
      have hl : raw41893step3Labels = raw41893step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41893step3 raw41893step3Labels = mixedMoment B raw41893step4 raw41893step4Labels := by
      have ha : raw41893step4 = raw41893step3 := by apply Matrix.ext; unfold raw41893step4 raw41893step3; decide +kernel
      have hl : raw41893step3Labels = labelEmbedding6 ∘ raw41893step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41893step3 raw41893step3Labels raw41893step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4480 node4480Labels := by rfl

def raw41894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41894Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41894step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw41894step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41894step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw41894step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41894 raw41894Labels = mixedMoment B node1735 node1735Labels := by
  calc
    mixedMoment B raw41894 raw41894Labels = mixedMoment B raw41894step0 raw41894step0Labels := by
      have hz : ∀ j, raw41894 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41894step0 = (fun i j => raw41894 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41894step0 raw41894; decide +kernel
      have hl : raw41894step0Labels = raw41894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41894 raw41894Labels permutation434 hz
    mixedMoment B raw41894step0 raw41894step0Labels = mixedMoment B raw41894step1 raw41894step1Labels := by
      have hz : ∀ j, raw41894step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41894step1 = (fun i j => raw41894step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41894step1 raw41894step0; decide +kernel
      have hl : raw41894step1Labels = raw41894step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41894step0 raw41894step0Labels permutation80 hz
    mixedMoment B raw41894step1 raw41894step1Labels = mixedMoment B raw41894step2 raw41894step2Labels := by
      have ha : raw41894step2 = raw41894step1 := by apply Matrix.ext; unfold raw41894step2 raw41894step1; decide +kernel
      have hl : raw41894step1Labels = labelEmbedding1 ∘ raw41894step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41894step1 raw41894step1Labels raw41894step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1735 node1735Labels := by rfl

def raw41895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41895Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41895step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw41895step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41895step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw41895step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41895step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41895step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41895step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41895step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41895 raw41895Labels = mixedMoment B node4373 node4373Labels := by
  calc
    mixedMoment B raw41895 raw41895Labels = mixedMoment B raw41895step0 raw41895step0Labels := by
      have hz : ∀ j, raw41895 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41895step0 = (fun i j => raw41895 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41895step0 raw41895; decide +kernel
      have hl : raw41895step0Labels = raw41895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41895 raw41895Labels permutation434 hz
    mixedMoment B raw41895step0 raw41895step0Labels = mixedMoment B raw41895step1 raw41895step1Labels := by
      have hz : ∀ j, raw41895step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41895step1 = (fun i j => raw41895step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41895step1 raw41895step0; decide +kernel
      have hl : raw41895step1Labels = raw41895step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41895step0 raw41895step0Labels permutation80 hz
    mixedMoment B raw41895step1 raw41895step1Labels = mixedMoment B raw41895step2 raw41895step2Labels := by
      have ha : raw41895step2 = (fun i j => raw41895step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41895step2 raw41895step1; decide +kernel
      have hl : raw41895step2Labels = raw41895step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41895step1 raw41895step1Labels permutation10 permutation7
    mixedMoment B raw41895step2 raw41895step2Labels = mixedMoment B raw41895step3 raw41895step3Labels := by
      have ha : raw41895step3 = -raw41895step2 := by apply Matrix.ext; change ∀ i j, raw41895step3 i j = -(raw41895step2 i j); unfold raw41895step3 raw41895step2; decide +kernel
      have hl : raw41895step3Labels = raw41895step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41895step3 raw41895step3Labels = mixedMoment B raw41895step4 raw41895step4Labels := by
      have ha : raw41895step4 = raw41895step3 := by apply Matrix.ext; unfold raw41895step4 raw41895step3; decide +kernel
      have hl : raw41895step3Labels = labelEmbedding6 ∘ raw41895step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41895step3 raw41895step3Labels raw41895step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4373 node4373Labels := by rfl

def raw41896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41896Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41896step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41896step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41896step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41896 raw41896Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw41896 raw41896Labels = mixedMoment B raw41896step0 raw41896step0Labels := by
      have hz : ∀ j, raw41896 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41896step0 = (fun i j => raw41896 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41896step0 raw41896; decide +kernel
      have hl : raw41896step0Labels = raw41896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41896 raw41896Labels permutation346 hz
    mixedMoment B raw41896step0 raw41896step0Labels = mixedMoment B raw41896step1 raw41896step1Labels := by
      have ha : raw41896step1 = (fun i j => raw41896step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41896step1 raw41896step0; decide +kernel
      have hl : raw41896step1Labels = raw41896step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41896step0 raw41896step0Labels permutation38 permutation2
    mixedMoment B raw41896step1 raw41896step1Labels = mixedMoment B raw41896step2 raw41896step2Labels := by
      have ha : raw41896step2 = raw41896step1 := by apply Matrix.ext; unfold raw41896step2 raw41896step1; decide +kernel
      have hl : raw41896step1Labels = labelEmbedding1 ∘ raw41896step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41896step1 raw41896step1Labels raw41896step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1679 node1679Labels := by rfl

def raw41897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41897Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41897step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw41897step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41897step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41897step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41897step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41897 raw41897Labels = mixedMoment B node4334 node4334Labels := by
  calc
    mixedMoment B raw41897 raw41897Labels = mixedMoment B raw41897step0 raw41897step0Labels := by
      have hz : ∀ j, raw41897 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41897step0 = (fun i j => raw41897 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41897step0 raw41897; decide +kernel
      have hl : raw41897step0Labels = raw41897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41897 raw41897Labels permutation346 hz
    mixedMoment B raw41897step0 raw41897step0Labels = mixedMoment B raw41897step1 raw41897step1Labels := by
      have ha : raw41897step1 = (fun i j => raw41897step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41897step1 raw41897step0; decide +kernel
      have hl : raw41897step1Labels = raw41897step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41897step0 raw41897step0Labels permutation40 permutation7
    mixedMoment B raw41897step1 raw41897step1Labels = mixedMoment B raw41897step2 raw41897step2Labels := by
      have ha : raw41897step2 = -raw41897step1 := by apply Matrix.ext; change ∀ i j, raw41897step2 i j = -(raw41897step1 i j); unfold raw41897step2 raw41897step1; decide +kernel
      have hl : raw41897step2Labels = raw41897step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41897step2 raw41897step2Labels = mixedMoment B raw41897step3 raw41897step3Labels := by
      have ha : raw41897step3 = raw41897step2 := by apply Matrix.ext; unfold raw41897step3 raw41897step2; decide +kernel
      have hl : raw41897step2Labels = labelEmbedding6 ∘ raw41897step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41897step2 raw41897step2Labels raw41897step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4334 node4334Labels := by rfl

def raw41898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41898Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41898step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41898step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41898 raw41898Labels = mixedMoment B node1734 node1734Labels := by
  calc
    mixedMoment B raw41898 raw41898Labels = mixedMoment B raw41898step0 raw41898step0Labels := by
      have hz : ∀ j, raw41898 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41898step0 = (fun i j => raw41898 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41898step0 raw41898; decide +kernel
      have hl : raw41898step0Labels = raw41898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41898 raw41898Labels permutation346 hz
    mixedMoment B raw41898step0 raw41898step0Labels = mixedMoment B raw41898step1 raw41898step1Labels := by
      have ha : raw41898step1 = (fun i j => raw41898step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41898step1 raw41898step0; decide +kernel
      have hl : raw41898step1Labels = raw41898step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41898step0 raw41898step0Labels permutation37 permutation2
    mixedMoment B raw41898step1 raw41898step1Labels = mixedMoment B raw41898step2 raw41898step2Labels := by
      have ha : raw41898step2 = raw41898step1 := by apply Matrix.ext; unfold raw41898step2 raw41898step1; decide +kernel
      have hl : raw41898step1Labels = labelEmbedding1 ∘ raw41898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41898step1 raw41898step1Labels raw41898step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1734 node1734Labels := by rfl

def raw41899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41899Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41899step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw41899step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41899step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41899step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41899step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41899 raw41899Labels = mixedMoment B node4372 node4372Labels := by
  calc
    mixedMoment B raw41899 raw41899Labels = mixedMoment B raw41899step0 raw41899step0Labels := by
      have hz : ∀ j, raw41899 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41899step0 = (fun i j => raw41899 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41899step0 raw41899; decide +kernel
      have hl : raw41899step0Labels = raw41899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41899 raw41899Labels permutation346 hz
    mixedMoment B raw41899step0 raw41899step0Labels = mixedMoment B raw41899step1 raw41899step1Labels := by
      have ha : raw41899step1 = (fun i j => raw41899step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41899step1 raw41899step0; decide +kernel
      have hl : raw41899step1Labels = raw41899step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41899step0 raw41899step0Labels permutation54 permutation7
    mixedMoment B raw41899step1 raw41899step1Labels = mixedMoment B raw41899step2 raw41899step2Labels := by
      have ha : raw41899step2 = -raw41899step1 := by apply Matrix.ext; change ∀ i j, raw41899step2 i j = -(raw41899step1 i j); unfold raw41899step2 raw41899step1; decide +kernel
      have hl : raw41899step2Labels = raw41899step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41899step2 raw41899step2Labels = mixedMoment B raw41899step3 raw41899step3Labels := by
      have ha : raw41899step3 = raw41899step2 := by apply Matrix.ext; unfold raw41899step3 raw41899step2; decide +kernel
      have hl : raw41899step2Labels = labelEmbedding6 ∘ raw41899step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41899step2 raw41899step2Labels raw41899step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4372 node4372Labels := by rfl

def raw41900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41900Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41900step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41900step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41900step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41900step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41900 raw41900Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw41900 raw41900Labels = mixedMoment B raw41900step0 raw41900step0Labels := by
      have hz : ∀ j, raw41900 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41900step0 = (fun i j => raw41900 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41900step0 raw41900; decide +kernel
      have hl : raw41900step0Labels = raw41900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41900 raw41900Labels permutation346 hz
    mixedMoment B raw41900step0 raw41900step0Labels = mixedMoment B raw41900step1 raw41900step1Labels := by
      have ha : raw41900step1 = (fun i j => raw41900step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41900step1 raw41900step0; decide +kernel
      have hl : raw41900step1Labels = raw41900step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41900step0 raw41900step0Labels permutation35 permutation2
    mixedMoment B raw41900step1 raw41900step1Labels = mixedMoment B raw41900step2 raw41900step2Labels := by
      have ha : raw41900step2 = raw41900step1 := by apply Matrix.ext; unfold raw41900step2 raw41900step1; decide +kernel
      have hl : raw41900step1Labels = labelEmbedding1 ∘ raw41900step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41900step1 raw41900step1Labels raw41900step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1736 node1736Labels := by rfl

def raw41901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41901Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41901step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw41901step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41901step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41901step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41901step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41901step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41901 raw41901Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw41901 raw41901Labels = mixedMoment B raw41901step0 raw41901step0Labels := by
      have hz : ∀ j, raw41901 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41901step0 = (fun i j => raw41901 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41901step0 raw41901; decide +kernel
      have hl : raw41901step0Labels = raw41901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41901 raw41901Labels permutation346 hz
    mixedMoment B raw41901step0 raw41901step0Labels = mixedMoment B raw41901step1 raw41901step1Labels := by
      have ha : raw41901step1 = (fun i j => raw41901step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41901step1 raw41901step0; decide +kernel
      have hl : raw41901step1Labels = raw41901step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41901step0 raw41901step0Labels permutation48 permutation7
    mixedMoment B raw41901step1 raw41901step1Labels = mixedMoment B raw41901step2 raw41901step2Labels := by
      have ha : raw41901step2 = -raw41901step1 := by apply Matrix.ext; change ∀ i j, raw41901step2 i j = -(raw41901step1 i j); unfold raw41901step2 raw41901step1; decide +kernel
      have hl : raw41901step2Labels = raw41901step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41901step2 raw41901step2Labels = mixedMoment B raw41901step3 raw41901step3Labels := by
      have ha : raw41901step3 = raw41901step2 := by apply Matrix.ext; unfold raw41901step3 raw41901step2; decide +kernel
      have hl : raw41901step2Labels = labelEmbedding6 ∘ raw41901step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41901step2 raw41901step2Labels raw41901step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4444 node4444Labels := by rfl

def raw41902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41902Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41902step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41902 raw41902Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw41902 raw41902Labels = mixedMoment B raw41902step0 raw41902step0Labels := by
      have ha : raw41902step0 = (fun i j => raw41902 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41902step0 raw41902; decide +kernel
      have hl : raw41902step0Labels = raw41902Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41902 raw41902Labels permutation181 permutation2
    mixedMoment B raw41902step0 raw41902step0Labels = mixedMoment B raw41902step1 raw41902step1Labels := by
      have ha : raw41902step1 = raw41902step0 := by apply Matrix.ext; unfold raw41902step1 raw41902step0; decide +kernel
      have hl : raw41902step0Labels = labelEmbedding1 ∘ raw41902step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41902step0 raw41902step0Labels raw41902step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1678 node1678Labels := by rfl

def raw41903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41903Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw41903step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41903step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41903step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41903step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41903 raw41903Labels = mixedMoment B node4332 node4332Labels := by
  calc
    mixedMoment B raw41903 raw41903Labels = mixedMoment B raw41903step0 raw41903step0Labels := by
      have ha : raw41903step0 = (fun i j => raw41903 (permutation198 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41903step0 raw41903; decide +kernel
      have hl : raw41903step0Labels = raw41903Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41903 raw41903Labels permutation198 permutation7
    mixedMoment B raw41903step0 raw41903step0Labels = mixedMoment B raw41903step1 raw41903step1Labels := by
      have ha : raw41903step1 = -raw41903step0 := by apply Matrix.ext; change ∀ i j, raw41903step1 i j = -(raw41903step0 i j); unfold raw41903step1 raw41903step0; decide +kernel
      have hl : raw41903step1Labels = raw41903step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41903step1 raw41903step1Labels = mixedMoment B raw41903step2 raw41903step2Labels := by
      have ha : raw41903step2 = raw41903step1 := by apply Matrix.ext; unfold raw41903step2 raw41903step1; decide +kernel
      have hl : raw41903step1Labels = labelEmbedding6 ∘ raw41903step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41903step1 raw41903step1Labels raw41903step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4332 node4332Labels := by rfl

def raw41904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41904Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41904 raw41904Labels = mixedMoment B node1699 node1699Labels := by
  calc
    mixedMoment B raw41904 raw41904Labels = mixedMoment B raw41904step0 raw41904step0Labels := by
      have ha : raw41904step0 = raw41904 := by apply Matrix.ext; unfold raw41904step0 raw41904; decide +kernel
      have hl : raw41904Labels = labelEmbedding1 ∘ raw41904step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41904 raw41904Labels raw41904step0Labels labelEmbedding1 hl
    _ = mixedMoment B node1699 node1699Labels := by rfl

def raw41905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41905Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw41905step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41905step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41905step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41905step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41905 raw41905Labels = mixedMoment B node4473 node4473Labels := by
  calc
    mixedMoment B raw41905 raw41905Labels = mixedMoment B raw41905step0 raw41905step0Labels := by
      have ha : raw41905step0 = (fun i j => raw41905 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41905step0 raw41905; decide +kernel
      have hl : raw41905step0Labels = raw41905Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41905 raw41905Labels permutation246 permutation7
    mixedMoment B raw41905step0 raw41905step0Labels = mixedMoment B raw41905step1 raw41905step1Labels := by
      have ha : raw41905step1 = -raw41905step0 := by apply Matrix.ext; change ∀ i j, raw41905step1 i j = -(raw41905step0 i j); unfold raw41905step1 raw41905step0; decide +kernel
      have hl : raw41905step1Labels = raw41905step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41905step1 raw41905step1Labels = mixedMoment B raw41905step2 raw41905step2Labels := by
      have ha : raw41905step2 = raw41905step1 := by apply Matrix.ext; unfold raw41905step2 raw41905step1; decide +kernel
      have hl : raw41905step1Labels = labelEmbedding6 ∘ raw41905step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41905step1 raw41905step1Labels raw41905step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4473 node4473Labels := by rfl

def raw41906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41906Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41906 raw41906Labels = mixedMoment B node1697 node1697Labels := by
  calc
    mixedMoment B raw41906 raw41906Labels = mixedMoment B raw41906step0 raw41906step0Labels := by
      have ha : raw41906step0 = raw41906 := by apply Matrix.ext; unfold raw41906step0 raw41906; decide +kernel
      have hl : raw41906Labels = labelEmbedding1 ∘ raw41906step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41906 raw41906Labels raw41906step0Labels labelEmbedding1 hl
    _ = mixedMoment B node1697 node1697Labels := by rfl

def raw41907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41907Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw41907step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41907step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41907step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41907step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41907step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41907 raw41907Labels = mixedMoment B node4363 node4363Labels := by
  calc
    mixedMoment B raw41907 raw41907Labels = mixedMoment B raw41907step0 raw41907step0Labels := by
      have ha : raw41907step0 = (fun i j => raw41907 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41907step0 raw41907; decide +kernel
      have hl : raw41907step0Labels = raw41907Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41907 raw41907Labels permutation224 permutation7
    mixedMoment B raw41907step0 raw41907step0Labels = mixedMoment B raw41907step1 raw41907step1Labels := by
      have ha : raw41907step1 = -raw41907step0 := by apply Matrix.ext; change ∀ i j, raw41907step1 i j = -(raw41907step0 i j); unfold raw41907step1 raw41907step0; decide +kernel
      have hl : raw41907step1Labels = raw41907step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41907step1 raw41907step1Labels = mixedMoment B raw41907step2 raw41907step2Labels := by
      have ha : raw41907step2 = raw41907step1 := by apply Matrix.ext; unfold raw41907step2 raw41907step1; decide +kernel
      have hl : raw41907step1Labels = labelEmbedding6 ∘ raw41907step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41907step1 raw41907step1Labels raw41907step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4363 node4363Labels := by rfl

def raw41908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41908Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41908step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41908 raw41908Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw41908 raw41908Labels = mixedMoment B raw41908step0 raw41908step0Labels := by
      have hz : ∀ j, raw41908 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41908step0 = (fun i j => raw41908 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41908step0 raw41908; decide +kernel
      have hl : raw41908step0Labels = raw41908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41908 raw41908Labels permutation434 hz
    mixedMoment B raw41908step0 raw41908step0Labels = mixedMoment B raw41908step1 raw41908step1Labels := by
      have ha : raw41908step1 = raw41908step0 := by apply Matrix.ext; unfold raw41908step1 raw41908step0; decide +kernel
      have hl : raw41908step0Labels = labelEmbedding1 ∘ raw41908step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41908step0 raw41908step0Labels raw41908step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1709 node1709Labels := by rfl

def raw41909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw41909Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41909step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw41909step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41909step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41909step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41909step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41909step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41909 raw41909Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw41909 raw41909Labels = mixedMoment B raw41909step0 raw41909step0Labels := by
      have hz : ∀ j, raw41909 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41909step0 = (fun i j => raw41909 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41909step0 raw41909; decide +kernel
      have hl : raw41909step0Labels = raw41909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41909 raw41909Labels permutation434 hz
    mixedMoment B raw41909step0 raw41909step0Labels = mixedMoment B raw41909step1 raw41909step1Labels := by
      have ha : raw41909step1 = (fun i j => raw41909step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41909step1 raw41909step0; decide +kernel
      have hl : raw41909step1Labels = raw41909step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41909step0 raw41909step0Labels permutation50 permutation7
    mixedMoment B raw41909step1 raw41909step1Labels = mixedMoment B raw41909step2 raw41909step2Labels := by
      have ha : raw41909step2 = -raw41909step1 := by apply Matrix.ext; change ∀ i j, raw41909step2 i j = -(raw41909step1 i j); unfold raw41909step2 raw41909step1; decide +kernel
      have hl : raw41909step2Labels = raw41909step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41909step2 raw41909step2Labels = mixedMoment B raw41909step3 raw41909step3Labels := by
      have ha : raw41909step3 = raw41909step2 := by apply Matrix.ext; unfold raw41909step3 raw41909step2; decide +kernel
      have hl : raw41909step2Labels = labelEmbedding6 ∘ raw41909step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41909step2 raw41909step2Labels raw41909step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4474 node4474Labels := by rfl

def raw41910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41910Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41910step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41910 raw41910Labels = mixedMoment B node1704 node1704Labels := by
  calc
    mixedMoment B raw41910 raw41910Labels = mixedMoment B raw41910step0 raw41910step0Labels := by
      have hz : ∀ j, raw41910 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41910step0 = (fun i j => raw41910 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41910step0 raw41910; decide +kernel
      have hl : raw41910step0Labels = raw41910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41910 raw41910Labels permutation434 hz
    mixedMoment B raw41910step0 raw41910step0Labels = mixedMoment B raw41910step1 raw41910step1Labels := by
      have ha : raw41910step1 = raw41910step0 := by apply Matrix.ext; unfold raw41910step1 raw41910step0; decide +kernel
      have hl : raw41910step0Labels = labelEmbedding1 ∘ raw41910step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41910step0 raw41910step0Labels raw41910step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1704 node1704Labels := by rfl

def raw41911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw41911Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw41911step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw41911step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41911step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41911step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41911step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41911step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41911 raw41911Labels = mixedMoment B node4365 node4365Labels := by
  calc
    mixedMoment B raw41911 raw41911Labels = mixedMoment B raw41911step0 raw41911step0Labels := by
      have hz : ∀ j, raw41911 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41911step0 = (fun i j => raw41911 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41911step0 raw41911; decide +kernel
      have hl : raw41911step0Labels = raw41911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41911 raw41911Labels permutation434 hz
    mixedMoment B raw41911step0 raw41911step0Labels = mixedMoment B raw41911step1 raw41911step1Labels := by
      have ha : raw41911step1 = (fun i j => raw41911step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41911step1 raw41911step0; decide +kernel
      have hl : raw41911step1Labels = raw41911step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41911step0 raw41911step0Labels permutation44 permutation7
    mixedMoment B raw41911step1 raw41911step1Labels = mixedMoment B raw41911step2 raw41911step2Labels := by
      have ha : raw41911step2 = -raw41911step1 := by apply Matrix.ext; change ∀ i j, raw41911step2 i j = -(raw41911step1 i j); unfold raw41911step2 raw41911step1; decide +kernel
      have hl : raw41911step2Labels = raw41911step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41911step2 raw41911step2Labels = mixedMoment B raw41911step3 raw41911step3Labels := by
      have ha : raw41911step3 = raw41911step2 := by apply Matrix.ext; unfold raw41911step3 raw41911step2; decide +kernel
      have hl : raw41911step2Labels = labelEmbedding6 ∘ raw41911step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41911step2 raw41911step2Labels raw41911step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4365 node4365Labels := by rfl

def raw41912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41912Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41912step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41912 raw41912Labels = mixedMoment B node1703 node1703Labels := by
  calc
    mixedMoment B raw41912 raw41912Labels = mixedMoment B raw41912step0 raw41912step0Labels := by
      have ha : raw41912step0 = (fun i j => raw41912 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41912step0 raw41912; decide +kernel
      have hl : raw41912step0Labels = raw41912Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41912 raw41912Labels permutation157 permutation2
    mixedMoment B raw41912step0 raw41912step0Labels = mixedMoment B raw41912step1 raw41912step1Labels := by
      have ha : raw41912step1 = raw41912step0 := by apply Matrix.ext; unfold raw41912step1 raw41912step0; decide +kernel
      have hl : raw41912step0Labels = labelEmbedding1 ∘ raw41912step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41912step0 raw41912step0Labels raw41912step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1703 node1703Labels := by rfl

def raw41913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41913Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw41913step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41913step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41913step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41913step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41913 raw41913Labels = mixedMoment B node4364 node4364Labels := by
  calc
    mixedMoment B raw41913 raw41913Labels = mixedMoment B raw41913step0 raw41913step0Labels := by
      have ha : raw41913step0 = (fun i j => raw41913 (permutation247 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41913step0 raw41913; decide +kernel
      have hl : raw41913step0Labels = raw41913Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41913 raw41913Labels permutation247 permutation7
    mixedMoment B raw41913step0 raw41913step0Labels = mixedMoment B raw41913step1 raw41913step1Labels := by
      have ha : raw41913step1 = -raw41913step0 := by apply Matrix.ext; change ∀ i j, raw41913step1 i j = -(raw41913step0 i j); unfold raw41913step1 raw41913step0; decide +kernel
      have hl : raw41913step1Labels = raw41913step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41913step1 raw41913step1Labels = mixedMoment B raw41913step2 raw41913step2Labels := by
      have ha : raw41913step2 = raw41913step1 := by apply Matrix.ext; unfold raw41913step2 raw41913step1; decide +kernel
      have hl : raw41913step1Labels = labelEmbedding6 ∘ raw41913step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41913step1 raw41913step1Labels raw41913step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4364 node4364Labels := by rfl

def raw41914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw41914Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw41914step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw41914step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41914step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw41914step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41914 raw41914Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw41914 raw41914Labels = mixedMoment B raw41914step0 raw41914step0Labels := by
      have hz : ∀ j, raw41914 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41914step0 = (fun i j => raw41914 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41914step0 raw41914; decide +kernel
      have hl : raw41914step0Labels = raw41914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41914 raw41914Labels permutation434 hz
    mixedMoment B raw41914step0 raw41914step0Labels = mixedMoment B raw41914step1 raw41914step1Labels := by
      have hz : ∀ j, raw41914step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41914step1 = (fun i j => raw41914step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41914step1 raw41914step0; decide +kernel
      have hl : raw41914step1Labels = raw41914step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41914step0 raw41914step0Labels permutation80 hz
    mixedMoment B raw41914step1 raw41914step1Labels = mixedMoment B raw41914step2 raw41914step2Labels := by
      have ha : raw41914step2 = raw41914step1 := by apply Matrix.ext; unfold raw41914step2 raw41914step1; decide +kernel
      have hl : raw41914step1Labels = labelEmbedding1 ∘ raw41914step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41914step1 raw41914step1Labels raw41914step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

def raw41915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw41915Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw41915step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw41915step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41915step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw41915step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41915step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw41915step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41915step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw41915step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41915 raw41915Labels = mixedMoment B node4476 node4476Labels := by
  calc
    mixedMoment B raw41915 raw41915Labels = mixedMoment B raw41915step0 raw41915step0Labels := by
      have hz : ∀ j, raw41915 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41915step0 = (fun i j => raw41915 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41915step0 raw41915; decide +kernel
      have hl : raw41915step0Labels = raw41915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41915 raw41915Labels permutation434 hz
    mixedMoment B raw41915step0 raw41915step0Labels = mixedMoment B raw41915step1 raw41915step1Labels := by
      have hz : ∀ j, raw41915step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41915step1 = (fun i j => raw41915step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41915step1 raw41915step0; decide +kernel
      have hl : raw41915step1Labels = raw41915step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41915step0 raw41915step0Labels permutation80 hz
    mixedMoment B raw41915step1 raw41915step1Labels = mixedMoment B raw41915step2 raw41915step2Labels := by
      have ha : raw41915step2 = (fun i j => raw41915step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41915step2 raw41915step1; decide +kernel
      have hl : raw41915step2Labels = raw41915step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41915step1 raw41915step1Labels permutation12 permutation7
    mixedMoment B raw41915step2 raw41915step2Labels = mixedMoment B raw41915step3 raw41915step3Labels := by
      have ha : raw41915step3 = -raw41915step2 := by apply Matrix.ext; change ∀ i j, raw41915step3 i j = -(raw41915step2 i j); unfold raw41915step3 raw41915step2; decide +kernel
      have hl : raw41915step3Labels = raw41915step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41915step3 raw41915step3Labels = mixedMoment B raw41915step4 raw41915step4Labels := by
      have ha : raw41915step4 = raw41915step3 := by apply Matrix.ext; unfold raw41915step4 raw41915step3; decide +kernel
      have hl : raw41915step3Labels = labelEmbedding6 ∘ raw41915step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41915step3 raw41915step3Labels raw41915step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4476 node4476Labels := by rfl

def raw41916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw41916Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw41916step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41916step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw41916step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41916step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw41916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41916 raw41916Labels = mixedMoment B node1722 node1722Labels := by
  calc
    mixedMoment B raw41916 raw41916Labels = mixedMoment B raw41916step0 raw41916step0Labels := by
      have hz : ∀ j, raw41916 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41916step0 = (fun i j => raw41916 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41916step0 raw41916; decide +kernel
      have hl : raw41916step0Labels = raw41916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41916 raw41916Labels permutation434 hz
    mixedMoment B raw41916step0 raw41916step0Labels = mixedMoment B raw41916step1 raw41916step1Labels := by
      have hz : ∀ j, raw41916step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41916step1 = (fun i j => raw41916step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41916step1 raw41916step0; decide +kernel
      have hl : raw41916step1Labels = raw41916step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41916step0 raw41916step0Labels permutation80 hz
    mixedMoment B raw41916step1 raw41916step1Labels = mixedMoment B raw41916step2 raw41916step2Labels := by
      have ha : raw41916step2 = raw41916step1 := by apply Matrix.ext; unfold raw41916step2 raw41916step1; decide +kernel
      have hl : raw41916step1Labels = labelEmbedding1 ∘ raw41916step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41916step1 raw41916step1Labels raw41916step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1722 node1722Labels := by rfl

def raw41917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw41917Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw41917step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw41917step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw41917step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41917step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw41917step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41917step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw41917step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41917 raw41917Labels = mixedMoment B node4370 node4370Labels := by
  calc
    mixedMoment B raw41917 raw41917Labels = mixedMoment B raw41917step0 raw41917step0Labels := by
      have hz : ∀ j, raw41917 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41917step0 = (fun i j => raw41917 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41917step0 raw41917; decide +kernel
      have hl : raw41917step0Labels = raw41917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41917 raw41917Labels permutation434 hz
    mixedMoment B raw41917step0 raw41917step0Labels = mixedMoment B raw41917step1 raw41917step1Labels := by
      have hz : ∀ j, raw41917step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41917step1 = (fun i j => raw41917step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41917step1 raw41917step0; decide +kernel
      have hl : raw41917step1Labels = raw41917step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41917step0 raw41917step0Labels permutation80 hz
    mixedMoment B raw41917step1 raw41917step1Labels = mixedMoment B raw41917step2 raw41917step2Labels := by
      have ha : raw41917step2 = (fun i j => raw41917step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41917step2 raw41917step1; decide +kernel
      have hl : raw41917step2Labels = raw41917step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41917step1 raw41917step1Labels permutation10 permutation7
    mixedMoment B raw41917step2 raw41917step2Labels = mixedMoment B raw41917step3 raw41917step3Labels := by
      have ha : raw41917step3 = -raw41917step2 := by apply Matrix.ext; change ∀ i j, raw41917step3 i j = -(raw41917step2 i j); unfold raw41917step3 raw41917step2; decide +kernel
      have hl : raw41917step3Labels = raw41917step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41917step3 raw41917step3Labels = mixedMoment B raw41917step4 raw41917step4Labels := by
      have ha : raw41917step4 = raw41917step3 := by apply Matrix.ext; unfold raw41917step4 raw41917step3; decide +kernel
      have hl : raw41917step3Labels = labelEmbedding6 ∘ raw41917step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41917step3 raw41917step3Labels raw41917step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4370 node4370Labels := by rfl

def raw41918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41918Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41918step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41918step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41918step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41918step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41918 raw41918Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw41918 raw41918Labels = mixedMoment B raw41918step0 raw41918step0Labels := by
      have hz : ∀ j, raw41918 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41918step0 = (fun i j => raw41918 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41918step0 raw41918; decide +kernel
      have hl : raw41918step0Labels = raw41918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41918 raw41918Labels permutation346 hz
    mixedMoment B raw41918step0 raw41918step0Labels = mixedMoment B raw41918step1 raw41918step1Labels := by
      have ha : raw41918step1 = (fun i j => raw41918step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41918step1 raw41918step0; decide +kernel
      have hl : raw41918step1Labels = raw41918step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41918step0 raw41918step0Labels permutation38 permutation2
    mixedMoment B raw41918step1 raw41918step1Labels = mixedMoment B raw41918step2 raw41918step2Labels := by
      have ha : raw41918step2 = raw41918step1 := by apply Matrix.ext; unfold raw41918step2 raw41918step1; decide +kernel
      have hl : raw41918step1Labels = labelEmbedding1 ∘ raw41918step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41918step1 raw41918step1Labels raw41918step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

def raw41919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41919Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw41919step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw41919step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw41919step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41919step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw41919step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41919 raw41919Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw41919 raw41919Labels = mixedMoment B raw41919step0 raw41919step0Labels := by
      have hz : ∀ j, raw41919 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41919step0 = (fun i j => raw41919 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41919step0 raw41919; decide +kernel
      have hl : raw41919step0Labels = raw41919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41919 raw41919Labels permutation346 hz
    mixedMoment B raw41919step0 raw41919step0Labels = mixedMoment B raw41919step1 raw41919step1Labels := by
      have ha : raw41919step1 = (fun i j => raw41919step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41919step1 raw41919step0; decide +kernel
      have hl : raw41919step1Labels = raw41919step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41919step0 raw41919step0Labels permutation40 permutation7
    mixedMoment B raw41919step1 raw41919step1Labels = mixedMoment B raw41919step2 raw41919step2Labels := by
      have ha : raw41919step2 = -raw41919step1 := by apply Matrix.ext; change ∀ i j, raw41919step2 i j = -(raw41919step1 i j); unfold raw41919step2 raw41919step1; decide +kernel
      have hl : raw41919step2Labels = raw41919step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41919step2 raw41919step2Labels = mixedMoment B raw41919step3 raw41919step3Labels := by
      have ha : raw41919step3 = raw41919step2 := by apply Matrix.ext; unfold raw41919step3 raw41919step2; decide +kernel
      have hl : raw41919step2Labels = labelEmbedding6 ∘ raw41919step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41919step2 raw41919step2Labels raw41919step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4330 node4330Labels := by rfl

def raw41920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41920Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41920step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw41920step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41920step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw41920step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41920 raw41920Labels = mixedMoment B node1720 node1720Labels := by
  calc
    mixedMoment B raw41920 raw41920Labels = mixedMoment B raw41920step0 raw41920step0Labels := by
      have hz : ∀ j, raw41920 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41920step0 = (fun i j => raw41920 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41920step0 raw41920; decide +kernel
      have hl : raw41920step0Labels = raw41920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41920 raw41920Labels permutation346 hz
    mixedMoment B raw41920step0 raw41920step0Labels = mixedMoment B raw41920step1 raw41920step1Labels := by
      have ha : raw41920step1 = (fun i j => raw41920step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41920step1 raw41920step0; decide +kernel
      have hl : raw41920step1Labels = raw41920step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41920step0 raw41920step0Labels permutation37 permutation2
    mixedMoment B raw41920step1 raw41920step1Labels = mixedMoment B raw41920step2 raw41920step2Labels := by
      have ha : raw41920step2 = raw41920step1 := by apply Matrix.ext; unfold raw41920step2 raw41920step1; decide +kernel
      have hl : raw41920step1Labels = labelEmbedding1 ∘ raw41920step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41920step1 raw41920step1Labels raw41920step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1720 node1720Labels := by rfl

def raw41921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41921Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw41921step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw41921step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41921step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41921step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41921step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41921step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41921 raw41921Labels = mixedMoment B node4367 node4367Labels := by
  calc
    mixedMoment B raw41921 raw41921Labels = mixedMoment B raw41921step0 raw41921step0Labels := by
      have hz : ∀ j, raw41921 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41921step0 = (fun i j => raw41921 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41921step0 raw41921; decide +kernel
      have hl : raw41921step0Labels = raw41921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41921 raw41921Labels permutation346 hz
    mixedMoment B raw41921step0 raw41921step0Labels = mixedMoment B raw41921step1 raw41921step1Labels := by
      have ha : raw41921step1 = (fun i j => raw41921step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41921step1 raw41921step0; decide +kernel
      have hl : raw41921step1Labels = raw41921step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41921step0 raw41921step0Labels permutation51 permutation7
    mixedMoment B raw41921step1 raw41921step1Labels = mixedMoment B raw41921step2 raw41921step2Labels := by
      have ha : raw41921step2 = -raw41921step1 := by apply Matrix.ext; change ∀ i j, raw41921step2 i j = -(raw41921step1 i j); unfold raw41921step2 raw41921step1; decide +kernel
      have hl : raw41921step2Labels = raw41921step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41921step2 raw41921step2Labels = mixedMoment B raw41921step3 raw41921step3Labels := by
      have ha : raw41921step3 = raw41921step2 := by apply Matrix.ext; unfold raw41921step3 raw41921step2; decide +kernel
      have hl : raw41921step2Labels = labelEmbedding6 ∘ raw41921step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41921step2 raw41921step2Labels raw41921step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4367 node4367Labels := by rfl

def raw41922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41922Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41922step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41922step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41922step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41922step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41922 raw41922Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw41922 raw41922Labels = mixedMoment B raw41922step0 raw41922step0Labels := by
      have hz : ∀ j, raw41922 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41922step0 = (fun i j => raw41922 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41922step0 raw41922; decide +kernel
      have hl : raw41922step0Labels = raw41922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41922 raw41922Labels permutation346 hz
    mixedMoment B raw41922step0 raw41922step0Labels = mixedMoment B raw41922step1 raw41922step1Labels := by
      have ha : raw41922step1 = (fun i j => raw41922step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41922step1 raw41922step0; decide +kernel
      have hl : raw41922step1Labels = raw41922step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41922step0 raw41922step0Labels permutation35 permutation2
    mixedMoment B raw41922step1 raw41922step1Labels = mixedMoment B raw41922step2 raw41922step2Labels := by
      have ha : raw41922step2 = raw41922step1 := by apply Matrix.ext; unfold raw41922step2 raw41922step1; decide +kernel
      have hl : raw41922step1Labels = labelEmbedding1 ∘ raw41922step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41922step1 raw41922step1Labels raw41922step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1723 node1723Labels := by rfl

def raw41923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41923Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw41923step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw41923step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw41923step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41923step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw41923step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41923 raw41923Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw41923 raw41923Labels = mixedMoment B raw41923step0 raw41923step0Labels := by
      have hz : ∀ j, raw41923 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41923step0 = (fun i j => raw41923 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41923step0 raw41923; decide +kernel
      have hl : raw41923step0Labels = raw41923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41923 raw41923Labels permutation346 hz
    mixedMoment B raw41923step0 raw41923step0Labels = mixedMoment B raw41923step1 raw41923step1Labels := by
      have ha : raw41923step1 = (fun i j => raw41923step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41923step1 raw41923step0; decide +kernel
      have hl : raw41923step1Labels = raw41923step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41923step0 raw41923step0Labels permutation48 permutation7
    mixedMoment B raw41923step1 raw41923step1Labels = mixedMoment B raw41923step2 raw41923step2Labels := by
      have ha : raw41923step2 = -raw41923step1 := by apply Matrix.ext; change ∀ i j, raw41923step2 i j = -(raw41923step1 i j); unfold raw41923step2 raw41923step1; decide +kernel
      have hl : raw41923step2Labels = raw41923step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41923step2 raw41923step2Labels = mixedMoment B raw41923step3 raw41923step3Labels := by
      have ha : raw41923step3 = raw41923step2 := by apply Matrix.ext; unfold raw41923step3 raw41923step2; decide +kernel
      have hl : raw41923step2Labels = labelEmbedding6 ∘ raw41923step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41923step2 raw41923step2Labels raw41923step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4440 node4440Labels := by rfl

def raw41924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41924Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41924step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw41924step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw41924step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41924 raw41924Labels = mixedMoment B node1721 node1721Labels := by
  calc
    mixedMoment B raw41924 raw41924Labels = mixedMoment B raw41924step0 raw41924step0Labels := by
      have hz : ∀ j, raw41924 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41924step0 = (fun i j => raw41924 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41924step0 raw41924; decide +kernel
      have hl : raw41924step0Labels = raw41924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41924 raw41924Labels permutation346 hz
    mixedMoment B raw41924step0 raw41924step0Labels = mixedMoment B raw41924step1 raw41924step1Labels := by
      have ha : raw41924step1 = (fun i j => raw41924step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41924step1 raw41924step0; decide +kernel
      have hl : raw41924step1Labels = raw41924step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41924step0 raw41924step0Labels permutation36 permutation2
    mixedMoment B raw41924step1 raw41924step1Labels = mixedMoment B raw41924step2 raw41924step2Labels := by
      have ha : raw41924step2 = raw41924step1 := by apply Matrix.ext; unfold raw41924step2 raw41924step1; decide +kernel
      have hl : raw41924step1Labels = labelEmbedding1 ∘ raw41924step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41924step1 raw41924step1Labels raw41924step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1721 node1721Labels := by rfl

def raw41925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41925Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41925step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw41925step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41925step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41925step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41925step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41925step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41925 raw41925Labels = mixedMoment B node4369 node4369Labels := by
  calc
    mixedMoment B raw41925 raw41925Labels = mixedMoment B raw41925step0 raw41925step0Labels := by
      have hz : ∀ j, raw41925 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41925step0 = (fun i j => raw41925 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41925step0 raw41925; decide +kernel
      have hl : raw41925step0Labels = raw41925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41925 raw41925Labels permutation346 hz
    mixedMoment B raw41925step0 raw41925step0Labels = mixedMoment B raw41925step1 raw41925step1Labels := by
      have ha : raw41925step1 = (fun i j => raw41925step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41925step1 raw41925step0; decide +kernel
      have hl : raw41925step1Labels = raw41925step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41925step0 raw41925step0Labels permutation50 permutation7
    mixedMoment B raw41925step1 raw41925step1Labels = mixedMoment B raw41925step2 raw41925step2Labels := by
      have ha : raw41925step2 = -raw41925step1 := by apply Matrix.ext; change ∀ i j, raw41925step2 i j = -(raw41925step1 i j); unfold raw41925step2 raw41925step1; decide +kernel
      have hl : raw41925step2Labels = raw41925step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41925step2 raw41925step2Labels = mixedMoment B raw41925step3 raw41925step3Labels := by
      have ha : raw41925step3 = raw41925step2 := by apply Matrix.ext; unfold raw41925step3 raw41925step2; decide +kernel
      have hl : raw41925step2Labels = labelEmbedding6 ∘ raw41925step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41925step2 raw41925step2Labels raw41925step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4369 node4369Labels := by rfl

def raw41926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41926Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw41926step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41926step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw41926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41926 raw41926Labels = mixedMoment B node1670 node1670Labels := by
  calc
    mixedMoment B raw41926 raw41926Labels = mixedMoment B raw41926step0 raw41926step0Labels := by
      have ha : raw41926step0 = (fun i j => raw41926 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41926step0 raw41926; decide +kernel
      have hl : raw41926step0Labels = raw41926Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41926 raw41926Labels permutation181 permutation2
    mixedMoment B raw41926step0 raw41926step0Labels = mixedMoment B raw41926step1 raw41926step1Labels := by
      have ha : raw41926step1 = raw41926step0 := by apply Matrix.ext; unfold raw41926step1 raw41926step0; decide +kernel
      have hl : raw41926step0Labels = labelEmbedding1 ∘ raw41926step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41926step0 raw41926step0Labels raw41926step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1670 node1670Labels := by rfl

def raw41927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41927Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw41927step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41927step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41927step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41927step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41927step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41927 raw41927Labels = mixedMoment B node4327 node4327Labels := by
  calc
    mixedMoment B raw41927 raw41927Labels = mixedMoment B raw41927step0 raw41927step0Labels := by
      have ha : raw41927step0 = (fun i j => raw41927 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41927step0 raw41927; decide +kernel
      have hl : raw41927step0Labels = raw41927Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41927 raw41927Labels permutation195 permutation7
    mixedMoment B raw41927step0 raw41927step0Labels = mixedMoment B raw41927step1 raw41927step1Labels := by
      have ha : raw41927step1 = -raw41927step0 := by apply Matrix.ext; change ∀ i j, raw41927step1 i j = -(raw41927step0 i j); unfold raw41927step1 raw41927step0; decide +kernel
      have hl : raw41927step1Labels = raw41927step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41927step1 raw41927step1Labels = mixedMoment B raw41927step2 raw41927step2Labels := by
      have ha : raw41927step2 = raw41927step1 := by apply Matrix.ext; unfold raw41927step2 raw41927step1; decide +kernel
      have hl : raw41927step1Labels = labelEmbedding6 ∘ raw41927step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41927step1 raw41927step1Labels raw41927step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4327 node4327Labels := by rfl

def raw41928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw41928Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw41928step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw41928step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41928step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def raw41928step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41928step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def raw41928step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41928 raw41928Labels = mixedMoment B node1757 node1757Labels := by
  calc
    mixedMoment B raw41928 raw41928Labels = mixedMoment B raw41928step0 raw41928step0Labels := by
      have hz : ∀ j, raw41928 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41928step0 = (fun i j => raw41928 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41928step0 raw41928; decide +kernel
      have hl : raw41928step0Labels = raw41928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41928 raw41928Labels permutation434 hz
    mixedMoment B raw41928step0 raw41928step0Labels = mixedMoment B raw41928step1 raw41928step1Labels := by
      have hz : ∀ j, raw41928step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41928step1 = (fun i j => raw41928step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41928step1 raw41928step0; decide +kernel
      have hl : raw41928step1Labels = raw41928step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41928step0 raw41928step0Labels permutation80 hz
    mixedMoment B raw41928step1 raw41928step1Labels = mixedMoment B raw41928step2 raw41928step2Labels := by
      have hz : ∀ j, raw41928step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41928step2 = (fun i j => raw41928step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41928step2 raw41928step1; decide +kernel
      have hl : raw41928step2Labels = raw41928step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41928step1 raw41928step1Labels permutation14 hz
    mixedMoment B raw41928step2 raw41928step2Labels = mixedMoment B raw41928step3 raw41928step3Labels := by
      have ha : raw41928step3 = raw41928step2 := by apply Matrix.ext; unfold raw41928step3 raw41928step2; decide +kernel
      have hl : raw41928step2Labels = labelEmbedding1 ∘ raw41928step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41928step2 raw41928step2Labels raw41928step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1757 node1757Labels := by rfl

def raw41929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw41929Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw41929step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw41929step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41929step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def raw41929step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41929step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw41929step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41929 raw41929Labels = mixedMoment B node4481 node4481Labels := by
  calc
    mixedMoment B raw41929 raw41929Labels = mixedMoment B raw41929step0 raw41929step0Labels := by
      have hz : ∀ j, raw41929 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41929step0 = (fun i j => raw41929 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41929step0 raw41929; decide +kernel
      have hl : raw41929step0Labels = raw41929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41929 raw41929Labels permutation434 hz
    mixedMoment B raw41929step0 raw41929step0Labels = mixedMoment B raw41929step1 raw41929step1Labels := by
      have hz : ∀ j, raw41929step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41929step1 = (fun i j => raw41929step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41929step1 raw41929step0; decide +kernel
      have hl : raw41929step1Labels = raw41929step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41929step0 raw41929step0Labels permutation80 hz
    mixedMoment B raw41929step1 raw41929step1Labels = mixedMoment B raw41929step2 raw41929step2Labels := by
      have hz : ∀ j, raw41929step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41929step2 = (fun i j => raw41929step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41929step2 raw41929step1; decide +kernel
      have hl : raw41929step2Labels = raw41929step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41929step1 raw41929step1Labels permutation14 hz
    mixedMoment B raw41929step2 raw41929step2Labels = mixedMoment B raw41929step3 raw41929step3Labels := by
      have ha : raw41929step3 = (fun i j => raw41929step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41929step3 raw41929step2; decide +kernel
      have hl : raw41929step3Labels = raw41929step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41929step2 raw41929step2Labels permutation5 permutation6
    _ = mixedMoment B node4481 node4481Labels := by rfl

def raw41930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw41930Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw41930step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw41930step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41930step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![2, 3, -5]]
def raw41930step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41930step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -3, 4], ![-2, 1, 1]]
def raw41930step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41930step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![2, -1, -1]]
def raw41930step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41930step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![2, -1, -1]]
def raw41930step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41930 raw41930Labels = mixedMoment B node1540 node1540Labels := by
  calc
    mixedMoment B raw41930 raw41930Labels = mixedMoment B raw41930step0 raw41930step0Labels := by
      have hz : ∀ j, raw41930 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41930step0 = (fun i j => raw41930 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41930step0 raw41930; decide +kernel
      have hl : raw41930step0Labels = raw41930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41930 raw41930Labels permutation434 hz
    mixedMoment B raw41930step0 raw41930step0Labels = mixedMoment B raw41930step1 raw41930step1Labels := by
      have hz : ∀ j, raw41930step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41930step1 = (fun i j => raw41930step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41930step1 raw41930step0; decide +kernel
      have hl : raw41930step1Labels = raw41930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41930step0 raw41930step0Labels permutation80 hz
    mixedMoment B raw41930step1 raw41930step1Labels = mixedMoment B raw41930step2 raw41930step2Labels := by
      have hz : ∀ j, raw41930step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41930step2 = (fun i j => raw41930step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41930step2 raw41930step1; decide +kernel
      have hl : raw41930step2Labels = raw41930step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41930step1 raw41930step1Labels permutation14 hz
    mixedMoment B raw41930step2 raw41930step2Labels = mixedMoment B raw41930step3 raw41930step3Labels := by
      have ha : raw41930step3 = (fun i j => raw41930step2 (permutation6 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41930step3 raw41930step2; decide +kernel
      have hl : raw41930step3Labels = raw41930step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41930step2 raw41930step2Labels permutation6 permutation4
    mixedMoment B raw41930step3 raw41930step3Labels = mixedMoment B raw41930step4 raw41930step4Labels := by
      have ha : raw41930step4 = -raw41930step3 := by apply Matrix.ext; change ∀ i j, raw41930step4 i j = -(raw41930step3 i j); unfold raw41930step4 raw41930step3; decide +kernel
      have hl : raw41930step4Labels = raw41930step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41930step4 raw41930step4Labels = mixedMoment B raw41930step5 raw41930step5Labels := by
      have ha : raw41930step5 = raw41930step4 := by apply Matrix.ext; unfold raw41930step5 raw41930step4; decide +kernel
      have hl : raw41930step4Labels = labelEmbedding1 ∘ raw41930step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41930step4 raw41930step4Labels raw41930step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1540 node1540Labels := by rfl

def raw41931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw41931Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw41931step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw41931step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41931step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![2, 3, -5]]
def raw41931step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41931step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def raw41931step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41931 raw41931Labels = mixedMoment B node4189 node4189Labels := by
  calc
    mixedMoment B raw41931 raw41931Labels = mixedMoment B raw41931step0 raw41931step0Labels := by
      have hz : ∀ j, raw41931 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41931step0 = (fun i j => raw41931 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41931step0 raw41931; decide +kernel
      have hl : raw41931step0Labels = raw41931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41931 raw41931Labels permutation434 hz
    mixedMoment B raw41931step0 raw41931step0Labels = mixedMoment B raw41931step1 raw41931step1Labels := by
      have hz : ∀ j, raw41931step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41931step1 = (fun i j => raw41931step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41931step1 raw41931step0; decide +kernel
      have hl : raw41931step1Labels = raw41931step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41931step0 raw41931step0Labels permutation80 hz
    mixedMoment B raw41931step1 raw41931step1Labels = mixedMoment B raw41931step2 raw41931step2Labels := by
      have hz : ∀ j, raw41931step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41931step2 = (fun i j => raw41931step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41931step2 raw41931step1; decide +kernel
      have hl : raw41931step2Labels = raw41931step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41931step1 raw41931step1Labels permutation14 hz
    mixedMoment B raw41931step2 raw41931step2Labels = mixedMoment B raw41931step3 raw41931step3Labels := by
      have ha : raw41931step3 = (fun i j => raw41931step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41931step3 raw41931step2; decide +kernel
      have hl : raw41931step3Labels = raw41931step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41931step2 raw41931step2Labels permutation7 permutation6
    _ = mixedMoment B node4189 node4189Labels := by rfl

def raw41932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41932Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41932step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41932step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41932step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw41932step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41932step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw41932step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41932step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw41932step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41932 raw41932Labels = mixedMoment B node1532 node1532Labels := by
  calc
    mixedMoment B raw41932 raw41932Labels = mixedMoment B raw41932step0 raw41932step0Labels := by
      have hz : ∀ j, raw41932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41932step0 = (fun i j => raw41932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41932step0 raw41932; decide +kernel
      have hl : raw41932step0Labels = raw41932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41932 raw41932Labels permutation346 hz
    mixedMoment B raw41932step0 raw41932step0Labels = mixedMoment B raw41932step1 raw41932step1Labels := by
      have hz : ∀ j, raw41932step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41932step1 = (fun i j => raw41932step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41932step1 raw41932step0; decide +kernel
      have hl : raw41932step1Labels = raw41932step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41932step0 raw41932step0Labels permutation56 hz
    mixedMoment B raw41932step1 raw41932step1Labels = mixedMoment B raw41932step2 raw41932step2Labels := by
      have ha : raw41932step2 = (fun i j => raw41932step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41932step2 raw41932step1; decide +kernel
      have hl : raw41932step2Labels = raw41932step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41932step1 raw41932step1Labels permutation31 permutation4
    mixedMoment B raw41932step2 raw41932step2Labels = mixedMoment B raw41932step3 raw41932step3Labels := by
      have ha : raw41932step3 = -raw41932step2 := by apply Matrix.ext; change ∀ i j, raw41932step3 i j = -(raw41932step2 i j); unfold raw41932step3 raw41932step2; decide +kernel
      have hl : raw41932step3Labels = raw41932step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41932step3 raw41932step3Labels = mixedMoment B raw41932step4 raw41932step4Labels := by
      have ha : raw41932step4 = raw41932step3 := by apply Matrix.ext; unfold raw41932step4 raw41932step3; decide +kernel
      have hl : raw41932step3Labels = labelEmbedding1 ∘ raw41932step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41932step3 raw41932step3Labels raw41932step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1532 node1532Labels := by rfl

def raw41933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41933Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41933step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41933step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw41933step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41933 raw41933Labels = mixedMoment B node4159 node4159Labels := by
  calc
    mixedMoment B raw41933 raw41933Labels = mixedMoment B raw41933step0 raw41933step0Labels := by
      have hz : ∀ j, raw41933 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41933step0 = (fun i j => raw41933 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41933step0 raw41933; decide +kernel
      have hl : raw41933step0Labels = raw41933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41933 raw41933Labels permutation346 hz
    mixedMoment B raw41933step0 raw41933step0Labels = mixedMoment B raw41933step1 raw41933step1Labels := by
      have hz : ∀ j, raw41933step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41933step1 = (fun i j => raw41933step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41933step1 raw41933step0; decide +kernel
      have hl : raw41933step1Labels = raw41933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41933step0 raw41933step0Labels permutation56 hz
    mixedMoment B raw41933step1 raw41933step1Labels = mixedMoment B raw41933step2 raw41933step2Labels := by
      have ha : raw41933step2 = (fun i j => raw41933step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41933step2 raw41933step1; decide +kernel
      have hl : raw41933step2Labels = raw41933step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41933step1 raw41933step1Labels permutation31 permutation6
    _ = mixedMoment B node4159 node4159Labels := by rfl

def raw41934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw41934Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw41934step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw41934step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -3, 4], ![-2, 1, 1]]
def raw41934step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41934step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw41934step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41934step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw41934step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41934 raw41934Labels = mixedMoment B node1695 node1695Labels := by
  calc
    mixedMoment B raw41934 raw41934Labels = mixedMoment B raw41934step0 raw41934step0Labels := by
      have hz : ∀ j, raw41934 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41934step0 = (fun i j => raw41934 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41934step0 raw41934; decide +kernel
      have hl : raw41934step0Labels = raw41934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41934 raw41934Labels permutation346 hz
    mixedMoment B raw41934step0 raw41934step0Labels = mixedMoment B raw41934step1 raw41934step1Labels := by
      have hz : ∀ j, raw41934step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41934step1 = (fun i j => raw41934step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41934step1 raw41934step0; decide +kernel
      have hl : raw41934step1Labels = raw41934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41934step0 raw41934step0Labels permutation56 hz
    mixedMoment B raw41934step1 raw41934step1Labels = mixedMoment B raw41934step2 raw41934step2Labels := by
      have ha : raw41934step2 = (fun i j => raw41934step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41934step2 raw41934step1; decide +kernel
      have hl : raw41934step2Labels = raw41934step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41934step1 raw41934step1Labels permutation16 permutation4
    mixedMoment B raw41934step2 raw41934step2Labels = mixedMoment B raw41934step3 raw41934step3Labels := by
      have ha : raw41934step3 = -raw41934step2 := by apply Matrix.ext; change ∀ i j, raw41934step3 i j = -(raw41934step2 i j); unfold raw41934step3 raw41934step2; decide +kernel
      have hl : raw41934step3Labels = raw41934step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41934step3 raw41934step3Labels = mixedMoment B raw41934step4 raw41934step4Labels := by
      have ha : raw41934step4 = raw41934step3 := by apply Matrix.ext; unfold raw41934step4 raw41934step3; decide +kernel
      have hl : raw41934step3Labels = labelEmbedding1 ∘ raw41934step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41934step3 raw41934step3Labels raw41934step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1695 node1695Labels := by rfl

def raw41935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw41935Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw41935step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw41935step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41935step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw41935step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41935 raw41935Labels = mixedMoment B node4358 node4358Labels := by
  calc
    mixedMoment B raw41935 raw41935Labels = mixedMoment B raw41935step0 raw41935step0Labels := by
      have hz : ∀ j, raw41935 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41935step0 = (fun i j => raw41935 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41935step0 raw41935; decide +kernel
      have hl : raw41935step0Labels = raw41935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41935 raw41935Labels permutation346 hz
    mixedMoment B raw41935step0 raw41935step0Labels = mixedMoment B raw41935step1 raw41935step1Labels := by
      have hz : ∀ j, raw41935step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41935step1 = (fun i j => raw41935step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41935step1 raw41935step0; decide +kernel
      have hl : raw41935step1Labels = raw41935step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41935step0 raw41935step0Labels permutation56 hz
    mixedMoment B raw41935step1 raw41935step1Labels = mixedMoment B raw41935step2 raw41935step2Labels := by
      have ha : raw41935step2 = (fun i j => raw41935step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41935step2 raw41935step1; decide +kernel
      have hl : raw41935step2Labels = raw41935step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41935step1 raw41935step1Labels permutation17 permutation6
    _ = mixedMoment B node4358 node4358Labels := by rfl

def raw41936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw41936Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw41936step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw41936step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw41936step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41936step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 3, -4]]
def raw41936step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41936 raw41936Labels = mixedMoment B node1749 node1749Labels := by
  calc
    mixedMoment B raw41936 raw41936Labels = mixedMoment B raw41936step0 raw41936step0Labels := by
      have hz : ∀ j, raw41936 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41936step0 = (fun i j => raw41936 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41936step0 raw41936; decide +kernel
      have hl : raw41936step0Labels = raw41936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41936 raw41936Labels permutation346 hz
    mixedMoment B raw41936step0 raw41936step0Labels = mixedMoment B raw41936step1 raw41936step1Labels := by
      have hz : ∀ j, raw41936step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41936step1 = (fun i j => raw41936step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41936step1 raw41936step0; decide +kernel
      have hl : raw41936step1Labels = raw41936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41936step0 raw41936step0Labels permutation56 hz
    mixedMoment B raw41936step1 raw41936step1Labels = mixedMoment B raw41936step2 raw41936step2Labels := by
      have ha : raw41936step2 = (fun i j => raw41936step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41936step2 raw41936step1; decide +kernel
      have hl : raw41936step2Labels = raw41936step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41936step1 raw41936step1Labels permutation11 permutation2
    mixedMoment B raw41936step2 raw41936step2Labels = mixedMoment B raw41936step3 raw41936step3Labels := by
      have ha : raw41936step3 = raw41936step2 := by apply Matrix.ext; unfold raw41936step3 raw41936step2; decide +kernel
      have hl : raw41936step2Labels = labelEmbedding1 ∘ raw41936step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41936step2 raw41936step2Labels raw41936step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1749 node1749Labels := by rfl

def raw41937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw41937Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw41937step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw41937step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41937step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw41937step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41937 raw41937Labels = mixedMoment B node4445 node4445Labels := by
  calc
    mixedMoment B raw41937 raw41937Labels = mixedMoment B raw41937step0 raw41937step0Labels := by
      have hz : ∀ j, raw41937 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41937step0 = (fun i j => raw41937 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41937step0 raw41937; decide +kernel
      have hl : raw41937step0Labels = raw41937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41937 raw41937Labels permutation346 hz
    mixedMoment B raw41937step0 raw41937step0Labels = mixedMoment B raw41937step1 raw41937step1Labels := by
      have hz : ∀ j, raw41937step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41937step1 = (fun i j => raw41937step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41937step1 raw41937step0; decide +kernel
      have hl : raw41937step1Labels = raw41937step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41937step0 raw41937step0Labels permutation56 hz
    mixedMoment B raw41937step1 raw41937step1Labels = mixedMoment B raw41937step2 raw41937step2Labels := by
      have ha : raw41937step2 = (fun i j => raw41937step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41937step2 raw41937step1; decide +kernel
      have hl : raw41937step2Labels = raw41937step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41937step1 raw41937step1Labels permutation17 permutation6
    _ = mixedMoment B node4445 node4445Labels := by rfl

def raw41938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw41938Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw41938step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw41938step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw41938step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41938step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw41938step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41938 raw41938Labels = mixedMoment B node1748 node1748Labels := by
  calc
    mixedMoment B raw41938 raw41938Labels = mixedMoment B raw41938step0 raw41938step0Labels := by
      have hz : ∀ j, raw41938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41938step0 = (fun i j => raw41938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41938step0 raw41938; decide +kernel
      have hl : raw41938step0Labels = raw41938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41938 raw41938Labels permutation346 hz
    mixedMoment B raw41938step0 raw41938step0Labels = mixedMoment B raw41938step1 raw41938step1Labels := by
      have hz : ∀ j, raw41938step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41938step1 = (fun i j => raw41938step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41938step1 raw41938step0; decide +kernel
      have hl : raw41938step1Labels = raw41938step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41938step0 raw41938step0Labels permutation56 hz
    mixedMoment B raw41938step1 raw41938step1Labels = mixedMoment B raw41938step2 raw41938step2Labels := by
      have ha : raw41938step2 = (fun i j => raw41938step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41938step2 raw41938step1; decide +kernel
      have hl : raw41938step2Labels = raw41938step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41938step1 raw41938step1Labels permutation13 permutation2
    mixedMoment B raw41938step2 raw41938step2Labels = mixedMoment B raw41938step3 raw41938step3Labels := by
      have ha : raw41938step3 = raw41938step2 := by apply Matrix.ext; unfold raw41938step3 raw41938step2; decide +kernel
      have hl : raw41938step2Labels = labelEmbedding1 ∘ raw41938step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41938step2 raw41938step2Labels raw41938step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1748 node1748Labels := by rfl

def raw41939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw41939Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw41939step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw41939step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw41939step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41939step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41939step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41939step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41939step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41939 raw41939Labels = mixedMoment B node4374 node4374Labels := by
  calc
    mixedMoment B raw41939 raw41939Labels = mixedMoment B raw41939step0 raw41939step0Labels := by
      have hz : ∀ j, raw41939 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41939step0 = (fun i j => raw41939 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41939step0 raw41939; decide +kernel
      have hl : raw41939step0Labels = raw41939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41939 raw41939Labels permutation346 hz
    mixedMoment B raw41939step0 raw41939step0Labels = mixedMoment B raw41939step1 raw41939step1Labels := by
      have hz : ∀ j, raw41939step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41939step1 = (fun i j => raw41939step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41939step1 raw41939step0; decide +kernel
      have hl : raw41939step1Labels = raw41939step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41939step0 raw41939step0Labels permutation56 hz
    mixedMoment B raw41939step1 raw41939step1Labels = mixedMoment B raw41939step2 raw41939step2Labels := by
      have ha : raw41939step2 = (fun i j => raw41939step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41939step2 raw41939step1; decide +kernel
      have hl : raw41939step2Labels = raw41939step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41939step1 raw41939step1Labels permutation13 permutation7
    mixedMoment B raw41939step2 raw41939step2Labels = mixedMoment B raw41939step3 raw41939step3Labels := by
      have ha : raw41939step3 = -raw41939step2 := by apply Matrix.ext; change ∀ i j, raw41939step3 i j = -(raw41939step2 i j); unfold raw41939step3 raw41939step2; decide +kernel
      have hl : raw41939step3Labels = raw41939step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41939step3 raw41939step3Labels = mixedMoment B raw41939step4 raw41939step4Labels := by
      have ha : raw41939step4 = raw41939step3 := by apply Matrix.ext; unfold raw41939step4 raw41939step3; decide +kernel
      have hl : raw41939step3Labels = labelEmbedding6 ∘ raw41939step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41939step3 raw41939step3Labels raw41939step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4374 node4374Labels := by rfl

def raw41940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41940Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41940step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw41940step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw41940step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41940 raw41940Labels = mixedMoment B node1688 node1688Labels := by
  calc
    mixedMoment B raw41940 raw41940Labels = mixedMoment B raw41940step0 raw41940step0Labels := by
      have hz : ∀ j, raw41940 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41940step0 = (fun i j => raw41940 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41940step0 raw41940; decide +kernel
      have hl : raw41940step0Labels = raw41940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41940 raw41940Labels permutation265 hz
    mixedMoment B raw41940step0 raw41940step0Labels = mixedMoment B raw41940step1 raw41940step1Labels := by
      have ha : raw41940step1 = (fun i j => raw41940step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41940step1 raw41940step0; decide +kernel
      have hl : raw41940step1Labels = raw41940step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41940step0 raw41940step0Labels permutation37 permutation2
    mixedMoment B raw41940step1 raw41940step1Labels = mixedMoment B raw41940step2 raw41940step2Labels := by
      have ha : raw41940step2 = raw41940step1 := by apply Matrix.ext; unfold raw41940step2 raw41940step1; decide +kernel
      have hl : raw41940step1Labels = labelEmbedding1 ∘ raw41940step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41940step1 raw41940step1Labels raw41940step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1688 node1688Labels := by rfl

def raw41941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41941Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41941step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw41941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41941 raw41941Labels = mixedMoment B node4333 node4333Labels := by
  calc
    mixedMoment B raw41941 raw41941Labels = mixedMoment B raw41941step0 raw41941step0Labels := by
      have hz : ∀ j, raw41941 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41941step0 = (fun i j => raw41941 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41941step0 raw41941; decide +kernel
      have hl : raw41941step0Labels = raw41941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41941 raw41941Labels permutation265 hz
    mixedMoment B raw41941step0 raw41941step0Labels = mixedMoment B raw41941step1 raw41941step1Labels := by
      have ha : raw41941step1 = (fun i j => raw41941step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41941step1 raw41941step0; decide +kernel
      have hl : raw41941step1Labels = raw41941step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41941step0 raw41941step0Labels permutation97 permutation6
    _ = mixedMoment B node4333 node4333Labels := by rfl

def raw41942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41942Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41942step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw41942step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw41942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41942 raw41942Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw41942 raw41942Labels = mixedMoment B raw41942step0 raw41942step0Labels := by
      have hz : ∀ j, raw41942 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41942step0 = (fun i j => raw41942 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41942step0 raw41942; decide +kernel
      have hl : raw41942step0Labels = raw41942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41942 raw41942Labels permutation265 hz
    mixedMoment B raw41942step0 raw41942step0Labels = mixedMoment B raw41942step1 raw41942step1Labels := by
      have ha : raw41942step1 = (fun i j => raw41942step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41942step1 raw41942step0; decide +kernel
      have hl : raw41942step1Labels = raw41942step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41942step0 raw41942step0Labels permutation37 permutation2
    mixedMoment B raw41942step1 raw41942step1Labels = mixedMoment B raw41942step2 raw41942step2Labels := by
      have ha : raw41942step2 = raw41942step1 := by apply Matrix.ext; unfold raw41942step2 raw41942step1; decide +kernel
      have hl : raw41942step1Labels = labelEmbedding1 ∘ raw41942step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41942step1 raw41942step1Labels raw41942step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

def raw41943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41943Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41943step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw41943step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41943step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41943step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41943step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41943 raw41943Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw41943 raw41943Labels = mixedMoment B raw41943step0 raw41943step0Labels := by
      have hz : ∀ j, raw41943 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41943step0 = (fun i j => raw41943 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41943step0 raw41943; decide +kernel
      have hl : raw41943step0Labels = raw41943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41943 raw41943Labels permutation265 hz
    mixedMoment B raw41943step0 raw41943step0Labels = mixedMoment B raw41943step1 raw41943step1Labels := by
      have ha : raw41943step1 = (fun i j => raw41943step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41943step1 raw41943step0; decide +kernel
      have hl : raw41943step1Labels = raw41943step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41943step0 raw41943step0Labels permutation37 permutation7
    mixedMoment B raw41943step1 raw41943step1Labels = mixedMoment B raw41943step2 raw41943step2Labels := by
      have ha : raw41943step2 = -raw41943step1 := by apply Matrix.ext; change ∀ i j, raw41943step2 i j = -(raw41943step1 i j); unfold raw41943step2 raw41943step1; decide +kernel
      have hl : raw41943step2Labels = raw41943step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41943step2 raw41943step2Labels = mixedMoment B raw41943step3 raw41943step3Labels := by
      have ha : raw41943step3 = raw41943step2 := by apply Matrix.ext; unfold raw41943step3 raw41943step2; decide +kernel
      have hl : raw41943step2Labels = labelEmbedding6 ∘ raw41943step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41943step2 raw41943step2Labels raw41943step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4335 node4335Labels := by rfl

def raw41944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41944Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41944step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41944step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41944step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41944 raw41944Labels = mixedMoment B node1529 node1529Labels := by
  calc
    mixedMoment B raw41944 raw41944Labels = mixedMoment B raw41944step0 raw41944step0Labels := by
      have hz : ∀ j, raw41944 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41944step0 = (fun i j => raw41944 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41944step0 raw41944; decide +kernel
      have hl : raw41944step0Labels = raw41944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41944 raw41944Labels permutation434 hz
    mixedMoment B raw41944step0 raw41944step0Labels = mixedMoment B raw41944step1 raw41944step1Labels := by
      have hz : ∀ j, raw41944step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41944step1 = (fun i j => raw41944step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41944step1 raw41944step0; decide +kernel
      have hl : raw41944step1Labels = raw41944step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41944step0 raw41944step0Labels permutation80 hz
    mixedMoment B raw41944step1 raw41944step1Labels = mixedMoment B raw41944step2 raw41944step2Labels := by
      have ha : raw41944step2 = raw41944step1 := by apply Matrix.ext; unfold raw41944step2 raw41944step1; decide +kernel
      have hl : raw41944step1Labels = labelEmbedding1 ∘ raw41944step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41944step1 raw41944step1Labels raw41944step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1529 node1529Labels := by rfl

def raw41945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41945Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41945step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41945step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41945step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw41945step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41945step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw41945step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41945step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw41945step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41945 raw41945Labels = mixedMoment B node4162 node4162Labels := by
  calc
    mixedMoment B raw41945 raw41945Labels = mixedMoment B raw41945step0 raw41945step0Labels := by
      have hz : ∀ j, raw41945 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41945step0 = (fun i j => raw41945 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41945step0 raw41945; decide +kernel
      have hl : raw41945step0Labels = raw41945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41945 raw41945Labels permutation434 hz
    mixedMoment B raw41945step0 raw41945step0Labels = mixedMoment B raw41945step1 raw41945step1Labels := by
      have hz : ∀ j, raw41945step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41945step1 = (fun i j => raw41945step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41945step1 raw41945step0; decide +kernel
      have hl : raw41945step1Labels = raw41945step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41945step0 raw41945step0Labels permutation80 hz
    mixedMoment B raw41945step1 raw41945step1Labels = mixedMoment B raw41945step2 raw41945step2Labels := by
      have ha : raw41945step2 = (fun i j => raw41945step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41945step2 raw41945step1; decide +kernel
      have hl : raw41945step2Labels = raw41945step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41945step1 raw41945step1Labels permutation11 permutation7
    mixedMoment B raw41945step2 raw41945step2Labels = mixedMoment B raw41945step3 raw41945step3Labels := by
      have ha : raw41945step3 = -raw41945step2 := by apply Matrix.ext; change ∀ i j, raw41945step3 i j = -(raw41945step2 i j); unfold raw41945step3 raw41945step2; decide +kernel
      have hl : raw41945step3Labels = raw41945step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41945step3 raw41945step3Labels = mixedMoment B raw41945step4 raw41945step4Labels := by
      have ha : raw41945step4 = raw41945step3 := by apply Matrix.ext; unfold raw41945step4 raw41945step3; decide +kernel
      have hl : raw41945step3Labels = labelEmbedding6 ∘ raw41945step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41945step3 raw41945step3Labels raw41945step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4162 node4162Labels := by rfl

def raw41946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41946Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41946step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41946 raw41946Labels = mixedMoment B node1528 node1528Labels := by
  calc
    mixedMoment B raw41946 raw41946Labels = mixedMoment B raw41946step0 raw41946step0Labels := by
      have hz : ∀ j, raw41946 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41946step0 = (fun i j => raw41946 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41946step0 raw41946; decide +kernel
      have hl : raw41946step0Labels = raw41946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41946 raw41946Labels permutation346 hz
    mixedMoment B raw41946step0 raw41946step0Labels = mixedMoment B raw41946step1 raw41946step1Labels := by
      have ha : raw41946step1 = (fun i j => raw41946step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41946step1 raw41946step0; decide +kernel
      have hl : raw41946step1Labels = raw41946step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41946step0 raw41946step0Labels permutation36 permutation2
    mixedMoment B raw41946step1 raw41946step1Labels = mixedMoment B raw41946step2 raw41946step2Labels := by
      have ha : raw41946step2 = raw41946step1 := by apply Matrix.ext; unfold raw41946step2 raw41946step1; decide +kernel
      have hl : raw41946step1Labels = labelEmbedding1 ∘ raw41946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41946step1 raw41946step1Labels raw41946step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1528 node1528Labels := by rfl

def raw41947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41947Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41947step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw41947step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41947step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41947step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw41947step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41947 raw41947Labels = mixedMoment B node4157 node4157Labels := by
  calc
    mixedMoment B raw41947 raw41947Labels = mixedMoment B raw41947step0 raw41947step0Labels := by
      have hz : ∀ j, raw41947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41947step0 = (fun i j => raw41947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41947step0 raw41947; decide +kernel
      have hl : raw41947step0Labels = raw41947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41947 raw41947Labels permutation346 hz
    mixedMoment B raw41947step0 raw41947step0Labels = mixedMoment B raw41947step1 raw41947step1Labels := by
      have ha : raw41947step1 = (fun i j => raw41947step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41947step1 raw41947step0; decide +kernel
      have hl : raw41947step1Labels = raw41947step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41947step0 raw41947step0Labels permutation53 permutation7
    mixedMoment B raw41947step1 raw41947step1Labels = mixedMoment B raw41947step2 raw41947step2Labels := by
      have ha : raw41947step2 = -raw41947step1 := by apply Matrix.ext; change ∀ i j, raw41947step2 i j = -(raw41947step1 i j); unfold raw41947step2 raw41947step1; decide +kernel
      have hl : raw41947step2Labels = raw41947step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41947step2 raw41947step2Labels = mixedMoment B raw41947step3 raw41947step3Labels := by
      have ha : raw41947step3 = raw41947step2 := by apply Matrix.ext; unfold raw41947step3 raw41947step2; decide +kernel
      have hl : raw41947step2Labels = labelEmbedding6 ∘ raw41947step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41947step2 raw41947step2Labels raw41947step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4157 node4157Labels := by rfl

def raw41948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41948Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41948step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41948 raw41948Labels = mixedMoment B node1511 node1511Labels := by
  calc
    mixedMoment B raw41948 raw41948Labels = mixedMoment B raw41948step0 raw41948step0Labels := by
      have hz : ∀ j, raw41948 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41948step0 = (fun i j => raw41948 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41948step0 raw41948; decide +kernel
      have hl : raw41948step0Labels = raw41948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41948 raw41948Labels permutation434 hz
    mixedMoment B raw41948step0 raw41948step0Labels = mixedMoment B raw41948step1 raw41948step1Labels := by
      have ha : raw41948step1 = (fun i j => raw41948step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41948step1 raw41948step0; decide +kernel
      have hl : raw41948step1Labels = raw41948step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41948step0 raw41948step0Labels permutation38 permutation2
    mixedMoment B raw41948step1 raw41948step1Labels = mixedMoment B raw41948step2 raw41948step2Labels := by
      have ha : raw41948step2 = raw41948step1 := by apply Matrix.ext; unfold raw41948step2 raw41948step1; decide +kernel
      have hl : raw41948step1Labels = labelEmbedding1 ∘ raw41948step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41948step1 raw41948step1Labels raw41948step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1511 node1511Labels := by rfl

def raw41949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41949Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41949step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw41949step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41949step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41949step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw41949step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41949 raw41949Labels = mixedMoment B node4154 node4154Labels := by
  calc
    mixedMoment B raw41949 raw41949Labels = mixedMoment B raw41949step0 raw41949step0Labels := by
      have hz : ∀ j, raw41949 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41949step0 = (fun i j => raw41949 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41949step0 raw41949; decide +kernel
      have hl : raw41949step0Labels = raw41949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41949 raw41949Labels permutation434 hz
    mixedMoment B raw41949step0 raw41949step0Labels = mixedMoment B raw41949step1 raw41949step1Labels := by
      have ha : raw41949step1 = (fun i j => raw41949step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41949step1 raw41949step0; decide +kernel
      have hl : raw41949step1Labels = raw41949step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41949step0 raw41949step0Labels permutation46 permutation7
    mixedMoment B raw41949step1 raw41949step1Labels = mixedMoment B raw41949step2 raw41949step2Labels := by
      have ha : raw41949step2 = -raw41949step1 := by apply Matrix.ext; change ∀ i j, raw41949step2 i j = -(raw41949step1 i j); unfold raw41949step2 raw41949step1; decide +kernel
      have hl : raw41949step2Labels = raw41949step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41949step2 raw41949step2Labels = mixedMoment B raw41949step3 raw41949step3Labels := by
      have ha : raw41949step3 = raw41949step2 := by apply Matrix.ext; unfold raw41949step3 raw41949step2; decide +kernel
      have hl : raw41949step2Labels = labelEmbedding6 ∘ raw41949step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41949step2 raw41949step2Labels raw41949step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4154 node4154Labels := by rfl

def raw41950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41950Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41950step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41950step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41950 raw41950Labels = mixedMoment B node1510 node1510Labels := by
  calc
    mixedMoment B raw41950 raw41950Labels = mixedMoment B raw41950step0 raw41950step0Labels := by
      have ha : raw41950step0 = (fun i j => raw41950 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41950step0 raw41950; decide +kernel
      have hl : raw41950step0Labels = raw41950Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41950 raw41950Labels permutation180 permutation2
    mixedMoment B raw41950step0 raw41950step0Labels = mixedMoment B raw41950step1 raw41950step1Labels := by
      have ha : raw41950step1 = raw41950step0 := by apply Matrix.ext; unfold raw41950step1 raw41950step0; decide +kernel
      have hl : raw41950step0Labels = labelEmbedding1 ∘ raw41950step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41950step0 raw41950step0Labels raw41950step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1510 node1510Labels := by rfl

def raw41951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41951Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41951step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41951step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41951step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41951step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41951step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41951 raw41951Labels = mixedMoment B node4152 node4152Labels := by
  calc
    mixedMoment B raw41951 raw41951Labels = mixedMoment B raw41951step0 raw41951step0Labels := by
      have ha : raw41951step0 = (fun i j => raw41951 (permutation255 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41951step0 raw41951; decide +kernel
      have hl : raw41951step0Labels = raw41951Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41951 raw41951Labels permutation255 permutation7
    mixedMoment B raw41951step0 raw41951step0Labels = mixedMoment B raw41951step1 raw41951step1Labels := by
      have ha : raw41951step1 = -raw41951step0 := by apply Matrix.ext; change ∀ i j, raw41951step1 i j = -(raw41951step0 i j); unfold raw41951step1 raw41951step0; decide +kernel
      have hl : raw41951step1Labels = raw41951step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41951step1 raw41951step1Labels = mixedMoment B raw41951step2 raw41951step2Labels := by
      have ha : raw41951step2 = raw41951step1 := by apply Matrix.ext; unfold raw41951step2 raw41951step1; decide +kernel
      have hl : raw41951step1Labels = labelEmbedding6 ∘ raw41951step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41951step1 raw41951step1Labels raw41951step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4152 node4152Labels := by rfl

def raw41952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41952Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41952step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41952step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41952step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41952step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41952 raw41952Labels = mixedMoment B node1523 node1523Labels := by
  calc
    mixedMoment B raw41952 raw41952Labels = mixedMoment B raw41952step0 raw41952step0Labels := by
      have hz : ∀ j, raw41952 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41952step0 = (fun i j => raw41952 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41952step0 raw41952; decide +kernel
      have hl : raw41952step0Labels = raw41952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41952 raw41952Labels permutation434 hz
    mixedMoment B raw41952step0 raw41952step0Labels = mixedMoment B raw41952step1 raw41952step1Labels := by
      have hz : ∀ j, raw41952step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41952step1 = (fun i j => raw41952step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41952step1 raw41952step0; decide +kernel
      have hl : raw41952step1Labels = raw41952step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41952step0 raw41952step0Labels permutation80 hz
    mixedMoment B raw41952step1 raw41952step1Labels = mixedMoment B raw41952step2 raw41952step2Labels := by
      have ha : raw41952step2 = raw41952step1 := by apply Matrix.ext; unfold raw41952step2 raw41952step1; decide +kernel
      have hl : raw41952step1Labels = labelEmbedding1 ∘ raw41952step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41952step1 raw41952step1Labels raw41952step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1523 node1523Labels := by rfl

def raw41953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41953Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41953step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41953step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41953step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41953step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw41953step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41953step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41953step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41953step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw41953step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41953 raw41953Labels = mixedMoment B node4160 node4160Labels := by
  calc
    mixedMoment B raw41953 raw41953Labels = mixedMoment B raw41953step0 raw41953step0Labels := by
      have hz : ∀ j, raw41953 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41953step0 = (fun i j => raw41953 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41953step0 raw41953; decide +kernel
      have hl : raw41953step0Labels = raw41953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41953 raw41953Labels permutation434 hz
    mixedMoment B raw41953step0 raw41953step0Labels = mixedMoment B raw41953step1 raw41953step1Labels := by
      have hz : ∀ j, raw41953step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41953step1 = (fun i j => raw41953step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41953step1 raw41953step0; decide +kernel
      have hl : raw41953step1Labels = raw41953step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41953step0 raw41953step0Labels permutation80 hz
    mixedMoment B raw41953step1 raw41953step1Labels = mixedMoment B raw41953step2 raw41953step2Labels := by
      have ha : raw41953step2 = (fun i j => raw41953step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41953step2 raw41953step1; decide +kernel
      have hl : raw41953step2Labels = raw41953step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41953step1 raw41953step1Labels permutation10 permutation7
    mixedMoment B raw41953step2 raw41953step2Labels = mixedMoment B raw41953step3 raw41953step3Labels := by
      have ha : raw41953step3 = -raw41953step2 := by apply Matrix.ext; change ∀ i j, raw41953step3 i j = -(raw41953step2 i j); unfold raw41953step3 raw41953step2; decide +kernel
      have hl : raw41953step3Labels = raw41953step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41953step3 raw41953step3Labels = mixedMoment B raw41953step4 raw41953step4Labels := by
      have ha : raw41953step4 = raw41953step3 := by apply Matrix.ext; unfold raw41953step4 raw41953step3; decide +kernel
      have hl : raw41953step3Labels = labelEmbedding6 ∘ raw41953step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41953step3 raw41953step3Labels raw41953step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4160 node4160Labels := by rfl

def raw41954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41954Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41954step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41954step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41954 raw41954Labels = mixedMoment B node1522 node1522Labels := by
  calc
    mixedMoment B raw41954 raw41954Labels = mixedMoment B raw41954step0 raw41954step0Labels := by
      have hz : ∀ j, raw41954 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41954step0 = (fun i j => raw41954 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41954step0 raw41954; decide +kernel
      have hl : raw41954step0Labels = raw41954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41954 raw41954Labels permutation346 hz
    mixedMoment B raw41954step0 raw41954step0Labels = mixedMoment B raw41954step1 raw41954step1Labels := by
      have ha : raw41954step1 = (fun i j => raw41954step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41954step1 raw41954step0; decide +kernel
      have hl : raw41954step1Labels = raw41954step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41954step0 raw41954step0Labels permutation37 permutation2
    mixedMoment B raw41954step1 raw41954step1Labels = mixedMoment B raw41954step2 raw41954step2Labels := by
      have ha : raw41954step2 = raw41954step1 := by apply Matrix.ext; unfold raw41954step2 raw41954step1; decide +kernel
      have hl : raw41954step1Labels = labelEmbedding1 ∘ raw41954step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41954step1 raw41954step1Labels raw41954step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1522 node1522Labels := by rfl

def raw41955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41955Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41955step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw41955step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41955step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41955step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw41955step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41955 raw41955Labels = mixedMoment B node4158 node4158Labels := by
  calc
    mixedMoment B raw41955 raw41955Labels = mixedMoment B raw41955step0 raw41955step0Labels := by
      have hz : ∀ j, raw41955 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41955step0 = (fun i j => raw41955 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41955step0 raw41955; decide +kernel
      have hl : raw41955step0Labels = raw41955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41955 raw41955Labels permutation346 hz
    mixedMoment B raw41955step0 raw41955step0Labels = mixedMoment B raw41955step1 raw41955step1Labels := by
      have ha : raw41955step1 = (fun i j => raw41955step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41955step1 raw41955step0; decide +kernel
      have hl : raw41955step1Labels = raw41955step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41955step0 raw41955step0Labels permutation54 permutation7
    mixedMoment B raw41955step1 raw41955step1Labels = mixedMoment B raw41955step2 raw41955step2Labels := by
      have ha : raw41955step2 = -raw41955step1 := by apply Matrix.ext; change ∀ i j, raw41955step2 i j = -(raw41955step1 i j); unfold raw41955step2 raw41955step1; decide +kernel
      have hl : raw41955step2Labels = raw41955step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41955step2 raw41955step2Labels = mixedMoment B raw41955step3 raw41955step3Labels := by
      have ha : raw41955step3 = raw41955step2 := by apply Matrix.ext; unfold raw41955step3 raw41955step2; decide +kernel
      have hl : raw41955step2Labels = labelEmbedding6 ∘ raw41955step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41955step2 raw41955step2Labels raw41955step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4158 node4158Labels := by rfl

def raw41956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41956Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41956step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41956 raw41956Labels = mixedMoment B node1501 node1501Labels := by
  calc
    mixedMoment B raw41956 raw41956Labels = mixedMoment B raw41956step0 raw41956step0Labels := by
      have ha : raw41956step0 = raw41956 := by apply Matrix.ext; unfold raw41956step0 raw41956; decide +kernel
      have hl : raw41956Labels = labelEmbedding1 ∘ raw41956step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41956 raw41956Labels raw41956step0Labels labelEmbedding1 hl
    _ = mixedMoment B node1501 node1501Labels := by rfl

def raw41957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41957Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw41957step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41957step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41957step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41957step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41957 raw41957Labels = mixedMoment B node4149 node4149Labels := by
  calc
    mixedMoment B raw41957 raw41957Labels = mixedMoment B raw41957step0 raw41957step0Labels := by
      have ha : raw41957step0 = (fun i j => raw41957 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41957step0 raw41957; decide +kernel
      have hl : raw41957step0Labels = raw41957Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41957 raw41957Labels permutation224 permutation7
    mixedMoment B raw41957step0 raw41957step0Labels = mixedMoment B raw41957step1 raw41957step1Labels := by
      have ha : raw41957step1 = -raw41957step0 := by apply Matrix.ext; change ∀ i j, raw41957step1 i j = -(raw41957step0 i j); unfold raw41957step1 raw41957step0; decide +kernel
      have hl : raw41957step1Labels = raw41957step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41957step1 raw41957step1Labels = mixedMoment B raw41957step2 raw41957step2Labels := by
      have ha : raw41957step2 = raw41957step1 := by apply Matrix.ext; unfold raw41957step2 raw41957step1; decide +kernel
      have hl : raw41957step1Labels = labelEmbedding6 ∘ raw41957step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41957step1 raw41957step1Labels raw41957step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4149 node4149Labels := by rfl

def raw41958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41958Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw41958step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw41958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41958 raw41958Labels = mixedMoment B node1505 node1505Labels := by
  calc
    mixedMoment B raw41958 raw41958Labels = mixedMoment B raw41958step0 raw41958step0Labels := by
      have hz : ∀ j, raw41958 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41958step0 = (fun i j => raw41958 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41958step0 raw41958; decide +kernel
      have hl : raw41958step0Labels = raw41958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41958 raw41958Labels permutation434 hz
    mixedMoment B raw41958step0 raw41958step0Labels = mixedMoment B raw41958step1 raw41958step1Labels := by
      have ha : raw41958step1 = raw41958step0 := by apply Matrix.ext; unfold raw41958step1 raw41958step0; decide +kernel
      have hl : raw41958step0Labels = labelEmbedding1 ∘ raw41958step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41958step0 raw41958step0Labels raw41958step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1505 node1505Labels := by rfl

def raw41959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41959Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw41959step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw41959step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41959step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41959step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41959step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw41959step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41959 raw41959Labels = mixedMoment B node4151 node4151Labels := by
  calc
    mixedMoment B raw41959 raw41959Labels = mixedMoment B raw41959step0 raw41959step0Labels := by
      have hz : ∀ j, raw41959 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41959step0 = (fun i j => raw41959 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41959step0 raw41959; decide +kernel
      have hl : raw41959step0Labels = raw41959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41959 raw41959Labels permutation434 hz
    mixedMoment B raw41959step0 raw41959step0Labels = mixedMoment B raw41959step1 raw41959step1Labels := by
      have ha : raw41959step1 = (fun i j => raw41959step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41959step1 raw41959step0; decide +kernel
      have hl : raw41959step1Labels = raw41959step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41959step0 raw41959step0Labels permutation44 permutation7
    mixedMoment B raw41959step1 raw41959step1Labels = mixedMoment B raw41959step2 raw41959step2Labels := by
      have ha : raw41959step2 = -raw41959step1 := by apply Matrix.ext; change ∀ i j, raw41959step2 i j = -(raw41959step1 i j); unfold raw41959step2 raw41959step1; decide +kernel
      have hl : raw41959step2Labels = raw41959step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41959step2 raw41959step2Labels = mixedMoment B raw41959step3 raw41959step3Labels := by
      have ha : raw41959step3 = raw41959step2 := by apply Matrix.ext; unfold raw41959step3 raw41959step2; decide +kernel
      have hl : raw41959step2Labels = labelEmbedding6 ∘ raw41959step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41959step2 raw41959step2Labels raw41959step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4151 node4151Labels := by rfl

def raw41960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41960Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41960step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41960step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41960 raw41960Labels = mixedMoment B node1504 node1504Labels := by
  calc
    mixedMoment B raw41960 raw41960Labels = mixedMoment B raw41960step0 raw41960step0Labels := by
      have ha : raw41960step0 = (fun i j => raw41960 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41960step0 raw41960; decide +kernel
      have hl : raw41960step0Labels = raw41960Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41960 raw41960Labels permutation157 permutation2
    mixedMoment B raw41960step0 raw41960step0Labels = mixedMoment B raw41960step1 raw41960step1Labels := by
      have ha : raw41960step1 = raw41960step0 := by apply Matrix.ext; unfold raw41960step1 raw41960step0; decide +kernel
      have hl : raw41960step0Labels = labelEmbedding1 ∘ raw41960step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41960step0 raw41960step0Labels raw41960step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1504 node1504Labels := by rfl

def raw41961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41961Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw41961step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41961step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41961step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41961step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41961step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41961 raw41961Labels = mixedMoment B node4150 node4150Labels := by
  calc
    mixedMoment B raw41961 raw41961Labels = mixedMoment B raw41961step0 raw41961step0Labels := by
      have ha : raw41961step0 = (fun i j => raw41961 (permutation247 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41961step0 raw41961; decide +kernel
      have hl : raw41961step0Labels = raw41961Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41961 raw41961Labels permutation247 permutation7
    mixedMoment B raw41961step0 raw41961step0Labels = mixedMoment B raw41961step1 raw41961step1Labels := by
      have ha : raw41961step1 = -raw41961step0 := by apply Matrix.ext; change ∀ i j, raw41961step1 i j = -(raw41961step0 i j); unfold raw41961step1 raw41961step0; decide +kernel
      have hl : raw41961step1Labels = raw41961step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41961step1 raw41961step1Labels = mixedMoment B raw41961step2 raw41961step2Labels := by
      have ha : raw41961step2 = raw41961step1 := by apply Matrix.ext; unfold raw41961step2 raw41961step1; decide +kernel
      have hl : raw41961step1Labels = labelEmbedding6 ∘ raw41961step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41961step1 raw41961step1Labels raw41961step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4150 node4150Labels := by rfl

def raw41962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw41962Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw41962step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41962 raw41962Labels = mixedMoment B node1516 node1516Labels := by
  calc
    mixedMoment B raw41962 raw41962Labels = mixedMoment B raw41962step0 raw41962step0Labels := by
      have hz : ∀ j, raw41962 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41962step0 = (fun i j => raw41962 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41962step0 raw41962; decide +kernel
      have hl : raw41962step0Labels = raw41962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41962 raw41962Labels permutation434 hz
    mixedMoment B raw41962step0 raw41962step0Labels = mixedMoment B raw41962step1 raw41962step1Labels := by
      have hz : ∀ j, raw41962step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41962step1 = (fun i j => raw41962step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41962step1 raw41962step0; decide +kernel
      have hl : raw41962step1Labels = raw41962step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41962step0 raw41962step0Labels permutation80 hz
    mixedMoment B raw41962step1 raw41962step1Labels = mixedMoment B raw41962step2 raw41962step2Labels := by
      have ha : raw41962step2 = raw41962step1 := by apply Matrix.ext; unfold raw41962step2 raw41962step1; decide +kernel
      have hl : raw41962step1Labels = labelEmbedding1 ∘ raw41962step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41962step1 raw41962step1Labels raw41962step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1516 node1516Labels := by rfl

def raw41963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw41963Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw41963step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41963step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41963step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw41963step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41963step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw41963step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41963step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw41963step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41963 raw41963Labels = mixedMoment B node4156 node4156Labels := by
  calc
    mixedMoment B raw41963 raw41963Labels = mixedMoment B raw41963step0 raw41963step0Labels := by
      have hz : ∀ j, raw41963 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41963step0 = (fun i j => raw41963 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41963step0 raw41963; decide +kernel
      have hl : raw41963step0Labels = raw41963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41963 raw41963Labels permutation434 hz
    mixedMoment B raw41963step0 raw41963step0Labels = mixedMoment B raw41963step1 raw41963step1Labels := by
      have hz : ∀ j, raw41963step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41963step1 = (fun i j => raw41963step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41963step1 raw41963step0; decide +kernel
      have hl : raw41963step1Labels = raw41963step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41963step0 raw41963step0Labels permutation80 hz
    mixedMoment B raw41963step1 raw41963step1Labels = mixedMoment B raw41963step2 raw41963step2Labels := by
      have ha : raw41963step2 = (fun i j => raw41963step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41963step2 raw41963step1; decide +kernel
      have hl : raw41963step2Labels = raw41963step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41963step1 raw41963step1Labels permutation10 permutation7
    mixedMoment B raw41963step2 raw41963step2Labels = mixedMoment B raw41963step3 raw41963step3Labels := by
      have ha : raw41963step3 = -raw41963step2 := by apply Matrix.ext; change ∀ i j, raw41963step3 i j = -(raw41963step2 i j); unfold raw41963step3 raw41963step2; decide +kernel
      have hl : raw41963step3Labels = raw41963step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41963step3 raw41963step3Labels = mixedMoment B raw41963step4 raw41963step4Labels := by
      have ha : raw41963step4 = raw41963step3 := by apply Matrix.ext; unfold raw41963step4 raw41963step3; decide +kernel
      have hl : raw41963step3Labels = labelEmbedding6 ∘ raw41963step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41963step3 raw41963step3Labels raw41963step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4156 node4156Labels := by rfl

def raw41964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41964Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41964step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw41964step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw41964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41964 raw41964Labels = mixedMoment B node1514 node1514Labels := by
  calc
    mixedMoment B raw41964 raw41964Labels = mixedMoment B raw41964step0 raw41964step0Labels := by
      have hz : ∀ j, raw41964 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41964step0 = (fun i j => raw41964 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41964step0 raw41964; decide +kernel
      have hl : raw41964step0Labels = raw41964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41964 raw41964Labels permutation346 hz
    mixedMoment B raw41964step0 raw41964step0Labels = mixedMoment B raw41964step1 raw41964step1Labels := by
      have ha : raw41964step1 = (fun i j => raw41964step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41964step1 raw41964step0; decide +kernel
      have hl : raw41964step1Labels = raw41964step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41964step0 raw41964step0Labels permutation37 permutation2
    mixedMoment B raw41964step1 raw41964step1Labels = mixedMoment B raw41964step2 raw41964step2Labels := by
      have ha : raw41964step2 = raw41964step1 := by apply Matrix.ext; unfold raw41964step2 raw41964step1; decide +kernel
      have hl : raw41964step1Labels = labelEmbedding1 ∘ raw41964step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41964step1 raw41964step1Labels raw41964step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1514 node1514Labels := by rfl

def raw41965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41965Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41965step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw41965step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41965step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41965step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw41965step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41965 raw41965Labels = mixedMoment B node4153 node4153Labels := by
  calc
    mixedMoment B raw41965 raw41965Labels = mixedMoment B raw41965step0 raw41965step0Labels := by
      have hz : ∀ j, raw41965 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41965step0 = (fun i j => raw41965 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41965step0 raw41965; decide +kernel
      have hl : raw41965step0Labels = raw41965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41965 raw41965Labels permutation346 hz
    mixedMoment B raw41965step0 raw41965step0Labels = mixedMoment B raw41965step1 raw41965step1Labels := by
      have ha : raw41965step1 = (fun i j => raw41965step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41965step1 raw41965step0; decide +kernel
      have hl : raw41965step1Labels = raw41965step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41965step0 raw41965step0Labels permutation51 permutation7
    mixedMoment B raw41965step1 raw41965step1Labels = mixedMoment B raw41965step2 raw41965step2Labels := by
      have ha : raw41965step2 = -raw41965step1 := by apply Matrix.ext; change ∀ i j, raw41965step2 i j = -(raw41965step1 i j); unfold raw41965step2 raw41965step1; decide +kernel
      have hl : raw41965step2Labels = raw41965step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41965step2 raw41965step2Labels = mixedMoment B raw41965step3 raw41965step3Labels := by
      have ha : raw41965step3 = raw41965step2 := by apply Matrix.ext; unfold raw41965step3 raw41965step2; decide +kernel
      have hl : raw41965step2Labels = labelEmbedding6 ∘ raw41965step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41965step2 raw41965step2Labels raw41965step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4153 node4153Labels := by rfl

def raw41966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41966Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41966step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw41966step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41966step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw41966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41966 raw41966Labels = mixedMoment B node1515 node1515Labels := by
  calc
    mixedMoment B raw41966 raw41966Labels = mixedMoment B raw41966step0 raw41966step0Labels := by
      have hz : ∀ j, raw41966 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41966step0 = (fun i j => raw41966 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41966step0 raw41966; decide +kernel
      have hl : raw41966step0Labels = raw41966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41966 raw41966Labels permutation346 hz
    mixedMoment B raw41966step0 raw41966step0Labels = mixedMoment B raw41966step1 raw41966step1Labels := by
      have ha : raw41966step1 = (fun i j => raw41966step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41966step1 raw41966step0; decide +kernel
      have hl : raw41966step1Labels = raw41966step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41966step0 raw41966step0Labels permutation36 permutation2
    mixedMoment B raw41966step1 raw41966step1Labels = mixedMoment B raw41966step2 raw41966step2Labels := by
      have ha : raw41966step2 = raw41966step1 := by apply Matrix.ext; unfold raw41966step2 raw41966step1; decide +kernel
      have hl : raw41966step1Labels = labelEmbedding1 ∘ raw41966step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41966step1 raw41966step1Labels raw41966step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1515 node1515Labels := by rfl

def raw41967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41967Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41967step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw41967step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41967step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41967step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw41967step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41967 raw41967Labels = mixedMoment B node4155 node4155Labels := by
  calc
    mixedMoment B raw41967 raw41967Labels = mixedMoment B raw41967step0 raw41967step0Labels := by
      have hz : ∀ j, raw41967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41967step0 = (fun i j => raw41967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41967step0 raw41967; decide +kernel
      have hl : raw41967step0Labels = raw41967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41967 raw41967Labels permutation346 hz
    mixedMoment B raw41967step0 raw41967step0Labels = mixedMoment B raw41967step1 raw41967step1Labels := by
      have ha : raw41967step1 = (fun i j => raw41967step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41967step1 raw41967step0; decide +kernel
      have hl : raw41967step1Labels = raw41967step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41967step0 raw41967step0Labels permutation50 permutation7
    mixedMoment B raw41967step1 raw41967step1Labels = mixedMoment B raw41967step2 raw41967step2Labels := by
      have ha : raw41967step2 = -raw41967step1 := by apply Matrix.ext; change ∀ i j, raw41967step2 i j = -(raw41967step1 i j); unfold raw41967step2 raw41967step1; decide +kernel
      have hl : raw41967step2Labels = raw41967step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41967step2 raw41967step2Labels = mixedMoment B raw41967step3 raw41967step3Labels := by
      have ha : raw41967step3 = raw41967step2 := by apply Matrix.ext; unfold raw41967step3 raw41967step2; decide +kernel
      have hl : raw41967step2Labels = labelEmbedding6 ∘ raw41967step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41967step2 raw41967step2Labels raw41967step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4155 node4155Labels := by rfl

def raw41968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41968Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41968step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41968step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41968step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw41968step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41968step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw41968step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41968 raw41968Labels = mixedMoment B node1534 node1534Labels := by
  calc
    mixedMoment B raw41968 raw41968Labels = mixedMoment B raw41968step0 raw41968step0Labels := by
      have hz : ∀ j, raw41968 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41968step0 = (fun i j => raw41968 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41968step0 raw41968; decide +kernel
      have hl : raw41968step0Labels = raw41968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41968 raw41968Labels permutation434 hz
    mixedMoment B raw41968step0 raw41968step0Labels = mixedMoment B raw41968step1 raw41968step1Labels := by
      have hz : ∀ j, raw41968step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41968step1 = (fun i j => raw41968step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41968step1 raw41968step0; decide +kernel
      have hl : raw41968step1Labels = raw41968step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41968step0 raw41968step0Labels permutation80 hz
    mixedMoment B raw41968step1 raw41968step1Labels = mixedMoment B raw41968step2 raw41968step2Labels := by
      have hz : ∀ j, raw41968step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41968step2 = (fun i j => raw41968step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41968step2 raw41968step1; decide +kernel
      have hl : raw41968step2Labels = raw41968step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41968step1 raw41968step1Labels permutation14 hz
    mixedMoment B raw41968step2 raw41968step2Labels = mixedMoment B raw41968step3 raw41968step3Labels := by
      have ha : raw41968step3 = raw41968step2 := by apply Matrix.ext; unfold raw41968step3 raw41968step2; decide +kernel
      have hl : raw41968step2Labels = labelEmbedding1 ∘ raw41968step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41968step2 raw41968step2Labels raw41968step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1534 node1534Labels := by rfl

def raw41969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41969Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41969step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41969step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41969step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41969step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw41969step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41969step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![5, -3, -2]]
def raw41969step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41969 raw41969Labels = mixedMoment B node4163 node4163Labels := by
  calc
    mixedMoment B raw41969 raw41969Labels = mixedMoment B raw41969step0 raw41969step0Labels := by
      have hz : ∀ j, raw41969 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41969step0 = (fun i j => raw41969 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41969step0 raw41969; decide +kernel
      have hl : raw41969step0Labels = raw41969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41969 raw41969Labels permutation434 hz
    mixedMoment B raw41969step0 raw41969step0Labels = mixedMoment B raw41969step1 raw41969step1Labels := by
      have hz : ∀ j, raw41969step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41969step1 = (fun i j => raw41969step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41969step1 raw41969step0; decide +kernel
      have hl : raw41969step1Labels = raw41969step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41969step0 raw41969step0Labels permutation80 hz
    mixedMoment B raw41969step1 raw41969step1Labels = mixedMoment B raw41969step2 raw41969step2Labels := by
      have hz : ∀ j, raw41969step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41969step2 = (fun i j => raw41969step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41969step2 raw41969step1; decide +kernel
      have hl : raw41969step2Labels = raw41969step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41969step1 raw41969step1Labels permutation14 hz
    mixedMoment B raw41969step2 raw41969step2Labels = mixedMoment B raw41969step3 raw41969step3Labels := by
      have ha : raw41969step3 = (fun i j => raw41969step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41969step3 raw41969step2; decide +kernel
      have hl : raw41969step3Labels = raw41969step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41969step2 raw41969step2Labels permutation7 permutation6
    _ = mixedMoment B node4163 node4163Labels := by rfl

def raw41970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41970Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41970step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41970step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41970step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41970step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw41970step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41970step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw41970step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41970 raw41970Labels = mixedMoment B node1532 node1532Labels := by
  calc
    mixedMoment B raw41970 raw41970Labels = mixedMoment B raw41970step0 raw41970step0Labels := by
      have hz : ∀ j, raw41970 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41970step0 = (fun i j => raw41970 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41970step0 raw41970; decide +kernel
      have hl : raw41970step0Labels = raw41970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41970 raw41970Labels permutation346 hz
    mixedMoment B raw41970step0 raw41970step0Labels = mixedMoment B raw41970step1 raw41970step1Labels := by
      have hz : ∀ j, raw41970step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41970step1 = (fun i j => raw41970step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41970step1 raw41970step0; decide +kernel
      have hl : raw41970step1Labels = raw41970step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41970step0 raw41970step0Labels permutation56 hz
    mixedMoment B raw41970step1 raw41970step1Labels = mixedMoment B raw41970step2 raw41970step2Labels := by
      have ha : raw41970step2 = (fun i j => raw41970step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41970step2 raw41970step1; decide +kernel
      have hl : raw41970step2Labels = raw41970step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41970step1 raw41970step1Labels permutation13 permutation2
    mixedMoment B raw41970step2 raw41970step2Labels = mixedMoment B raw41970step3 raw41970step3Labels := by
      have ha : raw41970step3 = raw41970step2 := by apply Matrix.ext; unfold raw41970step3 raw41970step2; decide +kernel
      have hl : raw41970step2Labels = labelEmbedding1 ∘ raw41970step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41970step2 raw41970step2Labels raw41970step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1532 node1532Labels := by rfl

def raw41971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41971Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41971step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw41971step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41971step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-1, 0, 1], ![-4, 3, 1]]
def raw41971step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41971step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw41971step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41971step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw41971step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41971 raw41971Labels = mixedMoment B node4159 node4159Labels := by
  calc
    mixedMoment B raw41971 raw41971Labels = mixedMoment B raw41971step0 raw41971step0Labels := by
      have hz : ∀ j, raw41971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41971step0 = (fun i j => raw41971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41971step0 raw41971; decide +kernel
      have hl : raw41971step0Labels = raw41971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41971 raw41971Labels permutation346 hz
    mixedMoment B raw41971step0 raw41971step0Labels = mixedMoment B raw41971step1 raw41971step1Labels := by
      have hz : ∀ j, raw41971step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41971step1 = (fun i j => raw41971step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41971step1 raw41971step0; decide +kernel
      have hl : raw41971step1Labels = raw41971step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41971step0 raw41971step0Labels permutation56 hz
    mixedMoment B raw41971step1 raw41971step1Labels = mixedMoment B raw41971step2 raw41971step2Labels := by
      have ha : raw41971step2 = (fun i j => raw41971step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41971step2 raw41971step1; decide +kernel
      have hl : raw41971step2Labels = raw41971step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41971step1 raw41971step1Labels permutation13 permutation7
    mixedMoment B raw41971step2 raw41971step2Labels = mixedMoment B raw41971step3 raw41971step3Labels := by
      have ha : raw41971step3 = -raw41971step2 := by apply Matrix.ext; change ∀ i j, raw41971step3 i j = -(raw41971step2 i j); unfold raw41971step3 raw41971step2; decide +kernel
      have hl : raw41971step3Labels = raw41971step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41971step3 raw41971step3Labels = mixedMoment B raw41971step4 raw41971step4Labels := by
      have ha : raw41971step4 = raw41971step3 := by apply Matrix.ext; unfold raw41971step4 raw41971step3; decide +kernel
      have hl : raw41971step3Labels = labelEmbedding6 ∘ raw41971step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41971step3 raw41971step3Labels raw41971step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4159 node4159Labels := by rfl

def raw41972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41972Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41972step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41972step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw41972step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw41972step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41972 raw41972Labels = mixedMoment B node1533 node1533Labels := by
  calc
    mixedMoment B raw41972 raw41972Labels = mixedMoment B raw41972step0 raw41972step0Labels := by
      have hz : ∀ j, raw41972 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41972step0 = (fun i j => raw41972 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41972step0 raw41972; decide +kernel
      have hl : raw41972step0Labels = raw41972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41972 raw41972Labels permutation346 hz
    mixedMoment B raw41972step0 raw41972step0Labels = mixedMoment B raw41972step1 raw41972step1Labels := by
      have hz : ∀ j, raw41972step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41972step1 = (fun i j => raw41972step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41972step1 raw41972step0; decide +kernel
      have hl : raw41972step1Labels = raw41972step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41972step0 raw41972step0Labels permutation56 hz
    mixedMoment B raw41972step1 raw41972step1Labels = mixedMoment B raw41972step2 raw41972step2Labels := by
      have ha : raw41972step2 = (fun i j => raw41972step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41972step2 raw41972step1; decide +kernel
      have hl : raw41972step2Labels = raw41972step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41972step1 raw41972step1Labels permutation13 permutation2
    mixedMoment B raw41972step2 raw41972step2Labels = mixedMoment B raw41972step3 raw41972step3Labels := by
      have ha : raw41972step3 = raw41972step2 := by apply Matrix.ext; unfold raw41972step3 raw41972step2; decide +kernel
      have hl : raw41972step2Labels = labelEmbedding1 ∘ raw41972step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41972step2 raw41972step2Labels raw41972step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1533 node1533Labels := by rfl

def raw41973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41973Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41973step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw41973step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41973step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw41973step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41973step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41973step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41973step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw41973step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41973 raw41973Labels = mixedMoment B node4161 node4161Labels := by
  calc
    mixedMoment B raw41973 raw41973Labels = mixedMoment B raw41973step0 raw41973step0Labels := by
      have hz : ∀ j, raw41973 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41973step0 = (fun i j => raw41973 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41973step0 raw41973; decide +kernel
      have hl : raw41973step0Labels = raw41973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41973 raw41973Labels permutation346 hz
    mixedMoment B raw41973step0 raw41973step0Labels = mixedMoment B raw41973step1 raw41973step1Labels := by
      have hz : ∀ j, raw41973step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41973step1 = (fun i j => raw41973step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41973step1 raw41973step0; decide +kernel
      have hl : raw41973step1Labels = raw41973step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41973step0 raw41973step0Labels permutation56 hz
    mixedMoment B raw41973step1 raw41973step1Labels = mixedMoment B raw41973step2 raw41973step2Labels := by
      have ha : raw41973step2 = (fun i j => raw41973step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41973step2 raw41973step1; decide +kernel
      have hl : raw41973step2Labels = raw41973step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41973step1 raw41973step1Labels permutation13 permutation7
    mixedMoment B raw41973step2 raw41973step2Labels = mixedMoment B raw41973step3 raw41973step3Labels := by
      have ha : raw41973step3 = -raw41973step2 := by apply Matrix.ext; change ∀ i j, raw41973step3 i j = -(raw41973step2 i j); unfold raw41973step3 raw41973step2; decide +kernel
      have hl : raw41973step3Labels = raw41973step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41973step3 raw41973step3Labels = mixedMoment B raw41973step4 raw41973step4Labels := by
      have ha : raw41973step4 = raw41973step3 := by apply Matrix.ext; unfold raw41973step4 raw41973step3; decide +kernel
      have hl : raw41973step3Labels = labelEmbedding6 ∘ raw41973step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41973step3 raw41973step3Labels raw41973step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4161 node4161Labels := by rfl

def raw41974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41974Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41974step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41974step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0]]
def raw41974step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41974step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![3, -3, 0]]
def raw41974step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41974step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-3, 3, 0]]
def raw41974step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41974step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw41974step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41974step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw41974step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41974 raw41974Labels = mixedMoment B node3114 node3114Labels := by
  calc
    mixedMoment B raw41974 raw41974Labels = mixedMoment B raw41974step0 raw41974step0Labels := by
      have hz : ∀ j, raw41974 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41974step0 = (fun i j => raw41974 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41974step0 raw41974; decide +kernel
      have hl : raw41974step0Labels = raw41974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41974 raw41974Labels permutation520 hz
    mixedMoment B raw41974step0 raw41974step0Labels = mixedMoment B raw41974step1 raw41974step1Labels := by
      have hz : ∀ j, raw41974step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41974step1 = (fun i j => raw41974step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41974step1 raw41974step0; decide +kernel
      have hl : raw41974step1Labels = raw41974step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41974step0 raw41974step0Labels permutation104 hz
    mixedMoment B raw41974step1 raw41974step1Labels = mixedMoment B raw41974step2 raw41974step2Labels := by
      have hz : ∀ j, raw41974step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41974step2 = (fun i j => raw41974step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41974step2 raw41974step1; decide +kernel
      have hl : raw41974step2Labels = raw41974step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41974step1 raw41974step1Labels permutation20 hz
    mixedMoment B raw41974step2 raw41974step2Labels = mixedMoment B raw41974step3 raw41974step3Labels := by
      have ha : raw41974step3 = (fun i j => raw41974step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41974step3 raw41974step2; decide +kernel
      have hl : raw41974step3Labels = raw41974step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41974step2 raw41974step2Labels permutation2 permutation4
    mixedMoment B raw41974step3 raw41974step3Labels = mixedMoment B raw41974step4 raw41974step4Labels := by
      have ha : raw41974step4 = -raw41974step3 := by apply Matrix.ext; change ∀ i j, raw41974step4 i j = -(raw41974step3 i j); unfold raw41974step4 raw41974step3; decide +kernel
      have hl : raw41974step4Labels = raw41974step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41974step4 raw41974step4Labels = mixedMoment B raw41974step5 raw41974step5Labels := by
      have ha : raw41974step5 = raw41974step4 := by apply Matrix.ext; unfold raw41974step5 raw41974step4; decide +kernel
      have hl : raw41974step4Labels = labelEmbedding1 ∘ raw41974step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41974step4 raw41974step4Labels raw41974step5Labels labelEmbedding1 hl
    _ = mixedMoment B node3114 node3114Labels := by rfl

def raw41975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41975Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41975step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0]]
def raw41975step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41975step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![3, -3, 0]]
def raw41975step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41975step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw41975step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41975step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw41975step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41975 raw41975Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw41975 raw41975Labels = mixedMoment B raw41975step0 raw41975step0Labels := by
      have hz : ∀ j, raw41975 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41975step0 = (fun i j => raw41975 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41975step0 raw41975; decide +kernel
      have hl : raw41975step0Labels = raw41975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41975 raw41975Labels permutation520 hz
    mixedMoment B raw41975step0 raw41975step0Labels = mixedMoment B raw41975step1 raw41975step1Labels := by
      have hz : ∀ j, raw41975step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41975step1 = (fun i j => raw41975step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41975step1 raw41975step0; decide +kernel
      have hl : raw41975step1Labels = raw41975step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41975step0 raw41975step0Labels permutation104 hz
    mixedMoment B raw41975step1 raw41975step1Labels = mixedMoment B raw41975step2 raw41975step2Labels := by
      have hz : ∀ j, raw41975step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41975step2 = (fun i j => raw41975step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41975step2 raw41975step1; decide +kernel
      have hl : raw41975step2Labels = raw41975step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41975step1 raw41975step1Labels permutation20 hz
    mixedMoment B raw41975step2 raw41975step2Labels = mixedMoment B raw41975step3 raw41975step3Labels := by
      have ha : raw41975step3 = (fun i j => raw41975step2 (permutation7 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41975step3 raw41975step2; decide +kernel
      have hl : raw41975step3Labels = raw41975step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41975step2 raw41975step2Labels permutation7 permutation5
    mixedMoment B raw41975step3 raw41975step3Labels = mixedMoment B raw41975step4 raw41975step4Labels := by
      have ha : raw41975step4 = raw41975step3 := by apply Matrix.ext; unfold raw41975step4 raw41975step3; decide +kernel
      have hl : raw41975step3Labels = labelEmbedding9 ∘ raw41975step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41975step3 raw41975step3Labels raw41975step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw41976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41976Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41976step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw41976step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw41976step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41976step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41976step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41976step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41976 raw41976Labels = mixedMoment B node3112 node3112Labels := by
  calc
    mixedMoment B raw41976 raw41976Labels = mixedMoment B raw41976step0 raw41976step0Labels := by
      have hz : ∀ j, raw41976 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41976step0 = (fun i j => raw41976 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41976step0 raw41976; decide +kernel
      have hl : raw41976step0Labels = raw41976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41976 raw41976Labels permutation434 hz
    mixedMoment B raw41976step0 raw41976step0Labels = mixedMoment B raw41976step1 raw41976step1Labels := by
      have hz : ∀ j, raw41976step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41976step1 = (fun i j => raw41976step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41976step1 raw41976step0; decide +kernel
      have hl : raw41976step1Labels = raw41976step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41976step0 raw41976step0Labels permutation80 hz
    mixedMoment B raw41976step1 raw41976step1Labels = mixedMoment B raw41976step2 raw41976step2Labels := by
      have ha : raw41976step2 = (fun i j => raw41976step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41976step2 raw41976step1; decide +kernel
      have hl : raw41976step2Labels = raw41976step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41976step1 raw41976step1Labels permutation8 permutation4
    mixedMoment B raw41976step2 raw41976step2Labels = mixedMoment B raw41976step3 raw41976step3Labels := by
      have ha : raw41976step3 = -raw41976step2 := by apply Matrix.ext; change ∀ i j, raw41976step3 i j = -(raw41976step2 i j); unfold raw41976step3 raw41976step2; decide +kernel
      have hl : raw41976step3Labels = raw41976step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41976step3 raw41976step3Labels = mixedMoment B raw41976step4 raw41976step4Labels := by
      have ha : raw41976step4 = raw41976step3 := by apply Matrix.ext; unfold raw41976step4 raw41976step3; decide +kernel
      have hl : raw41976step3Labels = labelEmbedding1 ∘ raw41976step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41976step3 raw41976step3Labels raw41976step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3112 node3112Labels := by rfl

def raw41977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41977Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41977step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw41977step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw41977step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41977step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw41977step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41977step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw41977step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41977 raw41977Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw41977 raw41977Labels = mixedMoment B raw41977step0 raw41977step0Labels := by
      have hz : ∀ j, raw41977 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41977step0 = (fun i j => raw41977 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41977step0 raw41977; decide +kernel
      have hl : raw41977step0Labels = raw41977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41977 raw41977Labels permutation434 hz
    mixedMoment B raw41977step0 raw41977step0Labels = mixedMoment B raw41977step1 raw41977step1Labels := by
      have hz : ∀ j, raw41977step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41977step1 = (fun i j => raw41977step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41977step1 raw41977step0; decide +kernel
      have hl : raw41977step1Labels = raw41977step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41977step0 raw41977step0Labels permutation80 hz
    mixedMoment B raw41977step1 raw41977step1Labels = mixedMoment B raw41977step2 raw41977step2Labels := by
      have ha : raw41977step2 = (fun i j => raw41977step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41977step2 raw41977step1; decide +kernel
      have hl : raw41977step2Labels = raw41977step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41977step1 raw41977step1Labels permutation8 permutation5
    mixedMoment B raw41977step2 raw41977step2Labels = mixedMoment B raw41977step3 raw41977step3Labels := by
      have ha : raw41977step3 = -raw41977step2 := by apply Matrix.ext; change ∀ i j, raw41977step3 i j = -(raw41977step2 i j); unfold raw41977step3 raw41977step2; decide +kernel
      have hl : raw41977step3Labels = raw41977step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41977step3 raw41977step3Labels = mixedMoment B raw41977step4 raw41977step4Labels := by
      have ha : raw41977step4 = raw41977step3 := by apply Matrix.ext; unfold raw41977step4 raw41977step3; decide +kernel
      have hl : raw41977step3Labels = labelEmbedding9 ∘ raw41977step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41977step3 raw41977step3Labels raw41977step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw41978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41978Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41978step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41978step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1]]
def raw41978step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41978step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw41978step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41978step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41978step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41978step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41978step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41978 raw41978Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw41978 raw41978Labels = mixedMoment B raw41978step0 raw41978step0Labels := by
      have hz : ∀ j, raw41978 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41978step0 = (fun i j => raw41978 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41978step0 raw41978; decide +kernel
      have hl : raw41978step0Labels = raw41978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41978 raw41978Labels permutation434 hz
    mixedMoment B raw41978step0 raw41978step0Labels = mixedMoment B raw41978step1 raw41978step1Labels := by
      have hz : ∀ j, raw41978step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41978step1 = (fun i j => raw41978step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41978step1 raw41978step0; decide +kernel
      have hl : raw41978step1Labels = raw41978step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41978step0 raw41978step0Labels permutation80 hz
    mixedMoment B raw41978step1 raw41978step1Labels = mixedMoment B raw41978step2 raw41978step2Labels := by
      have ha : raw41978step2 = (fun i j => raw41978step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41978step2 raw41978step1; decide +kernel
      have hl : raw41978step2Labels = raw41978step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41978step1 raw41978step1Labels permutation9 permutation4
    mixedMoment B raw41978step2 raw41978step2Labels = mixedMoment B raw41978step3 raw41978step3Labels := by
      have ha : raw41978step3 = -raw41978step2 := by apply Matrix.ext; change ∀ i j, raw41978step3 i j = -(raw41978step2 i j); unfold raw41978step3 raw41978step2; decide +kernel
      have hl : raw41978step3Labels = raw41978step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41978step3 raw41978step3Labels = mixedMoment B raw41978step4 raw41978step4Labels := by
      have ha : raw41978step4 = raw41978step3 := by apply Matrix.ext; unfold raw41978step4 raw41978step3; decide +kernel
      have hl : raw41978step3Labels = labelEmbedding1 ∘ raw41978step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41978step3 raw41978step3Labels raw41978step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3110 node3110Labels := by rfl

def raw41979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41979Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41979step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1]]
def raw41979step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw41979step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41979step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41979step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41979step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41979step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41979 raw41979Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw41979 raw41979Labels = mixedMoment B raw41979step0 raw41979step0Labels := by
      have hz : ∀ j, raw41979 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41979step0 = (fun i j => raw41979 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41979step0 raw41979; decide +kernel
      have hl : raw41979step0Labels = raw41979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41979 raw41979Labels permutation434 hz
    mixedMoment B raw41979step0 raw41979step0Labels = mixedMoment B raw41979step1 raw41979step1Labels := by
      have hz : ∀ j, raw41979step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41979step1 = (fun i j => raw41979step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41979step1 raw41979step0; decide +kernel
      have hl : raw41979step1Labels = raw41979step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41979step0 raw41979step0Labels permutation80 hz
    mixedMoment B raw41979step1 raw41979step1Labels = mixedMoment B raw41979step2 raw41979step2Labels := by
      have ha : raw41979step2 = (fun i j => raw41979step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41979step2 raw41979step1; decide +kernel
      have hl : raw41979step2Labels = raw41979step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41979step1 raw41979step1Labels permutation9 permutation5
    mixedMoment B raw41979step2 raw41979step2Labels = mixedMoment B raw41979step3 raw41979step3Labels := by
      have ha : raw41979step3 = -raw41979step2 := by apply Matrix.ext; change ∀ i j, raw41979step3 i j = -(raw41979step2 i j); unfold raw41979step3 raw41979step2; decide +kernel
      have hl : raw41979step3Labels = raw41979step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41979step3 raw41979step3Labels = mixedMoment B raw41979step4 raw41979step4Labels := by
      have ha : raw41979step4 = raw41979step3 := by apply Matrix.ext; unfold raw41979step4 raw41979step3; decide +kernel
      have hl : raw41979step3Labels = labelEmbedding9 ∘ raw41979step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41979step3 raw41979step3Labels raw41979step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw41980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41980Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41980step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -3, 2], ![2, 0, -2]]
def raw41980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41980step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw41980step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41980step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw41980step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41980 raw41980Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw41980 raw41980Labels = mixedMoment B raw41980step0 raw41980step0Labels := by
      have hz : ∀ j, raw41980 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41980step0 = (fun i j => raw41980 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41980step0 raw41980; decide +kernel
      have hl : raw41980step0Labels = raw41980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41980 raw41980Labels permutation434 hz
    mixedMoment B raw41980step0 raw41980step0Labels = mixedMoment B raw41980step1 raw41980step1Labels := by
      have hz : ∀ j, raw41980step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41980step1 = (fun i j => raw41980step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41980step1 raw41980step0; decide +kernel
      have hl : raw41980step1Labels = raw41980step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41980step0 raw41980step0Labels permutation80 hz
    mixedMoment B raw41980step1 raw41980step1Labels = mixedMoment B raw41980step2 raw41980step2Labels := by
      have ha : raw41980step2 = (fun i j => raw41980step1 (permutation23 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41980step2 raw41980step1; decide +kernel
      have hl : raw41980step2Labels = raw41980step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41980step1 raw41980step1Labels permutation23 permutation4
    mixedMoment B raw41980step2 raw41980step2Labels = mixedMoment B raw41980step3 raw41980step3Labels := by
      have ha : raw41980step3 = raw41980step2 := by apply Matrix.ext; unfold raw41980step3 raw41980step2; decide +kernel
      have hl : raw41980step2Labels = labelEmbedding1 ∘ raw41980step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41980step2 raw41980step2Labels raw41980step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw41981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41981Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41981step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -3, 2], ![2, 0, -2]]
def raw41981step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw41981step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw41981step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw41981step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41981 raw41981Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw41981 raw41981Labels = mixedMoment B raw41981step0 raw41981step0Labels := by
      have hz : ∀ j, raw41981 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41981step0 = (fun i j => raw41981 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41981step0 raw41981; decide +kernel
      have hl : raw41981step0Labels = raw41981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41981 raw41981Labels permutation434 hz
    mixedMoment B raw41981step0 raw41981step0Labels = mixedMoment B raw41981step1 raw41981step1Labels := by
      have hz : ∀ j, raw41981step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41981step1 = (fun i j => raw41981step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41981step1 raw41981step0; decide +kernel
      have hl : raw41981step1Labels = raw41981step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41981step0 raw41981step0Labels permutation80 hz
    mixedMoment B raw41981step1 raw41981step1Labels = mixedMoment B raw41981step2 raw41981step2Labels := by
      have ha : raw41981step2 = (fun i j => raw41981step1 (permutation23 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41981step2 raw41981step1; decide +kernel
      have hl : raw41981step2Labels = raw41981step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41981step1 raw41981step1Labels permutation23 permutation4
    mixedMoment B raw41981step2 raw41981step2Labels = mixedMoment B raw41981step3 raw41981step3Labels := by
      have ha : raw41981step3 = raw41981step2 := by apply Matrix.ext; unfold raw41981step3 raw41981step2; decide +kernel
      have hl : raw41981step2Labels = labelEmbedding10 ∘ raw41981step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41981step2 raw41981step2Labels raw41981step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5268 node5268Labels := by rfl

def raw41982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41982Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41982step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41982step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41982step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41982step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41982 raw41982Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw41982 raw41982Labels = mixedMoment B raw41982step0 raw41982step0Labels := by
      have hz : ∀ j, raw41982 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41982step0 = (fun i j => raw41982 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41982step0 raw41982; decide +kernel
      have hl : raw41982step0Labels = raw41982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41982 raw41982Labels permutation346 hz
    mixedMoment B raw41982step0 raw41982step0Labels = mixedMoment B raw41982step1 raw41982step1Labels := by
      have ha : raw41982step1 = (fun i j => raw41982step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41982step1 raw41982step0; decide +kernel
      have hl : raw41982step1Labels = raw41982step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41982step0 raw41982step0Labels permutation44 permutation4
    mixedMoment B raw41982step1 raw41982step1Labels = mixedMoment B raw41982step2 raw41982step2Labels := by
      have ha : raw41982step2 = -raw41982step1 := by apply Matrix.ext; change ∀ i j, raw41982step2 i j = -(raw41982step1 i j); unfold raw41982step2 raw41982step1; decide +kernel
      have hl : raw41982step2Labels = raw41982step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41982step2 raw41982step2Labels = mixedMoment B raw41982step3 raw41982step3Labels := by
      have ha : raw41982step3 = raw41982step2 := by apply Matrix.ext; unfold raw41982step3 raw41982step2; decide +kernel
      have hl : raw41982step2Labels = labelEmbedding1 ∘ raw41982step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41982step2 raw41982step2Labels raw41982step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw41983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41983Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41983step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw41983step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41983step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41983step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41983step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41983 raw41983Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw41983 raw41983Labels = mixedMoment B raw41983step0 raw41983step0Labels := by
      have hz : ∀ j, raw41983 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41983step0 = (fun i j => raw41983 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41983step0 raw41983; decide +kernel
      have hl : raw41983step0Labels = raw41983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41983 raw41983Labels permutation346 hz
    mixedMoment B raw41983step0 raw41983step0Labels = mixedMoment B raw41983step1 raw41983step1Labels := by
      have ha : raw41983step1 = (fun i j => raw41983step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41983step1 raw41983step0; decide +kernel
      have hl : raw41983step1Labels = raw41983step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41983step0 raw41983step0Labels permutation34 permutation5
    mixedMoment B raw41983step1 raw41983step1Labels = mixedMoment B raw41983step2 raw41983step2Labels := by
      have ha : raw41983step2 = -raw41983step1 := by apply Matrix.ext; change ∀ i j, raw41983step2 i j = -(raw41983step1 i j); unfold raw41983step2 raw41983step1; decide +kernel
      have hl : raw41983step2Labels = raw41983step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41983step2 raw41983step2Labels = mixedMoment B raw41983step3 raw41983step3Labels := by
      have ha : raw41983step3 = raw41983step2 := by apply Matrix.ext; unfold raw41983step3 raw41983step2; decide +kernel
      have hl : raw41983step2Labels = labelEmbedding9 ∘ raw41983step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41983step2 raw41983step2Labels raw41983step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
