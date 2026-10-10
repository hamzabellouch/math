import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9856step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9856step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9856 raw9856Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw9856 raw9856Labels = mixedMoment B raw9856step0 raw9856step0Labels := by
      have hz : ∀ j, raw9856 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9856step0 = (fun i j => raw9856 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9856step0 raw9856; decide +kernel
      have hl : raw9856step0Labels = raw9856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9856 raw9856Labels permutation346 hz
    mixedMoment B raw9856step0 raw9856step0Labels = mixedMoment B raw9856step1 raw9856step1Labels := by
      have ha : raw9856step1 = (fun i j => raw9856step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9856step1 raw9856step0; decide +kernel
      have hl : raw9856step1Labels = raw9856step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9856step0 raw9856step0Labels permutation32 permutation3
    mixedMoment B raw9856step1 raw9856step1Labels = mixedMoment B raw9856step2 raw9856step2Labels := by
      have ha : raw9856step2 = raw9856step1 := by apply Matrix.ext; unfold raw9856step2 raw9856step1; decide +kernel
      have hl : raw9856step1Labels = labelEmbedding6 ∘ raw9856step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9856step1 raw9856step1Labels raw9856step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw9857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9857step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9857step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9857 raw9857Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw9857 raw9857Labels = mixedMoment B raw9857step0 raw9857step0Labels := by
      have hz : ∀ j, raw9857 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9857step0 = (fun i j => raw9857 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9857step0 raw9857; decide +kernel
      have hl : raw9857step0Labels = raw9857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9857 raw9857Labels permutation346 hz
    mixedMoment B raw9857step0 raw9857step0Labels = mixedMoment B raw9857step1 raw9857step1Labels := by
      have ha : raw9857step1 = (fun i j => raw9857step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9857step1 raw9857step0; decide +kernel
      have hl : raw9857step1Labels = raw9857step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9857step0 raw9857step0Labels permutation32 permutation3
    mixedMoment B raw9857step1 raw9857step1Labels = mixedMoment B raw9857step2 raw9857step2Labels := by
      have ha : raw9857step2 = raw9857step1 := by apply Matrix.ext; unfold raw9857step2 raw9857step1; decide +kernel
      have hl : raw9857step1Labels = labelEmbedding6 ∘ raw9857step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9857step1 raw9857step1Labels raw9857step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw9858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9858step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9858 raw9858Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw9858 raw9858Labels = mixedMoment B raw9858step0 raw9858step0Labels := by
      have ha : raw9858step0 = (fun i j => raw9858 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9858step0 raw9858; decide +kernel
      have hl : raw9858step0Labels = raw9858Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9858 raw9858Labels permutation176 permutation3
    mixedMoment B raw9858step0 raw9858step0Labels = mixedMoment B raw9858step1 raw9858step1Labels := by
      have ha : raw9858step1 = raw9858step0 := by apply Matrix.ext; unfold raw9858step1 raw9858step0; decide +kernel
      have hl : raw9858step0Labels = labelEmbedding6 ∘ raw9858step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9858step0 raw9858step0Labels raw9858step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw9859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw9859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9859step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9859step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9859step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9859step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9859step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9859 raw9859Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw9859 raw9859Labels = mixedMoment B raw9859step0 raw9859step0Labels := by
      have hz : ∀ j, raw9859 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9859step0 = (fun i j => raw9859 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9859step0 raw9859; decide +kernel
      have hl : raw9859step0Labels = raw9859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9859 raw9859Labels permutation520 hz
    mixedMoment B raw9859step0 raw9859step0Labels = mixedMoment B raw9859step1 raw9859step1Labels := by
      have hz : ∀ j, raw9859step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9859step1 = (fun i j => raw9859step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9859step1 raw9859step0; decide +kernel
      have hl : raw9859step1Labels = raw9859step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9859step0 raw9859step0Labels permutation80 hz
    mixedMoment B raw9859step1 raw9859step1Labels = mixedMoment B raw9859step2 raw9859step2Labels := by
      have ha : raw9859step2 = (fun i j => raw9859step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9859step2 raw9859step1; decide +kernel
      have hl : raw9859step2Labels = raw9859step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9859step1 raw9859step1Labels permutation8 permutation3
    mixedMoment B raw9859step2 raw9859step2Labels = mixedMoment B raw9859step3 raw9859step3Labels := by
      have ha : raw9859step3 = raw9859step2 := by apply Matrix.ext; unfold raw9859step3 raw9859step2; decide +kernel
      have hl : raw9859step2Labels = labelEmbedding6 ∘ raw9859step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9859step2 raw9859step2Labels raw9859step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw9860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9860step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9860step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9860 raw9860Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw9860 raw9860Labels = mixedMoment B raw9860step0 raw9860step0Labels := by
      have hz : ∀ j, raw9860 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9860step0 = (fun i j => raw9860 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9860step0 raw9860; decide +kernel
      have hl : raw9860step0Labels = raw9860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9860 raw9860Labels permutation346 hz
    mixedMoment B raw9860step0 raw9860step0Labels = mixedMoment B raw9860step1 raw9860step1Labels := by
      have ha : raw9860step1 = (fun i j => raw9860step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9860step1 raw9860step0; decide +kernel
      have hl : raw9860step1Labels = raw9860step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9860step0 raw9860step0Labels permutation39 permutation3
    mixedMoment B raw9860step1 raw9860step1Labels = mixedMoment B raw9860step2 raw9860step2Labels := by
      have ha : raw9860step2 = raw9860step1 := by apply Matrix.ext; unfold raw9860step2 raw9860step1; decide +kernel
      have hl : raw9860step1Labels = labelEmbedding6 ∘ raw9860step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9860step1 raw9860step1Labels raw9860step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

def raw9861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9861step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9861step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9861 raw9861Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw9861 raw9861Labels = mixedMoment B raw9861step0 raw9861step0Labels := by
      have hz : ∀ j, raw9861 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9861step0 = (fun i j => raw9861 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9861step0 raw9861; decide +kernel
      have hl : raw9861step0Labels = raw9861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9861 raw9861Labels permutation346 hz
    mixedMoment B raw9861step0 raw9861step0Labels = mixedMoment B raw9861step1 raw9861step1Labels := by
      have ha : raw9861step1 = (fun i j => raw9861step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9861step1 raw9861step0; decide +kernel
      have hl : raw9861step1Labels = raw9861step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9861step0 raw9861step0Labels permutation33 permutation3
    mixedMoment B raw9861step1 raw9861step1Labels = mixedMoment B raw9861step2 raw9861step2Labels := by
      have ha : raw9861step2 = raw9861step1 := by apply Matrix.ext; unfold raw9861step2 raw9861step1; decide +kernel
      have hl : raw9861step1Labels = labelEmbedding6 ∘ raw9861step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9861step1 raw9861step1Labels raw9861step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw9862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9862step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9862step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9862 raw9862Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw9862 raw9862Labels = mixedMoment B raw9862step0 raw9862step0Labels := by
      have ha : raw9862step0 = (fun i j => raw9862 (permutation183 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9862step0 raw9862; decide +kernel
      have hl : raw9862step0Labels = raw9862Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9862 raw9862Labels permutation183 permutation3
    mixedMoment B raw9862step0 raw9862step0Labels = mixedMoment B raw9862step1 raw9862step1Labels := by
      have ha : raw9862step1 = raw9862step0 := by apply Matrix.ext; unfold raw9862step1 raw9862step0; decide +kernel
      have hl : raw9862step0Labels = labelEmbedding6 ∘ raw9862step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9862step0 raw9862step0Labels raw9862step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5050 node5050Labels := by rfl

def raw9863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9863step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9863step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9863 raw9863Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw9863 raw9863Labels = mixedMoment B raw9863step0 raw9863step0Labels := by
      have hz : ∀ j, raw9863 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9863step0 = (fun i j => raw9863 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9863step0 raw9863; decide +kernel
      have hl : raw9863step0Labels = raw9863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9863 raw9863Labels permutation346 hz
    mixedMoment B raw9863step0 raw9863step0Labels = mixedMoment B raw9863step1 raw9863step1Labels := by
      have ha : raw9863step1 = (fun i j => raw9863step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9863step1 raw9863step0; decide +kernel
      have hl : raw9863step1Labels = raw9863step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9863step0 raw9863step0Labels permutation39 permutation3
    mixedMoment B raw9863step1 raw9863step1Labels = mixedMoment B raw9863step2 raw9863step2Labels := by
      have ha : raw9863step2 = raw9863step1 := by apply Matrix.ext; unfold raw9863step2 raw9863step1; decide +kernel
      have hl : raw9863step1Labels = labelEmbedding6 ∘ raw9863step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9863step1 raw9863step1Labels raw9863step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

def raw9864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9864step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9864step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9864 raw9864Labels = mixedMoment B node4401 node4401Labels := by
  calc
    mixedMoment B raw9864 raw9864Labels = mixedMoment B raw9864step0 raw9864step0Labels := by
      have hz : ∀ j, raw9864 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9864step0 = (fun i j => raw9864 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9864step0 raw9864; decide +kernel
      have hl : raw9864step0Labels = raw9864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9864 raw9864Labels permutation346 hz
    mixedMoment B raw9864step0 raw9864step0Labels = mixedMoment B raw9864step1 raw9864step1Labels := by
      have ha : raw9864step1 = (fun i j => raw9864step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9864step1 raw9864step0; decide +kernel
      have hl : raw9864step1Labels = raw9864step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9864step0 raw9864step0Labels permutation38 permutation3
    mixedMoment B raw9864step1 raw9864step1Labels = mixedMoment B raw9864step2 raw9864step2Labels := by
      have ha : raw9864step2 = raw9864step1 := by apply Matrix.ext; unfold raw9864step2 raw9864step1; decide +kernel
      have hl : raw9864step1Labels = labelEmbedding6 ∘ raw9864step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9864step1 raw9864step1Labels raw9864step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4401 node4401Labels := by rfl

def raw9865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw9865step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9865step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9865step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9865step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9865 raw9865Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw9865 raw9865Labels = mixedMoment B raw9865step0 raw9865step0Labels := by
      have hz : ∀ j, raw9865 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9865step0 = (fun i j => raw9865 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9865step0 raw9865; decide +kernel
      have hl : raw9865step0Labels = raw9865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9865 raw9865Labels permutation346 hz
    mixedMoment B raw9865step0 raw9865step0Labels = mixedMoment B raw9865step1 raw9865step1Labels := by
      have ha : raw9865step1 = (fun i j => raw9865step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9865step1 raw9865step0; decide +kernel
      have hl : raw9865step1Labels = raw9865step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9865step0 raw9865step0Labels permutation151 permutation3
    mixedMoment B raw9865step1 raw9865step1Labels = mixedMoment B raw9865step2 raw9865step2Labels := by
      have ha : raw9865step2 = -raw9865step1 := by apply Matrix.ext; change ∀ i j, raw9865step2 i j = -(raw9865step1 i j); unfold raw9865step2 raw9865step1; decide +kernel
      have hl : raw9865step2Labels = raw9865step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9865step2 raw9865step2Labels = mixedMoment B raw9865step3 raw9865step3Labels := by
      have ha : raw9865step3 = raw9865step2 := by apply Matrix.ext; unfold raw9865step3 raw9865step2; decide +kernel
      have hl : raw9865step2Labels = labelEmbedding6 ∘ raw9865step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9865step2 raw9865step2Labels raw9865step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw9866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9866step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9866 raw9866Labels = mixedMoment B node5047 node5047Labels := by
  calc
    mixedMoment B raw9866 raw9866Labels = mixedMoment B raw9866step0 raw9866step0Labels := by
      have ha : raw9866step0 = (fun i j => raw9866 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9866step0 raw9866; decide +kernel
      have hl : raw9866step0Labels = raw9866Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9866 raw9866Labels permutation182 permutation3
    mixedMoment B raw9866step0 raw9866step0Labels = mixedMoment B raw9866step1 raw9866step1Labels := by
      have ha : raw9866step1 = raw9866step0 := by apply Matrix.ext; unfold raw9866step1 raw9866step0; decide +kernel
      have hl : raw9866step0Labels = labelEmbedding6 ∘ raw9866step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9866step0 raw9866step0Labels raw9866step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5047 node5047Labels := by rfl

def raw9867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9867step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9867step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9867 raw9867Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw9867 raw9867Labels = mixedMoment B raw9867step0 raw9867step0Labels := by
      have hz : ∀ j, raw9867 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9867step0 = (fun i j => raw9867 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9867step0 raw9867; decide +kernel
      have hl : raw9867step0Labels = raw9867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9867 raw9867Labels permutation346 hz
    mixedMoment B raw9867step0 raw9867step0Labels = mixedMoment B raw9867step1 raw9867step1Labels := by
      have ha : raw9867step1 = (fun i j => raw9867step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9867step1 raw9867step0; decide +kernel
      have hl : raw9867step1Labels = raw9867step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9867step0 raw9867step0Labels permutation38 permutation3
    mixedMoment B raw9867step1 raw9867step1Labels = mixedMoment B raw9867step2 raw9867step2Labels := by
      have ha : raw9867step2 = raw9867step1 := by apply Matrix.ext; unfold raw9867step2 raw9867step1; decide +kernel
      have hl : raw9867step1Labels = labelEmbedding6 ∘ raw9867step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9867step1 raw9867step1Labels raw9867step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

def raw9868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw9868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw9868step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9868step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9868step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9868step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9868step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9868 raw9868Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw9868 raw9868Labels = mixedMoment B raw9868step0 raw9868step0Labels := by
      have hz : ∀ j, raw9868 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9868step0 = (fun i j => raw9868 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9868step0 raw9868; decide +kernel
      have hl : raw9868step0Labels = raw9868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9868 raw9868Labels permutation520 hz
    mixedMoment B raw9868step0 raw9868step0Labels = mixedMoment B raw9868step1 raw9868step1Labels := by
      have hz : ∀ j, raw9868step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9868step1 = (fun i j => raw9868step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9868step1 raw9868step0; decide +kernel
      have hl : raw9868step1Labels = raw9868step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9868step0 raw9868step0Labels permutation80 hz
    mixedMoment B raw9868step1 raw9868step1Labels = mixedMoment B raw9868step2 raw9868step2Labels := by
      have ha : raw9868step2 = (fun i j => raw9868step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9868step2 raw9868step1; decide +kernel
      have hl : raw9868step2Labels = raw9868step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9868step1 raw9868step1Labels permutation10 permutation3
    mixedMoment B raw9868step2 raw9868step2Labels = mixedMoment B raw9868step3 raw9868step3Labels := by
      have ha : raw9868step3 = raw9868step2 := by apply Matrix.ext; unfold raw9868step3 raw9868step2; decide +kernel
      have hl : raw9868step2Labels = labelEmbedding6 ∘ raw9868step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9868step2 raw9868step2Labels raw9868step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw9869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw9869Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw9869step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw9869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9869 raw9869Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw9869 raw9869Labels = mixedMoment B raw9869step0 raw9869step0Labels := by
      have hz : ∀ j, raw9869 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9869step0 = (fun i j => raw9869 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9869step0 raw9869; decide +kernel
      have hl : raw9869step0Labels = raw9869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9869 raw9869Labels permutation346 hz
    mixedMoment B raw9869step0 raw9869step0Labels = mixedMoment B raw9869step1 raw9869step1Labels := by
      have ha : raw9869step1 = (fun i j => raw9869step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9869step1 raw9869step0; decide +kernel
      have hl : raw9869step1Labels = raw9869step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9869step0 raw9869step0Labels permutation39 permutation3
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw9870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9870Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9870step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9870 raw9870Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw9870 raw9870Labels = mixedMoment B raw9870step0 raw9870step0Labels := by
      have hz : ∀ j, raw9870 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9870step0 = (fun i j => raw9870 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9870step0 raw9870; decide +kernel
      have hl : raw9870step0Labels = raw9870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9870 raw9870Labels permutation346 hz
    mixedMoment B raw9870step0 raw9870step0Labels = mixedMoment B raw9870step1 raw9870step1Labels := by
      have ha : raw9870step1 = (fun i j => raw9870step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9870step1 raw9870step0; decide +kernel
      have hl : raw9870step1Labels = raw9870step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9870step0 raw9870step0Labels permutation40 permutation3
    _ = mixedMoment B node1005 node1005Labels := by rfl

def raw9871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9871Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9871 raw9871Labels = mixedMoment B node2462 node2462Labels := by
  calc
    mixedMoment B raw9871 raw9871Labels = mixedMoment B raw9871step0 raw9871step0Labels := by
      have ha : raw9871step0 = (fun i j => raw9871 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9871step0 raw9871; decide +kernel
      have hl : raw9871step0Labels = raw9871Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9871 raw9871Labels permutation184 permutation3
    _ = mixedMoment B node2462 node2462Labels := by rfl

def raw9872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9872Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9872step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9872 raw9872Labels = mixedMoment B node2404 node2404Labels := by
  calc
    mixedMoment B raw9872 raw9872Labels = mixedMoment B raw9872step0 raw9872step0Labels := by
      have hz : ∀ j, raw9872 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9872step0 = (fun i j => raw9872 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9872step0 raw9872; decide +kernel
      have hl : raw9872step0Labels = raw9872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9872 raw9872Labels permutation346 hz
    mixedMoment B raw9872step0 raw9872step0Labels = mixedMoment B raw9872step1 raw9872step1Labels := by
      have ha : raw9872step1 = (fun i j => raw9872step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9872step1 raw9872step0; decide +kernel
      have hl : raw9872step1Labels = raw9872step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9872step0 raw9872step0Labels permutation40 permutation3
    _ = mixedMoment B node2404 node2404Labels := by rfl

def raw9873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw9873Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw9873step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9873step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw9873step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9873step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9873step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9873 raw9873Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw9873 raw9873Labels = mixedMoment B raw9873step0 raw9873step0Labels := by
      have hz : ∀ j, raw9873 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9873step0 = (fun i j => raw9873 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9873step0 raw9873; decide +kernel
      have hl : raw9873step0Labels = raw9873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9873 raw9873Labels permutation520 hz
    mixedMoment B raw9873step0 raw9873step0Labels = mixedMoment B raw9873step1 raw9873step1Labels := by
      have hz : ∀ j, raw9873step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9873step1 = (fun i j => raw9873step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9873step1 raw9873step0; decide +kernel
      have hl : raw9873step1Labels = raw9873step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9873step0 raw9873step0Labels permutation80 hz
    mixedMoment B raw9873step1 raw9873step1Labels = mixedMoment B raw9873step2 raw9873step2Labels := by
      have ha : raw9873step2 = (fun i j => raw9873step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9873step2 raw9873step1; decide +kernel
      have hl : raw9873step2Labels = raw9873step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9873step1 raw9873step1Labels permutation10 permutation3
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw9874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9874Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9874 raw9874Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw9874 raw9874Labels = mixedMoment B raw9874step0 raw9874step0Labels := by
      have ha : raw9874step0 = (fun i j => raw9874 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9874step0 raw9874; decide +kernel
      have hl : raw9874step0Labels = raw9874Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9874 raw9874Labels permutation200 permutation3
    _ = mixedMoment B node980 node980Labels := by rfl

def raw9875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9875Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9875 raw9875Labels = mixedMoment B node2556 node2556Labels := by
  calc
    mixedMoment B raw9875 raw9875Labels = mixedMoment B raw9875step0 raw9875step0Labels := by
      have ha : raw9875step0 = (fun i j => raw9875 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9875step0 raw9875; decide +kernel
      have hl : raw9875step0Labels = raw9875Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9875 raw9875Labels permutation158 permutation3
    _ = mixedMoment B node2556 node2556Labels := by rfl

def raw9876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9876Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9876 raw9876Labels = mixedMoment B node2383 node2383Labels := by
  calc
    mixedMoment B raw9876 raw9876Labels = mixedMoment B raw9876step0 raw9876step0Labels := by
      have ha : raw9876step0 = (fun i j => raw9876 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9876step0 raw9876; decide +kernel
      have hl : raw9876step0Labels = raw9876Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9876 raw9876Labels permutation200 permutation3
    _ = mixedMoment B node2383 node2383Labels := by rfl

def raw9877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw9877Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw9877step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9877 raw9877Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw9877 raw9877Labels = mixedMoment B raw9877step0 raw9877step0Labels := by
      have hz : ∀ j, raw9877 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9877step0 = (fun i j => raw9877 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9877step0 raw9877; decide +kernel
      have hl : raw9877step0Labels = raw9877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9877 raw9877Labels permutation520 hz
    mixedMoment B raw9877step0 raw9877step0Labels = mixedMoment B raw9877step1 raw9877step1Labels := by
      have ha : raw9877step1 = (fun i j => raw9877step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9877step1 raw9877step0; decide +kernel
      have hl : raw9877step1Labels = raw9877step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9877step0 raw9877step0Labels permutation44 permutation3
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw9878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9878step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9878step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9878 raw9878Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw9878 raw9878Labels = mixedMoment B raw9878step0 raw9878step0Labels := by
      have hz : ∀ j, raw9878 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9878step0 = (fun i j => raw9878 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9878step0 raw9878; decide +kernel
      have hl : raw9878step0Labels = raw9878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9878 raw9878Labels permutation346 hz
    mixedMoment B raw9878step0 raw9878step0Labels = mixedMoment B raw9878step1 raw9878step1Labels := by
      have ha : raw9878step1 = (fun i j => raw9878step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9878step1 raw9878step0; decide +kernel
      have hl : raw9878step1Labels = raw9878step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9878step0 raw9878step0Labels permutation32 permutation3
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw9879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9879Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9879step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9879 raw9879Labels = mixedMoment B node2595 node2595Labels := by
  calc
    mixedMoment B raw9879 raw9879Labels = mixedMoment B raw9879step0 raw9879step0Labels := by
      have hz : ∀ j, raw9879 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9879step0 = (fun i j => raw9879 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9879step0 raw9879; decide +kernel
      have hl : raw9879step0Labels = raw9879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9879 raw9879Labels permutation346 hz
    mixedMoment B raw9879step0 raw9879step0Labels = mixedMoment B raw9879step1 raw9879step1Labels := by
      have ha : raw9879step1 = (fun i j => raw9879step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9879step1 raw9879step0; decide +kernel
      have hl : raw9879step1Labels = raw9879step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9879step0 raw9879step0Labels permutation32 permutation3
    _ = mixedMoment B node2595 node2595Labels := by rfl

def raw9880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9880Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9880 raw9880Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw9880 raw9880Labels = mixedMoment B raw9880step0 raw9880step0Labels := by
      have ha : raw9880step0 = (fun i j => raw9880 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9880step0 raw9880; decide +kernel
      have hl : raw9880step0Labels = raw9880Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9880 raw9880Labels permutation176 permutation3
    _ = mixedMoment B node2480 node2480Labels := by rfl

def raw9881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw9881Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw9881step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9881step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9881step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9881step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9881step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9881 raw9881Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw9881 raw9881Labels = mixedMoment B raw9881step0 raw9881step0Labels := by
      have hz : ∀ j, raw9881 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9881step0 = (fun i j => raw9881 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9881step0 raw9881; decide +kernel
      have hl : raw9881step0Labels = raw9881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9881 raw9881Labels permutation520 hz
    mixedMoment B raw9881step0 raw9881step0Labels = mixedMoment B raw9881step1 raw9881step1Labels := by
      have hz : ∀ j, raw9881step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9881step1 = (fun i j => raw9881step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9881step1 raw9881step0; decide +kernel
      have hl : raw9881step1Labels = raw9881step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9881step0 raw9881step0Labels permutation80 hz
    mixedMoment B raw9881step1 raw9881step1Labels = mixedMoment B raw9881step2 raw9881step2Labels := by
      have ha : raw9881step2 = (fun i j => raw9881step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9881step2 raw9881step1; decide +kernel
      have hl : raw9881step2Labels = raw9881step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9881step1 raw9881step1Labels permutation8 permutation3
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw9882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9882Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9882step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9882step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9882 raw9882Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw9882 raw9882Labels = mixedMoment B raw9882step0 raw9882step0Labels := by
      have hz : ∀ j, raw9882 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9882step0 = (fun i j => raw9882 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9882step0 raw9882; decide +kernel
      have hl : raw9882step0Labels = raw9882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9882 raw9882Labels permutation346 hz
    mixedMoment B raw9882step0 raw9882step0Labels = mixedMoment B raw9882step1 raw9882step1Labels := by
      have ha : raw9882step1 = (fun i j => raw9882step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9882step1 raw9882step0; decide +kernel
      have hl : raw9882step1Labels = raw9882step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9882step0 raw9882step0Labels permutation39 permutation3
    _ = mixedMoment B node985 node985Labels := by rfl

def raw9883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9883Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9883step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9883 raw9883Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw9883 raw9883Labels = mixedMoment B raw9883step0 raw9883step0Labels := by
      have hz : ∀ j, raw9883 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9883step0 = (fun i j => raw9883 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9883step0 raw9883; decide +kernel
      have hl : raw9883step0Labels = raw9883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9883 raw9883Labels permutation346 hz
    mixedMoment B raw9883step0 raw9883step0Labels = mixedMoment B raw9883step1 raw9883step1Labels := by
      have ha : raw9883step1 = (fun i j => raw9883step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9883step1 raw9883step0; decide +kernel
      have hl : raw9883step1Labels = raw9883step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9883step0 raw9883step0Labels permutation33 permutation3
    _ = mixedMoment B node2561 node2561Labels := by rfl

def raw9884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9884 raw9884Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw9884 raw9884Labels = mixedMoment B raw9884step0 raw9884step0Labels := by
      have ha : raw9884step0 = (fun i j => raw9884 (permutation183 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9884step0 raw9884; decide +kernel
      have hl : raw9884step0Labels = raw9884Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9884 raw9884Labels permutation183 permutation3
    _ = mixedMoment B node2452 node2452Labels := by rfl

def raw9885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9885Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9885step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw9885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9885 raw9885Labels = mixedMoment B node2388 node2388Labels := by
  calc
    mixedMoment B raw9885 raw9885Labels = mixedMoment B raw9885step0 raw9885step0Labels := by
      have hz : ∀ j, raw9885 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9885step0 = (fun i j => raw9885 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9885step0 raw9885; decide +kernel
      have hl : raw9885step0Labels = raw9885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9885 raw9885Labels permutation346 hz
    mixedMoment B raw9885step0 raw9885step0Labels = mixedMoment B raw9885step1 raw9885step1Labels := by
      have ha : raw9885step1 = (fun i j => raw9885step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9885step1 raw9885step0; decide +kernel
      have hl : raw9885step1Labels = raw9885step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9885step0 raw9885step0Labels permutation39 permutation3
    _ = mixedMoment B node2388 node2388Labels := by rfl

def raw9886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9886Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9886step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9886 raw9886Labels = mixedMoment B node982 node982Labels := by
  calc
    mixedMoment B raw9886 raw9886Labels = mixedMoment B raw9886step0 raw9886step0Labels := by
      have hz : ∀ j, raw9886 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9886step0 = (fun i j => raw9886 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9886step0 raw9886; decide +kernel
      have hl : raw9886step0Labels = raw9886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9886 raw9886Labels permutation346 hz
    mixedMoment B raw9886step0 raw9886step0Labels = mixedMoment B raw9886step1 raw9886step1Labels := by
      have ha : raw9886step1 = (fun i j => raw9886step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9886step1 raw9886step0; decide +kernel
      have hl : raw9886step1Labels = raw9886step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9886step0 raw9886step0Labels permutation38 permutation3
    _ = mixedMoment B node982 node982Labels := by rfl

def raw9887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9887Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9887step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw9887step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9887step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9887 raw9887Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw9887 raw9887Labels = mixedMoment B raw9887step0 raw9887step0Labels := by
      have hz : ∀ j, raw9887 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9887step0 = (fun i j => raw9887 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9887step0 raw9887; decide +kernel
      have hl : raw9887step0Labels = raw9887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9887 raw9887Labels permutation346 hz
    mixedMoment B raw9887step0 raw9887step0Labels = mixedMoment B raw9887step1 raw9887step1Labels := by
      have ha : raw9887step1 = (fun i j => raw9887step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9887step1 raw9887step0; decide +kernel
      have hl : raw9887step1Labels = raw9887step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9887step0 raw9887step0Labels permutation151 permutation3
    mixedMoment B raw9887step1 raw9887step1Labels = mixedMoment B raw9887step2 raw9887step2Labels := by
      have ha : raw9887step2 = -raw9887step1 := by apply Matrix.ext; change ∀ i j, raw9887step2 i j = -(raw9887step1 i j); unfold raw9887step2 raw9887step1; decide +kernel
      have hl : raw9887step2Labels = raw9887step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw9888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9888Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9888 raw9888Labels = mixedMoment B node2449 node2449Labels := by
  calc
    mixedMoment B raw9888 raw9888Labels = mixedMoment B raw9888step0 raw9888step0Labels := by
      have ha : raw9888step0 = (fun i j => raw9888 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9888step0 raw9888; decide +kernel
      have hl : raw9888step0Labels = raw9888Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9888 raw9888Labels permutation182 permutation3
    _ = mixedMoment B node2449 node2449Labels := by rfl

def raw9889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9889Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9889step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw9889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9889 raw9889Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw9889 raw9889Labels = mixedMoment B raw9889step0 raw9889step0Labels := by
      have hz : ∀ j, raw9889 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9889step0 = (fun i j => raw9889 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9889step0 raw9889; decide +kernel
      have hl : raw9889step0Labels = raw9889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9889 raw9889Labels permutation346 hz
    mixedMoment B raw9889step0 raw9889step0Labels = mixedMoment B raw9889step1 raw9889step1Labels := by
      have ha : raw9889step1 = (fun i j => raw9889step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9889step1 raw9889step0; decide +kernel
      have hl : raw9889step1Labels = raw9889step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9889step0 raw9889step0Labels permutation38 permutation3
    _ = mixedMoment B node2385 node2385Labels := by rfl

def raw9890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw9890Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw9890step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw9890step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9890step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9890 raw9890Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw9890 raw9890Labels = mixedMoment B raw9890step0 raw9890step0Labels := by
      have hz : ∀ j, raw9890 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9890step0 = (fun i j => raw9890 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9890step0 raw9890; decide +kernel
      have hl : raw9890step0Labels = raw9890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9890 raw9890Labels permutation520 hz
    mixedMoment B raw9890step0 raw9890step0Labels = mixedMoment B raw9890step1 raw9890step1Labels := by
      have hz : ∀ j, raw9890step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9890step1 = (fun i j => raw9890step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9890step1 raw9890step0; decide +kernel
      have hl : raw9890step1Labels = raw9890step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9890step0 raw9890step0Labels permutation80 hz
    mixedMoment B raw9890step1 raw9890step1Labels = mixedMoment B raw9890step2 raw9890step2Labels := by
      have ha : raw9890step2 = (fun i j => raw9890step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9890step2 raw9890step1; decide +kernel
      have hl : raw9890step2Labels = raw9890step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9890step1 raw9890step1Labels permutation10 permutation3
    _ = mixedMoment B node2726 node2726Labels := by rfl

def raw9891 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9891step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9891step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9891step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9891step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9891step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9891 raw9891Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw9891 raw9891Labels = mixedMoment B raw9891step0 raw9891step0Labels := by
      have hz : ∀ j, raw9891 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9891step0 = (fun i j => raw9891 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9891step0 raw9891; decide +kernel
      have hl : raw9891step0Labels = raw9891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9891 raw9891Labels permutation346 hz
    mixedMoment B raw9891step0 raw9891step0Labels = mixedMoment B raw9891step1 raw9891step1Labels := by
      have hz : ∀ j, raw9891step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9891step1 = (fun i j => raw9891step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9891step1 raw9891step0; decide +kernel
      have hl : raw9891step1Labels = raw9891step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9891step0 raw9891step0Labels permutation56 hz
    mixedMoment B raw9891step1 raw9891step1Labels = mixedMoment B raw9891step2 raw9891step2Labels := by
      have ha : raw9891step2 = (fun i j => raw9891step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9891step2 raw9891step1; decide +kernel
      have hl : raw9891step2Labels = raw9891step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9891step1 raw9891step1Labels permutation8 permutation7
    mixedMoment B raw9891step2 raw9891step2Labels = mixedMoment B raw9891step3 raw9891step3Labels := by
      have ha : raw9891step3 = raw9891step2 := by apply Matrix.ext; unfold raw9891step3 raw9891step2; decide +kernel
      have hl : raw9891step2Labels = labelEmbedding10 ∘ raw9891step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9891step2 raw9891step2Labels raw9891step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw9892 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9892step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9892step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9892step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9892 raw9892Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw9892 raw9892Labels = mixedMoment B raw9892step0 raw9892step0Labels := by
      have ha : raw9892step0 = (fun i j => raw9892 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9892step0 raw9892; decide +kernel
      have hl : raw9892step0Labels = raw9892Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9892 raw9892Labels permutation152 permutation7
    mixedMoment B raw9892step0 raw9892step0Labels = mixedMoment B raw9892step1 raw9892step1Labels := by
      have ha : raw9892step1 = raw9892step0 := by apply Matrix.ext; unfold raw9892step1 raw9892step0; decide +kernel
      have hl : raw9892step0Labels = labelEmbedding10 ∘ raw9892step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9892step0 raw9892step0Labels raw9892step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5250 node5250Labels := by rfl

def raw9893 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9893step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9893step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9893 raw9893Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw9893 raw9893Labels = mixedMoment B raw9893step0 raw9893step0Labels := by
      have hz : ∀ j, raw9893 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9893step0 = (fun i j => raw9893 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9893step0 raw9893; decide +kernel
      have hl : raw9893step0Labels = raw9893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9893 raw9893Labels permutation346 hz
    mixedMoment B raw9893step0 raw9893step0Labels = mixedMoment B raw9893step1 raw9893step1Labels := by
      have ha : raw9893step1 = (fun i j => raw9893step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9893step1 raw9893step0; decide +kernel
      have hl : raw9893step1Labels = raw9893step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9893step0 raw9893step0Labels permutation32 permutation7
    mixedMoment B raw9893step1 raw9893step1Labels = mixedMoment B raw9893step2 raw9893step2Labels := by
      have ha : raw9893step2 = raw9893step1 := by apply Matrix.ext; unfold raw9893step2 raw9893step1; decide +kernel
      have hl : raw9893step1Labels = labelEmbedding10 ∘ raw9893step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9893step1 raw9893step1Labels raw9893step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw9894 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9894step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9894step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9894 raw9894Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw9894 raw9894Labels = mixedMoment B raw9894step0 raw9894step0Labels := by
      have hz : ∀ j, raw9894 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9894step0 = (fun i j => raw9894 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9894step0 raw9894; decide +kernel
      have hl : raw9894step0Labels = raw9894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9894 raw9894Labels permutation346 hz
    mixedMoment B raw9894step0 raw9894step0Labels = mixedMoment B raw9894step1 raw9894step1Labels := by
      have ha : raw9894step1 = (fun i j => raw9894step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9894step1 raw9894step0; decide +kernel
      have hl : raw9894step1Labels = raw9894step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9894step0 raw9894step0Labels permutation32 permutation7
    mixedMoment B raw9894step1 raw9894step1Labels = mixedMoment B raw9894step2 raw9894step2Labels := by
      have ha : raw9894step2 = raw9894step1 := by apply Matrix.ext; unfold raw9894step2 raw9894step1; decide +kernel
      have hl : raw9894step1Labels = labelEmbedding10 ∘ raw9894step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9894step1 raw9894step1Labels raw9894step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw9895 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9895step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9895step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9895step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9895 raw9895Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw9895 raw9895Labels = mixedMoment B raw9895step0 raw9895step0Labels := by
      have hz : ∀ j, raw9895 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9895step0 = (fun i j => raw9895 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9895step0 raw9895; decide +kernel
      have hl : raw9895step0Labels = raw9895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9895 raw9895Labels permutation346 hz
    mixedMoment B raw9895step0 raw9895step0Labels = mixedMoment B raw9895step1 raw9895step1Labels := by
      have ha : raw9895step1 = (fun i j => raw9895step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9895step1 raw9895step0; decide +kernel
      have hl : raw9895step1Labels = raw9895step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9895step0 raw9895step0Labels permutation32 permutation7
    mixedMoment B raw9895step1 raw9895step1Labels = mixedMoment B raw9895step2 raw9895step2Labels := by
      have ha : raw9895step2 = raw9895step1 := by apply Matrix.ext; unfold raw9895step2 raw9895step1; decide +kernel
      have hl : raw9895step1Labels = labelEmbedding10 ∘ raw9895step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9895step1 raw9895step1Labels raw9895step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw9896 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw9896step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9896step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9896step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9896step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9896 raw9896Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw9896 raw9896Labels = mixedMoment B raw9896step0 raw9896step0Labels := by
      have hz : ∀ j, raw9896 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9896step0 = (fun i j => raw9896 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9896step0 raw9896; decide +kernel
      have hl : raw9896step0Labels = raw9896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9896 raw9896Labels permutation346 hz
    mixedMoment B raw9896step0 raw9896step0Labels = mixedMoment B raw9896step1 raw9896step1Labels := by
      have ha : raw9896step1 = (fun i j => raw9896step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9896step1 raw9896step0; decide +kernel
      have hl : raw9896step1Labels = raw9896step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9896step0 raw9896step0Labels permutation41 permutation4
    mixedMoment B raw9896step1 raw9896step1Labels = mixedMoment B raw9896step2 raw9896step2Labels := by
      have ha : raw9896step2 = -raw9896step1 := by apply Matrix.ext; change ∀ i j, raw9896step2 i j = -(raw9896step1 i j); unfold raw9896step2 raw9896step1; decide +kernel
      have hl : raw9896step2Labels = raw9896step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9896step2 raw9896step2Labels = mixedMoment B raw9896step3 raw9896step3Labels := by
      have ha : raw9896step3 = raw9896step2 := by apply Matrix.ext; unfold raw9896step3 raw9896step2; decide +kernel
      have hl : raw9896step2Labels = labelEmbedding7 ∘ raw9896step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9896step2 raw9896step2Labels raw9896step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw9897 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9897step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9897step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9897step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9897 raw9897Labels = mixedMoment B node5244 node5244Labels := by
  calc
    mixedMoment B raw9897 raw9897Labels = mixedMoment B raw9897step0 raw9897step0Labels := by
      have ha : raw9897step0 = (fun i j => raw9897 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9897step0 raw9897; decide +kernel
      have hl : raw9897step0Labels = raw9897Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9897 raw9897Labels permutation182 permutation6
    mixedMoment B raw9897step0 raw9897step0Labels = mixedMoment B raw9897step1 raw9897step1Labels := by
      have ha : raw9897step1 = raw9897step0 := by apply Matrix.ext; unfold raw9897step1 raw9897step0; decide +kernel
      have hl : raw9897step0Labels = labelEmbedding9 ∘ raw9897step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9897step0 raw9897step0Labels raw9897step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5244 node5244Labels := by rfl

def raw9898 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9898step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9898step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9898 raw9898Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw9898 raw9898Labels = mixedMoment B raw9898step0 raw9898step0Labels := by
      have hz : ∀ j, raw9898 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9898step0 = (fun i j => raw9898 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9898step0 raw9898; decide +kernel
      have hl : raw9898step0Labels = raw9898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9898 raw9898Labels permutation346 hz
    mixedMoment B raw9898step0 raw9898step0Labels = mixedMoment B raw9898step1 raw9898step1Labels := by
      have ha : raw9898step1 = (fun i j => raw9898step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9898step1 raw9898step0; decide +kernel
      have hl : raw9898step1Labels = raw9898step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9898step0 raw9898step0Labels permutation38 permutation6
    mixedMoment B raw9898step1 raw9898step1Labels = mixedMoment B raw9898step2 raw9898step2Labels := by
      have ha : raw9898step2 = raw9898step1 := by apply Matrix.ext; unfold raw9898step2 raw9898step1; decide +kernel
      have hl : raw9898step1Labels = labelEmbedding9 ∘ raw9898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9898step1 raw9898step1Labels raw9898step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5233 node5233Labels := by rfl

def raw9899 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9899step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9899step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9899 raw9899Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw9899 raw9899Labels = mixedMoment B raw9899step0 raw9899step0Labels := by
      have hz : ∀ j, raw9899 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9899step0 = (fun i j => raw9899 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9899step0 raw9899; decide +kernel
      have hl : raw9899step0Labels = raw9899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9899 raw9899Labels permutation346 hz
    mixedMoment B raw9899step0 raw9899step0Labels = mixedMoment B raw9899step1 raw9899step1Labels := by
      have ha : raw9899step1 = (fun i j => raw9899step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9899step1 raw9899step0; decide +kernel
      have hl : raw9899step1Labels = raw9899step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9899step0 raw9899step0Labels permutation38 permutation6
    mixedMoment B raw9899step1 raw9899step1Labels = mixedMoment B raw9899step2 raw9899step2Labels := by
      have ha : raw9899step2 = raw9899step1 := by apply Matrix.ext; unfold raw9899step2 raw9899step1; decide +kernel
      have hl : raw9899step1Labels = labelEmbedding9 ∘ raw9899step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9899step1 raw9899step1Labels raw9899step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw9900 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw9900step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9900step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw9900step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9900 raw9900Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw9900 raw9900Labels = mixedMoment B raw9900step0 raw9900step0Labels := by
      have hz : ∀ j, raw9900 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9900step0 = (fun i j => raw9900 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9900step0 raw9900; decide +kernel
      have hl : raw9900step0Labels = raw9900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9900 raw9900Labels permutation346 hz
    mixedMoment B raw9900step0 raw9900step0Labels = mixedMoment B raw9900step1 raw9900step1Labels := by
      have ha : raw9900step1 = (fun i j => raw9900step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9900step1 raw9900step0; decide +kernel
      have hl : raw9900step1Labels = raw9900step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9900step0 raw9900step0Labels permutation38 permutation6
    mixedMoment B raw9900step1 raw9900step1Labels = mixedMoment B raw9900step2 raw9900step2Labels := by
      have ha : raw9900step2 = raw9900step1 := by apply Matrix.ext; unfold raw9900step2 raw9900step1; decide +kernel
      have hl : raw9900step1Labels = labelEmbedding9 ∘ raw9900step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9900step1 raw9900step1Labels raw9900step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw9901 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9901step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9901step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9901step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9901step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9901step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9901 raw9901Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw9901 raw9901Labels = mixedMoment B raw9901step0 raw9901step0Labels := by
      have ha : raw9901step0 = (fun i j => raw9901 (permutation200 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9901step0 raw9901; decide +kernel
      have hl : raw9901step0Labels = raw9901Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9901 raw9901Labels permutation200 permutation4
    mixedMoment B raw9901step0 raw9901step0Labels = mixedMoment B raw9901step1 raw9901step1Labels := by
      have ha : raw9901step1 = -raw9901step0 := by apply Matrix.ext; change ∀ i j, raw9901step1 i j = -(raw9901step0 i j); unfold raw9901step1 raw9901step0; decide +kernel
      have hl : raw9901step1Labels = raw9901step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9901step1 raw9901step1Labels = mixedMoment B raw9901step2 raw9901step2Labels := by
      have ha : raw9901step2 = raw9901step1 := by apply Matrix.ext; unfold raw9901step2 raw9901step1; decide +kernel
      have hl : raw9901step1Labels = labelEmbedding7 ∘ raw9901step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9901step1 raw9901step1Labels raw9901step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

def raw9902 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9902step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9902step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9902 raw9902Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw9902 raw9902Labels = mixedMoment B raw9902step0 raw9902step0Labels := by
      have hz : ∀ j, raw9902 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9902step0 = (fun i j => raw9902 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9902step0 raw9902; decide +kernel
      have hl : raw9902step0Labels = raw9902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9902 raw9902Labels permutation265 hz
    mixedMoment B raw9902step0 raw9902step0Labels = mixedMoment B raw9902step1 raw9902step1Labels := by
      have ha : raw9902step1 = (fun i j => raw9902step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9902step1 raw9902step0; decide +kernel
      have hl : raw9902step1Labels = raw9902step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9902step0 raw9902step0Labels permutation38 permutation6
    mixedMoment B raw9902step1 raw9902step1Labels = mixedMoment B raw9902step2 raw9902step2Labels := by
      have ha : raw9902step2 = raw9902step1 := by apply Matrix.ext; unfold raw9902step2 raw9902step1; decide +kernel
      have hl : raw9902step1Labels = labelEmbedding9 ∘ raw9902step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9902step1 raw9902step1Labels raw9902step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw9903 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9903step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9903 raw9903Labels = mixedMoment B node5220 node5220Labels := by
  calc
    mixedMoment B raw9903 raw9903Labels = mixedMoment B raw9903step0 raw9903step0Labels := by
      have ha : raw9903step0 = (fun i j => raw9903 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9903step0 raw9903; decide +kernel
      have hl : raw9903step0Labels = raw9903Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9903 raw9903Labels permutation200 permutation6
    mixedMoment B raw9903step0 raw9903step0Labels = mixedMoment B raw9903step1 raw9903step1Labels := by
      have ha : raw9903step1 = raw9903step0 := by apply Matrix.ext; unfold raw9903step1 raw9903step0; decide +kernel
      have hl : raw9903step0Labels = labelEmbedding9 ∘ raw9903step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9903step0 raw9903step0Labels raw9903step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5220 node5220Labels := by rfl

def raw9904 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9904step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9904 raw9904Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw9904 raw9904Labels = mixedMoment B raw9904step0 raw9904step0Labels := by
      have ha : raw9904step0 = (fun i j => raw9904 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9904step0 raw9904; decide +kernel
      have hl : raw9904step0Labels = raw9904Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9904 raw9904Labels permutation200 permutation6
    mixedMoment B raw9904step0 raw9904step0Labels = mixedMoment B raw9904step1 raw9904step1Labels := by
      have ha : raw9904step1 = raw9904step0 := by apply Matrix.ext; unfold raw9904step1 raw9904step0; decide +kernel
      have hl : raw9904step0Labels = labelEmbedding9 ∘ raw9904step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9904step0 raw9904step0Labels raw9904step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5250 node5250Labels := by rfl

def raw9905 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9905step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9905 raw9905Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw9905 raw9905Labels = mixedMoment B raw9905step0 raw9905step0Labels := by
      have ha : raw9905step0 = (fun i j => raw9905 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9905step0 raw9905; decide +kernel
      have hl : raw9905step0Labels = raw9905Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9905 raw9905Labels permutation200 permutation6
    mixedMoment B raw9905step0 raw9905step0Labels = mixedMoment B raw9905step1 raw9905step1Labels := by
      have ha : raw9905step1 = raw9905step0 := by apply Matrix.ext; unfold raw9905step1 raw9905step0; decide +kernel
      have hl : raw9905step0Labels = labelEmbedding9 ∘ raw9905step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9905step0 raw9905step0Labels raw9905step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw9906 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9906step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9906step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9906step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9906step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9906 raw9906Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw9906 raw9906Labels = mixedMoment B raw9906step0 raw9906step0Labels := by
      have hz : ∀ j, raw9906 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9906step0 = (fun i j => raw9906 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9906step0 raw9906; decide +kernel
      have hl : raw9906step0Labels = raw9906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9906 raw9906Labels permutation434 hz
    mixedMoment B raw9906step0 raw9906step0Labels = mixedMoment B raw9906step1 raw9906step1Labels := by
      have hz : ∀ j, raw9906step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9906step1 = (fun i j => raw9906step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9906step1 raw9906step0; decide +kernel
      have hl : raw9906step1Labels = raw9906step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9906step0 raw9906step0Labels permutation80 hz
    mixedMoment B raw9906step1 raw9906step1Labels = mixedMoment B raw9906step2 raw9906step2Labels := by
      have ha : raw9906step2 = (fun i j => raw9906step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9906step2 raw9906step1; decide +kernel
      have hl : raw9906step2Labels = raw9906step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9906step1 raw9906step1Labels permutation8 permutation6
    mixedMoment B raw9906step2 raw9906step2Labels = mixedMoment B raw9906step3 raw9906step3Labels := by
      have ha : raw9906step3 = raw9906step2 := by apply Matrix.ext; unfold raw9906step3 raw9906step2; decide +kernel
      have hl : raw9906step2Labels = labelEmbedding9 ∘ raw9906step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9906step2 raw9906step2Labels raw9906step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw9907 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9907step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9907step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9907step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9907 raw9907Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw9907 raw9907Labels = mixedMoment B raw9907step0 raw9907step0Labels := by
      have hz : ∀ j, raw9907 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9907step0 = (fun i j => raw9907 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9907step0 raw9907; decide +kernel
      have hl : raw9907step0Labels = raw9907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9907 raw9907Labels permutation434 hz
    mixedMoment B raw9907step0 raw9907step0Labels = mixedMoment B raw9907step1 raw9907step1Labels := by
      have ha : raw9907step1 = (fun i j => raw9907step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9907step1 raw9907step0; decide +kernel
      have hl : raw9907step1Labels = raw9907step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9907step0 raw9907step0Labels permutation38 permutation6
    mixedMoment B raw9907step1 raw9907step1Labels = mixedMoment B raw9907step2 raw9907step2Labels := by
      have ha : raw9907step2 = raw9907step1 := by apply Matrix.ext; unfold raw9907step2 raw9907step1; decide +kernel
      have hl : raw9907step1Labels = labelEmbedding9 ∘ raw9907step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9907step1 raw9907step1Labels raw9907step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw9908 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw9908step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9908step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9908step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9908step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9908step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9908 raw9908Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw9908 raw9908Labels = mixedMoment B raw9908step0 raw9908step0Labels := by
      have hz : ∀ j, raw9908 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9908step0 = (fun i j => raw9908 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9908step0 raw9908; decide +kernel
      have hl : raw9908step0Labels = raw9908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9908 raw9908Labels permutation346 hz
    mixedMoment B raw9908step0 raw9908step0Labels = mixedMoment B raw9908step1 raw9908step1Labels := by
      have ha : raw9908step1 = (fun i j => raw9908step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9908step1 raw9908step0; decide +kernel
      have hl : raw9908step1Labels = raw9908step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9908step0 raw9908step0Labels permutation39 permutation4
    mixedMoment B raw9908step1 raw9908step1Labels = mixedMoment B raw9908step2 raw9908step2Labels := by
      have ha : raw9908step2 = -raw9908step1 := by apply Matrix.ext; change ∀ i j, raw9908step2 i j = -(raw9908step1 i j); unfold raw9908step2 raw9908step1; decide +kernel
      have hl : raw9908step2Labels = raw9908step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9908step2 raw9908step2Labels = mixedMoment B raw9908step3 raw9908step3Labels := by
      have ha : raw9908step3 = raw9908step2 := by apply Matrix.ext; unfold raw9908step3 raw9908step2; decide +kernel
      have hl : raw9908step2Labels = labelEmbedding7 ∘ raw9908step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9908step2 raw9908step2Labels raw9908step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw9909 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9909step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9909step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9909 raw9909Labels = mixedMoment B node5242 node5242Labels := by
  calc
    mixedMoment B raw9909 raw9909Labels = mixedMoment B raw9909step0 raw9909step0Labels := by
      have ha : raw9909step0 = (fun i j => raw9909 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9909step0 raw9909; decide +kernel
      have hl : raw9909step0Labels = raw9909Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9909 raw9909Labels permutation182 permutation6
    mixedMoment B raw9909step0 raw9909step0Labels = mixedMoment B raw9909step1 raw9909step1Labels := by
      have ha : raw9909step1 = raw9909step0 := by apply Matrix.ext; unfold raw9909step1 raw9909step0; decide +kernel
      have hl : raw9909step0Labels = labelEmbedding9 ∘ raw9909step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9909step0 raw9909step0Labels raw9909step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5242 node5242Labels := by rfl

def raw9910 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9910step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9910step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9910step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9910 raw9910Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw9910 raw9910Labels = mixedMoment B raw9910step0 raw9910step0Labels := by
      have hz : ∀ j, raw9910 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9910step0 = (fun i j => raw9910 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9910step0 raw9910; decide +kernel
      have hl : raw9910step0Labels = raw9910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9910 raw9910Labels permutation346 hz
    mixedMoment B raw9910step0 raw9910step0Labels = mixedMoment B raw9910step1 raw9910step1Labels := by
      have ha : raw9910step1 = (fun i j => raw9910step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9910step1 raw9910step0; decide +kernel
      have hl : raw9910step1Labels = raw9910step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9910step0 raw9910step0Labels permutation38 permutation6
    mixedMoment B raw9910step1 raw9910step1Labels = mixedMoment B raw9910step2 raw9910step2Labels := by
      have ha : raw9910step2 = raw9910step1 := by apply Matrix.ext; unfold raw9910step2 raw9910step1; decide +kernel
      have hl : raw9910step1Labels = labelEmbedding9 ∘ raw9910step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9910step1 raw9910step1Labels raw9910step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

def raw9911 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9911step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9911step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9911step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9911step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw9911step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9911step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9911 raw9911Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw9911 raw9911Labels = mixedMoment B raw9911step0 raw9911step0Labels := by
      have hz : ∀ j, raw9911 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9911step0 = (fun i j => raw9911 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9911step0 raw9911; decide +kernel
      have hl : raw9911step0Labels = raw9911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9911 raw9911Labels permutation346 hz
    mixedMoment B raw9911step0 raw9911step0Labels = mixedMoment B raw9911step1 raw9911step1Labels := by
      have ha : raw9911step1 = (fun i j => raw9911step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9911step1 raw9911step0; decide +kernel
      have hl : raw9911step1Labels = raw9911step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9911step0 raw9911step0Labels permutation38 permutation4
    mixedMoment B raw9911step1 raw9911step1Labels = mixedMoment B raw9911step2 raw9911step2Labels := by
      have ha : raw9911step2 = -raw9911step1 := by apply Matrix.ext; change ∀ i j, raw9911step2 i j = -(raw9911step1 i j); unfold raw9911step2 raw9911step1; decide +kernel
      have hl : raw9911step2Labels = raw9911step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9911step2 raw9911step2Labels = mixedMoment B raw9911step3 raw9911step3Labels := by
      have ha : raw9911step3 = raw9911step2 := by apply Matrix.ext; unfold raw9911step3 raw9911step2; decide +kernel
      have hl : raw9911step2Labels = labelEmbedding7 ∘ raw9911step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9911step2 raw9911step2Labels raw9911step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw9912 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9912step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9912step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9912step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9912step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9912step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9912step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9912 raw9912Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw9912 raw9912Labels = mixedMoment B raw9912step0 raw9912step0Labels := by
      have hz : ∀ j, raw9912 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9912step0 = (fun i j => raw9912 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9912step0 raw9912; decide +kernel
      have hl : raw9912step0Labels = raw9912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9912 raw9912Labels permutation346 hz
    mixedMoment B raw9912step0 raw9912step0Labels = mixedMoment B raw9912step1 raw9912step1Labels := by
      have hz : ∀ j, raw9912step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9912step1 = (fun i j => raw9912step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9912step1 raw9912step0; decide +kernel
      have hl : raw9912step1Labels = raw9912step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9912step0 raw9912step0Labels permutation56 hz
    mixedMoment B raw9912step1 raw9912step1Labels = mixedMoment B raw9912step2 raw9912step2Labels := by
      have ha : raw9912step2 = (fun i j => raw9912step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9912step2 raw9912step1; decide +kernel
      have hl : raw9912step2Labels = raw9912step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9912step1 raw9912step1Labels permutation8 permutation6
    mixedMoment B raw9912step2 raw9912step2Labels = mixedMoment B raw9912step3 raw9912step3Labels := by
      have ha : raw9912step3 = raw9912step2 := by apply Matrix.ext; unfold raw9912step3 raw9912step2; decide +kernel
      have hl : raw9912step2Labels = labelEmbedding9 ∘ raw9912step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9912step2 raw9912step2Labels raw9912step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw9913 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9913step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9913step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9913 raw9913Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw9913 raw9913Labels = mixedMoment B raw9913step0 raw9913step0Labels := by
      have ha : raw9913step0 = (fun i j => raw9913 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9913step0 raw9913; decide +kernel
      have hl : raw9913step0Labels = raw9913Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9913 raw9913Labels permutation182 permutation6
    mixedMoment B raw9913step0 raw9913step0Labels = mixedMoment B raw9913step1 raw9913step1Labels := by
      have ha : raw9913step1 = raw9913step0 := by apply Matrix.ext; unfold raw9913step1 raw9913step0; decide +kernel
      have hl : raw9913step0Labels = labelEmbedding9 ∘ raw9913step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9913step0 raw9913step0Labels raw9913step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

def raw9914 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9914step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9914step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9914step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9914step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9914 raw9914Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw9914 raw9914Labels = mixedMoment B raw9914step0 raw9914step0Labels := by
      have hz : ∀ j, raw9914 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9914step0 = (fun i j => raw9914 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9914step0 raw9914; decide +kernel
      have hl : raw9914step0Labels = raw9914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9914 raw9914Labels permutation346 hz
    mixedMoment B raw9914step0 raw9914step0Labels = mixedMoment B raw9914step1 raw9914step1Labels := by
      have ha : raw9914step1 = (fun i j => raw9914step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9914step1 raw9914step0; decide +kernel
      have hl : raw9914step1Labels = raw9914step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9914step0 raw9914step0Labels permutation38 permutation6
    mixedMoment B raw9914step1 raw9914step1Labels = mixedMoment B raw9914step2 raw9914step2Labels := by
      have ha : raw9914step2 = raw9914step1 := by apply Matrix.ext; unfold raw9914step2 raw9914step1; decide +kernel
      have hl : raw9914step1Labels = labelEmbedding9 ∘ raw9914step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9914step1 raw9914step1Labels raw9914step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw9915 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9915step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9915step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9915step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9915step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9915 raw9915Labels = mixedMoment B node3102 node3102Labels := by
  calc
    mixedMoment B raw9915 raw9915Labels = mixedMoment B raw9915step0 raw9915step0Labels := by
      have hz : ∀ j, raw9915 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9915step0 = (fun i j => raw9915 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9915step0 raw9915; decide +kernel
      have hl : raw9915step0Labels = raw9915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9915 raw9915Labels permutation346 hz
    mixedMoment B raw9915step0 raw9915step0Labels = mixedMoment B raw9915step1 raw9915step1Labels := by
      have hz : ∀ j, raw9915step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9915step1 = (fun i j => raw9915step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9915step1 raw9915step0; decide +kernel
      have hl : raw9915step1Labels = raw9915step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9915step0 raw9915step0Labels permutation56 hz
    mixedMoment B raw9915step1 raw9915step1Labels = mixedMoment B raw9915step2 raw9915step2Labels := by
      have ha : raw9915step2 = (fun i j => raw9915step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9915step2 raw9915step1; decide +kernel
      have hl : raw9915step2Labels = raw9915step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9915step1 raw9915step1Labels permutation8 permutation6
    _ = mixedMoment B node3102 node3102Labels := by rfl

def raw9916 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9916Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9916 raw9916Labels = mixedMoment B node3065 node3065Labels := by
  calc
    mixedMoment B raw9916 raw9916Labels = mixedMoment B raw9916step0 raw9916step0Labels := by
      have ha : raw9916step0 = (fun i j => raw9916 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9916step0 raw9916; decide +kernel
      have hl : raw9916step0Labels = raw9916Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9916 raw9916Labels permutation182 permutation6
    _ = mixedMoment B node3065 node3065Labels := by rfl

def raw9917 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9917Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9917step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9917 raw9917Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw9917 raw9917Labels = mixedMoment B raw9917step0 raw9917step0Labels := by
      have hz : ∀ j, raw9917 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9917step0 = (fun i j => raw9917 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9917step0 raw9917; decide +kernel
      have hl : raw9917step0Labels = raw9917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9917 raw9917Labels permutation346 hz
    mixedMoment B raw9917step0 raw9917step0Labels = mixedMoment B raw9917step1 raw9917step1Labels := by
      have ha : raw9917step1 = (fun i j => raw9917step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9917step1 raw9917step0; decide +kernel
      have hl : raw9917step1Labels = raw9917step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9917step0 raw9917step0Labels permutation38 permutation6
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw9918 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9918Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9918step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9918 raw9918Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw9918 raw9918Labels = mixedMoment B raw9918step0 raw9918step0Labels := by
      have hz : ∀ j, raw9918 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9918step0 = (fun i j => raw9918 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9918step0 raw9918; decide +kernel
      have hl : raw9918step0Labels = raw9918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9918 raw9918Labels permutation346 hz
    mixedMoment B raw9918step0 raw9918step0Labels = mixedMoment B raw9918step1 raw9918step1Labels := by
      have ha : raw9918step1 = (fun i j => raw9918step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9918step1 raw9918step0; decide +kernel
      have hl : raw9918step1Labels = raw9918step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9918step0 raw9918step0Labels permutation38 permutation6
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw9919 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9919Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9919step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9919 raw9919Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw9919 raw9919Labels = mixedMoment B raw9919step0 raw9919step0Labels := by
      have hz : ∀ j, raw9919 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9919step0 = (fun i j => raw9919 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9919step0 raw9919; decide +kernel
      have hl : raw9919step0Labels = raw9919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9919 raw9919Labels permutation346 hz
    mixedMoment B raw9919step0 raw9919step0Labels = mixedMoment B raw9919step1 raw9919step1Labels := by
      have ha : raw9919step1 = (fun i j => raw9919step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9919step1 raw9919step0; decide +kernel
      have hl : raw9919step1Labels = raw9919step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9919step0 raw9919step0Labels permutation38 permutation6
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw9920 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9920Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9920step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9920 raw9920Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw9920 raw9920Labels = mixedMoment B raw9920step0 raw9920step0Labels := by
      have hz : ∀ j, raw9920 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9920step0 = (fun i j => raw9920 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9920step0 raw9920; decide +kernel
      have hl : raw9920step0Labels = raw9920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9920 raw9920Labels permutation346 hz
    mixedMoment B raw9920step0 raw9920step0Labels = mixedMoment B raw9920step1 raw9920step1Labels := by
      have ha : raw9920step1 = (fun i j => raw9920step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9920step1 raw9920step0; decide +kernel
      have hl : raw9920step1Labels = raw9920step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9920step0 raw9920step0Labels permutation38 permutation6
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw9921 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9921Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9921 raw9921Labels = mixedMoment B node2698 node2698Labels := by
  calc
    mixedMoment B raw9921 raw9921Labels = mixedMoment B raw9921step0 raw9921step0Labels := by
      have ha : raw9921step0 = (fun i j => raw9921 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9921step0 raw9921; decide +kernel
      have hl : raw9921step0Labels = raw9921Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9921 raw9921Labels permutation182 permutation6
    _ = mixedMoment B node2698 node2698Labels := by rfl

def raw9922 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9922Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9922step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9922step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw9922step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9922 raw9922Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw9922 raw9922Labels = mixedMoment B raw9922step0 raw9922step0Labels := by
      have hz : ∀ j, raw9922 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9922step0 = (fun i j => raw9922 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9922step0 raw9922; decide +kernel
      have hl : raw9922step0Labels = raw9922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9922 raw9922Labels permutation346 hz
    mixedMoment B raw9922step0 raw9922step0Labels = mixedMoment B raw9922step1 raw9922step1Labels := by
      have ha : raw9922step1 = (fun i j => raw9922step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9922step1 raw9922step0; decide +kernel
      have hl : raw9922step1Labels = raw9922step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9922step0 raw9922step0Labels permutation38 permutation6
    _ = mixedMoment B node2678 node2678Labels := by rfl

def raw9923 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9923Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9923step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9923 raw9923Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw9923 raw9923Labels = mixedMoment B raw9923step0 raw9923step0Labels := by
      have hz : ∀ j, raw9923 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9923step0 = (fun i j => raw9923 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9923step0 raw9923; decide +kernel
      have hl : raw9923step0Labels = raw9923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9923 raw9923Labels permutation346 hz
    mixedMoment B raw9923step0 raw9923step0Labels = mixedMoment B raw9923step1 raw9923step1Labels := by
      have ha : raw9923step1 = (fun i j => raw9923step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9923step1 raw9923step0; decide +kernel
      have hl : raw9923step1Labels = raw9923step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9923step0 raw9923step0Labels permutation38 permutation6
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw9924 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9924Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9924step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw9924step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9924 raw9924Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw9924 raw9924Labels = mixedMoment B raw9924step0 raw9924step0Labels := by
      have hz : ∀ j, raw9924 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9924step0 = (fun i j => raw9924 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9924step0 raw9924; decide +kernel
      have hl : raw9924step0Labels = raw9924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9924 raw9924Labels permutation346 hz
    mixedMoment B raw9924step0 raw9924step0Labels = mixedMoment B raw9924step1 raw9924step1Labels := by
      have ha : raw9924step1 = (fun i j => raw9924step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9924step1 raw9924step0; decide +kernel
      have hl : raw9924step1Labels = raw9924step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9924step0 raw9924step0Labels permutation38 permutation6
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw9925 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9925Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9925 raw9925Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw9925 raw9925Labels = mixedMoment B raw9925step0 raw9925step0Labels := by
      have ha : raw9925step0 = (fun i j => raw9925 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9925step0 raw9925; decide +kernel
      have hl : raw9925step0Labels = raw9925Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9925 raw9925Labels permutation200 permutation6
    _ = mixedMoment B node2191 node2191Labels := by rfl

def raw9926 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9926Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9926step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9926 raw9926Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw9926 raw9926Labels = mixedMoment B raw9926step0 raw9926step0Labels := by
      have hz : ∀ j, raw9926 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9926step0 = (fun i j => raw9926 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9926step0 raw9926; decide +kernel
      have hl : raw9926step0Labels = raw9926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9926 raw9926Labels permutation265 hz
    mixedMoment B raw9926step0 raw9926step0Labels = mixedMoment B raw9926step1 raw9926step1Labels := by
      have ha : raw9926step1 = (fun i j => raw9926step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9926step1 raw9926step0; decide +kernel
      have hl : raw9926step1Labels = raw9926step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9926step0 raw9926step0Labels permutation38 permutation6
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw9927 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9927Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9927 raw9927Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw9927 raw9927Labels = mixedMoment B raw9927step0 raw9927step0Labels := by
      have ha : raw9927step0 = (fun i j => raw9927 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9927step0 raw9927; decide +kernel
      have hl : raw9927step0Labels = raw9927Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9927 raw9927Labels permutation200 permutation6
    _ = mixedMoment B node2662 node2662Labels := by rfl

def raw9928 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9928Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9928 raw9928Labels = mixedMoment B node2709 node2709Labels := by
  calc
    mixedMoment B raw9928 raw9928Labels = mixedMoment B raw9928step0 raw9928step0Labels := by
      have ha : raw9928step0 = (fun i j => raw9928 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9928step0 raw9928; decide +kernel
      have hl : raw9928step0Labels = raw9928Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9928 raw9928Labels permutation200 permutation6
    _ = mixedMoment B node2709 node2709Labels := by rfl

def raw9929 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9929Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9929 raw9929Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw9929 raw9929Labels = mixedMoment B raw9929step0 raw9929step0Labels := by
      have ha : raw9929step0 = (fun i j => raw9929 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9929step0 raw9929; decide +kernel
      have hl : raw9929step0Labels = raw9929Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9929 raw9929Labels permutation200 permutation6
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw9930 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9930Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9930step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9930step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9930step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9930step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9930 raw9930Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw9930 raw9930Labels = mixedMoment B raw9930step0 raw9930step0Labels := by
      have hz : ∀ j, raw9930 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9930step0 = (fun i j => raw9930 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9930step0 raw9930; decide +kernel
      have hl : raw9930step0Labels = raw9930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9930 raw9930Labels permutation434 hz
    mixedMoment B raw9930step0 raw9930step0Labels = mixedMoment B raw9930step1 raw9930step1Labels := by
      have hz : ∀ j, raw9930step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9930step1 = (fun i j => raw9930step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9930step1 raw9930step0; decide +kernel
      have hl : raw9930step1Labels = raw9930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9930step0 raw9930step0Labels permutation80 hz
    mixedMoment B raw9930step1 raw9930step1Labels = mixedMoment B raw9930step2 raw9930step2Labels := by
      have ha : raw9930step2 = (fun i j => raw9930step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9930step2 raw9930step1; decide +kernel
      have hl : raw9930step2Labels = raw9930step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9930step1 raw9930step1Labels permutation8 permutation6
    _ = mixedMoment B node2265 node2265Labels := by rfl

def raw9931 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9931step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9931 raw9931Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw9931 raw9931Labels = mixedMoment B raw9931step0 raw9931step0Labels := by
      have hz : ∀ j, raw9931 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9931step0 = (fun i j => raw9931 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9931step0 raw9931; decide +kernel
      have hl : raw9931step0Labels = raw9931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9931 raw9931Labels permutation434 hz
    mixedMoment B raw9931step0 raw9931step0Labels = mixedMoment B raw9931step1 raw9931step1Labels := by
      have ha : raw9931step1 = (fun i j => raw9931step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9931step1 raw9931step0; decide +kernel
      have hl : raw9931step1Labels = raw9931step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9931step0 raw9931step0Labels permutation38 permutation6
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw9932 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9932step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9932step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9932 raw9932Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw9932 raw9932Labels = mixedMoment B raw9932step0 raw9932step0Labels := by
      have hz : ∀ j, raw9932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9932step0 = (fun i j => raw9932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9932step0 raw9932; decide +kernel
      have hl : raw9932step0Labels = raw9932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9932 raw9932Labels permutation346 hz
    mixedMoment B raw9932step0 raw9932step0Labels = mixedMoment B raw9932step1 raw9932step1Labels := by
      have ha : raw9932step1 = (fun i j => raw9932step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9932step1 raw9932step0; decide +kernel
      have hl : raw9932step1Labels = raw9932step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9932step0 raw9932step0Labels permutation38 permutation6
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw9933 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9933step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9933 raw9933Labels = mixedMoment B node2695 node2695Labels := by
  calc
    mixedMoment B raw9933 raw9933Labels = mixedMoment B raw9933step0 raw9933step0Labels := by
      have ha : raw9933step0 = (fun i j => raw9933 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9933step0 raw9933; decide +kernel
      have hl : raw9933step0Labels = raw9933Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9933 raw9933Labels permutation182 permutation6
    _ = mixedMoment B node2695 node2695Labels := by rfl

def raw9934 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9934Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9934step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw9934step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9934 raw9934Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw9934 raw9934Labels = mixedMoment B raw9934step0 raw9934step0Labels := by
      have hz : ∀ j, raw9934 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9934step0 = (fun i j => raw9934 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9934step0 raw9934; decide +kernel
      have hl : raw9934step0Labels = raw9934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9934 raw9934Labels permutation346 hz
    mixedMoment B raw9934step0 raw9934step0Labels = mixedMoment B raw9934step1 raw9934step1Labels := by
      have ha : raw9934step1 = (fun i j => raw9934step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9934step1 raw9934step0; decide +kernel
      have hl : raw9934step1Labels = raw9934step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9934step0 raw9934step0Labels permutation38 permutation6
    _ = mixedMoment B node2673 node2673Labels := by rfl

def raw9935 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9935Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9935step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9935step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9935 raw9935Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw9935 raw9935Labels = mixedMoment B raw9935step0 raw9935step0Labels := by
      have hz : ∀ j, raw9935 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9935step0 = (fun i j => raw9935 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9935step0 raw9935; decide +kernel
      have hl : raw9935step0Labels = raw9935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9935 raw9935Labels permutation346 hz
    mixedMoment B raw9935step0 raw9935step0Labels = mixedMoment B raw9935step1 raw9935step1Labels := by
      have ha : raw9935step1 = (fun i j => raw9935step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9935step1 raw9935step0; decide +kernel
      have hl : raw9935step1Labels = raw9935step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9935step0 raw9935step0Labels permutation38 permutation6
    _ = mixedMoment B node2205 node2205Labels := by rfl

def raw9936 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9936Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9936step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9936step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9936step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9936 raw9936Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw9936 raw9936Labels = mixedMoment B raw9936step0 raw9936step0Labels := by
      have hz : ∀ j, raw9936 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9936step0 = (fun i j => raw9936 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9936step0 raw9936; decide +kernel
      have hl : raw9936step0Labels = raw9936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9936 raw9936Labels permutation346 hz
    mixedMoment B raw9936step0 raw9936step0Labels = mixedMoment B raw9936step1 raw9936step1Labels := by
      have hz : ∀ j, raw9936step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9936step1 = (fun i j => raw9936step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9936step1 raw9936step0; decide +kernel
      have hl : raw9936step1Labels = raw9936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9936step0 raw9936step0Labels permutation56 hz
    mixedMoment B raw9936step1 raw9936step1Labels = mixedMoment B raw9936step2 raw9936step2Labels := by
      have ha : raw9936step2 = (fun i j => raw9936step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9936step2 raw9936step1; decide +kernel
      have hl : raw9936step2Labels = raw9936step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9936step1 raw9936step1Labels permutation8 permutation6
    _ = mixedMoment B node2742 node2742Labels := by rfl

def raw9937 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9937Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9937 raw9937Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw9937 raw9937Labels = mixedMoment B raw9937step0 raw9937step0Labels := by
      have ha : raw9937step0 = (fun i j => raw9937 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9937step0 raw9937; decide +kernel
      have hl : raw9937step0Labels = raw9937Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9937 raw9937Labels permutation182 permutation6
    _ = mixedMoment B node2694 node2694Labels := by rfl

def raw9938 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9938Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9938step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9938step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9938 raw9938Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw9938 raw9938Labels = mixedMoment B raw9938step0 raw9938step0Labels := by
      have hz : ∀ j, raw9938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9938step0 = (fun i j => raw9938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9938step0 raw9938; decide +kernel
      have hl : raw9938step0Labels = raw9938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9938 raw9938Labels permutation346 hz
    mixedMoment B raw9938step0 raw9938step0Labels = mixedMoment B raw9938step1 raw9938step1Labels := by
      have ha : raw9938step1 = (fun i j => raw9938step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9938step1 raw9938step0; decide +kernel
      have hl : raw9938step1Labels = raw9938step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9938step0 raw9938step0Labels permutation38 permutation6
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw9939 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9939Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9939step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9939step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9939step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9939step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9939step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9939 raw9939Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw9939 raw9939Labels = mixedMoment B raw9939step0 raw9939step0Labels := by
      have hz : ∀ j, raw9939 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9939step0 = (fun i j => raw9939 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9939step0 raw9939; decide +kernel
      have hl : raw9939step0Labels = raw9939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9939 raw9939Labels permutation346 hz
    mixedMoment B raw9939step0 raw9939step0Labels = mixedMoment B raw9939step1 raw9939step1Labels := by
      have hz : ∀ j, raw9939step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9939step1 = (fun i j => raw9939step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9939step1 raw9939step0; decide +kernel
      have hl : raw9939step1Labels = raw9939step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9939step0 raw9939step0Labels permutation56 hz
    mixedMoment B raw9939step1 raw9939step1Labels = mixedMoment B raw9939step2 raw9939step2Labels := by
      have ha : raw9939step2 = (fun i j => raw9939step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9939step2 raw9939step1; decide +kernel
      have hl : raw9939step2Labels = raw9939step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9939step1 raw9939step1Labels permutation8 permutation7
    mixedMoment B raw9939step2 raw9939step2Labels = mixedMoment B raw9939step3 raw9939step3Labels := by
      have ha : raw9939step3 = raw9939step2 := by apply Matrix.ext; unfold raw9939step3 raw9939step2; decide +kernel
      have hl : raw9939step2Labels = labelEmbedding1 ∘ raw9939step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9939step2 raw9939step2Labels raw9939step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw9940 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9940Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9940step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9940step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9940step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9940 raw9940Labels = mixedMoment B node2709 node2709Labels := by
  calc
    mixedMoment B raw9940 raw9940Labels = mixedMoment B raw9940step0 raw9940step0Labels := by
      have ha : raw9940step0 = (fun i j => raw9940 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9940step0 raw9940; decide +kernel
      have hl : raw9940step0Labels = raw9940Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9940 raw9940Labels permutation152 permutation7
    mixedMoment B raw9940step0 raw9940step0Labels = mixedMoment B raw9940step1 raw9940step1Labels := by
      have ha : raw9940step1 = raw9940step0 := by apply Matrix.ext; unfold raw9940step1 raw9940step0; decide +kernel
      have hl : raw9940step0Labels = labelEmbedding1 ∘ raw9940step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9940step0 raw9940step0Labels raw9940step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2709 node2709Labels := by rfl

def raw9941 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9941Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9941step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9941step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9941step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9941 raw9941Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw9941 raw9941Labels = mixedMoment B raw9941step0 raw9941step0Labels := by
      have hz : ∀ j, raw9941 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9941step0 = (fun i j => raw9941 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9941step0 raw9941; decide +kernel
      have hl : raw9941step0Labels = raw9941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9941 raw9941Labels permutation346 hz
    mixedMoment B raw9941step0 raw9941step0Labels = mixedMoment B raw9941step1 raw9941step1Labels := by
      have ha : raw9941step1 = (fun i j => raw9941step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9941step1 raw9941step0; decide +kernel
      have hl : raw9941step1Labels = raw9941step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9941step0 raw9941step0Labels permutation32 permutation7
    mixedMoment B raw9941step1 raw9941step1Labels = mixedMoment B raw9941step2 raw9941step2Labels := by
      have ha : raw9941step2 = raw9941step1 := by apply Matrix.ext; unfold raw9941step2 raw9941step1; decide +kernel
      have hl : raw9941step1Labels = labelEmbedding1 ∘ raw9941step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9941step1 raw9941step1Labels raw9941step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw9942 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9942Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9942step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9942step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9942 raw9942Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw9942 raw9942Labels = mixedMoment B raw9942step0 raw9942step0Labels := by
      have hz : ∀ j, raw9942 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9942step0 = (fun i j => raw9942 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9942step0 raw9942; decide +kernel
      have hl : raw9942step0Labels = raw9942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9942 raw9942Labels permutation346 hz
    mixedMoment B raw9942step0 raw9942step0Labels = mixedMoment B raw9942step1 raw9942step1Labels := by
      have ha : raw9942step1 = (fun i j => raw9942step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9942step1 raw9942step0; decide +kernel
      have hl : raw9942step1Labels = raw9942step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9942step0 raw9942step0Labels permutation32 permutation7
    mixedMoment B raw9942step1 raw9942step1Labels = mixedMoment B raw9942step2 raw9942step2Labels := by
      have ha : raw9942step2 = raw9942step1 := by apply Matrix.ext; unfold raw9942step2 raw9942step1; decide +kernel
      have hl : raw9942step1Labels = labelEmbedding1 ∘ raw9942step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9942step1 raw9942step1Labels raw9942step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw9943 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9943Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9943step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9943step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9943 raw9943Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw9943 raw9943Labels = mixedMoment B raw9943step0 raw9943step0Labels := by
      have hz : ∀ j, raw9943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9943step0 = (fun i j => raw9943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9943step0 raw9943; decide +kernel
      have hl : raw9943step0Labels = raw9943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9943 raw9943Labels permutation346 hz
    mixedMoment B raw9943step0 raw9943step0Labels = mixedMoment B raw9943step1 raw9943step1Labels := by
      have ha : raw9943step1 = (fun i j => raw9943step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9943step1 raw9943step0; decide +kernel
      have hl : raw9943step1Labels = raw9943step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9943step0 raw9943step0Labels permutation32 permutation7
    mixedMoment B raw9943step1 raw9943step1Labels = mixedMoment B raw9943step2 raw9943step2Labels := by
      have ha : raw9943step2 = raw9943step1 := by apply Matrix.ext; unfold raw9943step2 raw9943step1; decide +kernel
      have hl : raw9943step1Labels = labelEmbedding1 ∘ raw9943step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9943step1 raw9943step1Labels raw9943step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw9944 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9944Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9944step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw9944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9944step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9944step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9944step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9944 raw9944Labels = mixedMoment B node3210 node3210Labels := by
  calc
    mixedMoment B raw9944 raw9944Labels = mixedMoment B raw9944step0 raw9944step0Labels := by
      have hz : ∀ j, raw9944 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9944step0 = (fun i j => raw9944 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9944step0 raw9944; decide +kernel
      have hl : raw9944step0Labels = raw9944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9944 raw9944Labels permutation346 hz
    mixedMoment B raw9944step0 raw9944step0Labels = mixedMoment B raw9944step1 raw9944step1Labels := by
      have ha : raw9944step1 = (fun i j => raw9944step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9944step1 raw9944step0; decide +kernel
      have hl : raw9944step1Labels = raw9944step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9944step0 raw9944step0Labels permutation43 permutation5
    mixedMoment B raw9944step1 raw9944step1Labels = mixedMoment B raw9944step2 raw9944step2Labels := by
      have ha : raw9944step2 = -raw9944step1 := by apply Matrix.ext; change ∀ i j, raw9944step2 i j = -(raw9944step1 i j); unfold raw9944step2 raw9944step1; decide +kernel
      have hl : raw9944step2Labels = raw9944step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9944step2 raw9944step2Labels = mixedMoment B raw9944step3 raw9944step3Labels := by
      have ha : raw9944step3 = raw9944step2 := by apply Matrix.ext; unfold raw9944step3 raw9944step2; decide +kernel
      have hl : raw9944step2Labels = labelEmbedding1 ∘ raw9944step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9944step2 raw9944step2Labels raw9944step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3210 node3210Labels := by rfl

def raw9945 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9945Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9945step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9945step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9945step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9945 raw9945Labels = mixedMoment B node3029 node3029Labels := by
  calc
    mixedMoment B raw9945 raw9945Labels = mixedMoment B raw9945step0 raw9945step0Labels := by
      have ha : raw9945step0 = (fun i j => raw9945 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9945step0 raw9945; decide +kernel
      have hl : raw9945step0Labels = raw9945Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9945 raw9945Labels permutation152 permutation7
    mixedMoment B raw9945step0 raw9945step0Labels = mixedMoment B raw9945step1 raw9945step1Labels := by
      have ha : raw9945step1 = raw9945step0 := by apply Matrix.ext; unfold raw9945step1 raw9945step0; decide +kernel
      have hl : raw9945step0Labels = labelEmbedding1 ∘ raw9945step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9945step0 raw9945step0Labels raw9945step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3029 node3029Labels := by rfl

def raw9946 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9946step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9946 raw9946Labels = mixedMoment B node3044 node3044Labels := by
  calc
    mixedMoment B raw9946 raw9946Labels = mixedMoment B raw9946step0 raw9946step0Labels := by
      have hz : ∀ j, raw9946 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9946step0 = (fun i j => raw9946 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9946step0 raw9946; decide +kernel
      have hl : raw9946step0Labels = raw9946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9946 raw9946Labels permutation346 hz
    mixedMoment B raw9946step0 raw9946step0Labels = mixedMoment B raw9946step1 raw9946step1Labels := by
      have ha : raw9946step1 = (fun i j => raw9946step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9946step1 raw9946step0; decide +kernel
      have hl : raw9946step1Labels = raw9946step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9946step0 raw9946step0Labels permutation32 permutation7
    mixedMoment B raw9946step1 raw9946step1Labels = mixedMoment B raw9946step2 raw9946step2Labels := by
      have ha : raw9946step2 = raw9946step1 := by apply Matrix.ext; unfold raw9946step2 raw9946step1; decide +kernel
      have hl : raw9946step1Labels = labelEmbedding1 ∘ raw9946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9946step1 raw9946step1Labels raw9946step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3044 node3044Labels := by rfl

def raw9947 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9947Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9947step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9947step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9947 raw9947Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw9947 raw9947Labels = mixedMoment B raw9947step0 raw9947step0Labels := by
      have hz : ∀ j, raw9947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9947step0 = (fun i j => raw9947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9947step0 raw9947; decide +kernel
      have hl : raw9947step0Labels = raw9947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9947 raw9947Labels permutation346 hz
    mixedMoment B raw9947step0 raw9947step0Labels = mixedMoment B raw9947step1 raw9947step1Labels := by
      have ha : raw9947step1 = (fun i j => raw9947step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9947step1 raw9947step0; decide +kernel
      have hl : raw9947step1Labels = raw9947step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9947step0 raw9947step0Labels permutation32 permutation7
    mixedMoment B raw9947step1 raw9947step1Labels = mixedMoment B raw9947step2 raw9947step2Labels := by
      have ha : raw9947step2 = raw9947step1 := by apply Matrix.ext; unfold raw9947step2 raw9947step1; decide +kernel
      have hl : raw9947step1Labels = labelEmbedding1 ∘ raw9947step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9947step1 raw9947step1Labels raw9947step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw9948 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9948Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9948step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9948 raw9948Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw9948 raw9948Labels = mixedMoment B raw9948step0 raw9948step0Labels := by
      have hz : ∀ j, raw9948 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9948step0 = (fun i j => raw9948 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9948step0 raw9948; decide +kernel
      have hl : raw9948step0Labels = raw9948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9948 raw9948Labels permutation346 hz
    mixedMoment B raw9948step0 raw9948step0Labels = mixedMoment B raw9948step1 raw9948step1Labels := by
      have ha : raw9948step1 = (fun i j => raw9948step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9948step1 raw9948step0; decide +kernel
      have hl : raw9948step1Labels = raw9948step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9948step0 raw9948step0Labels permutation32 permutation7
    mixedMoment B raw9948step1 raw9948step1Labels = mixedMoment B raw9948step2 raw9948step2Labels := by
      have ha : raw9948step2 = raw9948step1 := by apply Matrix.ext; unfold raw9948step2 raw9948step1; decide +kernel
      have hl : raw9948step1Labels = labelEmbedding1 ∘ raw9948step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9948step1 raw9948step1Labels raw9948step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw9949 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9949Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9949step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9949step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9949step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9949step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9949 raw9949Labels = mixedMoment B node3209 node3209Labels := by
  calc
    mixedMoment B raw9949 raw9949Labels = mixedMoment B raw9949step0 raw9949step0Labels := by
      have ha : raw9949step0 = (fun i j => raw9949 (permutation222 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9949step0 raw9949; decide +kernel
      have hl : raw9949step0Labels = raw9949Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9949 raw9949Labels permutation222 permutation5
    mixedMoment B raw9949step0 raw9949step0Labels = mixedMoment B raw9949step1 raw9949step1Labels := by
      have ha : raw9949step1 = -raw9949step0 := by apply Matrix.ext; change ∀ i j, raw9949step1 i j = -(raw9949step0 i j); unfold raw9949step1 raw9949step0; decide +kernel
      have hl : raw9949step1Labels = raw9949step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9949step1 raw9949step1Labels = mixedMoment B raw9949step2 raw9949step2Labels := by
      have ha : raw9949step2 = raw9949step1 := by apply Matrix.ext; unfold raw9949step2 raw9949step1; decide +kernel
      have hl : raw9949step1Labels = labelEmbedding1 ∘ raw9949step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9949step1 raw9949step1Labels raw9949step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3209 node3209Labels := by rfl

def raw9950 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9950Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9950step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9950step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9950step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9950 raw9950Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw9950 raw9950Labels = mixedMoment B raw9950step0 raw9950step0Labels := by
      have hz : ∀ j, raw9950 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9950step0 = (fun i j => raw9950 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9950step0 raw9950; decide +kernel
      have hl : raw9950step0Labels = raw9950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9950 raw9950Labels permutation265 hz
    mixedMoment B raw9950step0 raw9950step0Labels = mixedMoment B raw9950step1 raw9950step1Labels := by
      have ha : raw9950step1 = (fun i j => raw9950step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9950step1 raw9950step0; decide +kernel
      have hl : raw9950step1Labels = raw9950step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9950step0 raw9950step0Labels permutation32 permutation7
    mixedMoment B raw9950step1 raw9950step1Labels = mixedMoment B raw9950step2 raw9950step2Labels := by
      have ha : raw9950step2 = raw9950step1 := by apply Matrix.ext; unfold raw9950step2 raw9950step1; decide +kernel
      have hl : raw9950step1Labels = labelEmbedding1 ∘ raw9950step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9950step1 raw9950step1Labels raw9950step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw9951 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9951Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9951step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9951step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9951step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9951 raw9951Labels = mixedMoment B node3068 node3068Labels := by
  calc
    mixedMoment B raw9951 raw9951Labels = mixedMoment B raw9951step0 raw9951step0Labels := by
      have ha : raw9951step0 = (fun i j => raw9951 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9951step0 raw9951; decide +kernel
      have hl : raw9951step0Labels = raw9951Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9951 raw9951Labels permutation152 permutation7
    mixedMoment B raw9951step0 raw9951step0Labels = mixedMoment B raw9951step1 raw9951step1Labels := by
      have ha : raw9951step1 = raw9951step0 := by apply Matrix.ext; unfold raw9951step1 raw9951step0; decide +kernel
      have hl : raw9951step0Labels = labelEmbedding1 ∘ raw9951step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9951step0 raw9951step0Labels raw9951step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3068 node3068Labels := by rfl

def raw9952 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9952step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9952step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9952 raw9952Labels = mixedMoment B node3065 node3065Labels := by
  calc
    mixedMoment B raw9952 raw9952Labels = mixedMoment B raw9952step0 raw9952step0Labels := by
      have ha : raw9952step0 = (fun i j => raw9952 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9952step0 raw9952; decide +kernel
      have hl : raw9952step0Labels = raw9952Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9952 raw9952Labels permutation152 permutation7
    mixedMoment B raw9952step0 raw9952step0Labels = mixedMoment B raw9952step1 raw9952step1Labels := by
      have ha : raw9952step1 = raw9952step0 := by apply Matrix.ext; unfold raw9952step1 raw9952step0; decide +kernel
      have hl : raw9952step0Labels = labelEmbedding1 ∘ raw9952step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9952step0 raw9952step0Labels raw9952step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3065 node3065Labels := by rfl

def raw9953 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw9953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9953step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9953 raw9953Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw9953 raw9953Labels = mixedMoment B raw9953step0 raw9953step0Labels := by
      have ha : raw9953step0 = (fun i j => raw9953 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9953step0 raw9953; decide +kernel
      have hl : raw9953step0Labels = raw9953Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9953 raw9953Labels permutation152 permutation7
    mixedMoment B raw9953step0 raw9953step0Labels = mixedMoment B raw9953step1 raw9953step1Labels := by
      have ha : raw9953step1 = raw9953step0 := by apply Matrix.ext; unfold raw9953step1 raw9953step0; decide +kernel
      have hl : raw9953step0Labels = labelEmbedding1 ∘ raw9953step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9953step0 raw9953step0Labels raw9953step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3064 node3064Labels := by rfl

def raw9954 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9954step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9954step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9954step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9954step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw9954step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9954step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw9954step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9954 raw9954Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw9954 raw9954Labels = mixedMoment B raw9954step0 raw9954step0Labels := by
      have hz : ∀ j, raw9954 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9954step0 = (fun i j => raw9954 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9954step0 raw9954; decide +kernel
      have hl : raw9954step0Labels = raw9954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9954 raw9954Labels permutation434 hz
    mixedMoment B raw9954step0 raw9954step0Labels = mixedMoment B raw9954step1 raw9954step1Labels := by
      have hz : ∀ j, raw9954step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9954step1 = (fun i j => raw9954step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9954step1 raw9954step0; decide +kernel
      have hl : raw9954step1Labels = raw9954step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9954step0 raw9954step0Labels permutation80 hz
    mixedMoment B raw9954step1 raw9954step1Labels = mixedMoment B raw9954step2 raw9954step2Labels := by
      have ha : raw9954step2 = (fun i j => raw9954step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9954step2 raw9954step1; decide +kernel
      have hl : raw9954step2Labels = raw9954step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9954step1 raw9954step1Labels permutation8 permutation7
    mixedMoment B raw9954step2 raw9954step2Labels = mixedMoment B raw9954step3 raw9954step3Labels := by
      have ha : raw9954step3 = raw9954step2 := by apply Matrix.ext; unfold raw9954step3 raw9954step2; decide +kernel
      have hl : raw9954step2Labels = labelEmbedding1 ∘ raw9954step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9954step2 raw9954step2Labels raw9954step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw9955 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9955step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9955step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9955 raw9955Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw9955 raw9955Labels = mixedMoment B raw9955step0 raw9955step0Labels := by
      have hz : ∀ j, raw9955 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9955step0 = (fun i j => raw9955 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9955step0 raw9955; decide +kernel
      have hl : raw9955step0Labels = raw9955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9955 raw9955Labels permutation434 hz
    mixedMoment B raw9955step0 raw9955step0Labels = mixedMoment B raw9955step1 raw9955step1Labels := by
      have ha : raw9955step1 = (fun i j => raw9955step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9955step1 raw9955step0; decide +kernel
      have hl : raw9955step1Labels = raw9955step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9955step0 raw9955step0Labels permutation32 permutation7
    mixedMoment B raw9955step1 raw9955step1Labels = mixedMoment B raw9955step2 raw9955step2Labels := by
      have ha : raw9955step2 = raw9955step1 := by apply Matrix.ext; unfold raw9955step2 raw9955step1; decide +kernel
      have hl : raw9955step1Labels = labelEmbedding1 ∘ raw9955step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9955step1 raw9955step1Labels raw9955step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw9956 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9956step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9956step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9956step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw9956step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9956 raw9956Labels = mixedMoment B node3211 node3211Labels := by
  calc
    mixedMoment B raw9956 raw9956Labels = mixedMoment B raw9956step0 raw9956step0Labels := by
      have hz : ∀ j, raw9956 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9956step0 = (fun i j => raw9956 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9956step0 raw9956; decide +kernel
      have hl : raw9956step0Labels = raw9956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9956 raw9956Labels permutation346 hz
    mixedMoment B raw9956step0 raw9956step0Labels = mixedMoment B raw9956step1 raw9956step1Labels := by
      have ha : raw9956step1 = (fun i j => raw9956step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9956step1 raw9956step0; decide +kernel
      have hl : raw9956step1Labels = raw9956step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9956step0 raw9956step0Labels permutation42 permutation5
    mixedMoment B raw9956step1 raw9956step1Labels = mixedMoment B raw9956step2 raw9956step2Labels := by
      have ha : raw9956step2 = -raw9956step1 := by apply Matrix.ext; change ∀ i j, raw9956step2 i j = -(raw9956step1 i j); unfold raw9956step2 raw9956step1; decide +kernel
      have hl : raw9956step2Labels = raw9956step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9956step2 raw9956step2Labels = mixedMoment B raw9956step3 raw9956step3Labels := by
      have ha : raw9956step3 = raw9956step2 := by apply Matrix.ext; unfold raw9956step3 raw9956step2; decide +kernel
      have hl : raw9956step2Labels = labelEmbedding1 ∘ raw9956step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9956step2 raw9956step2Labels raw9956step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3211 node3211Labels := by rfl

def raw9957 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9957step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9957 raw9957Labels = mixedMoment B node3080 node3080Labels := by
  calc
    mixedMoment B raw9957 raw9957Labels = mixedMoment B raw9957step0 raw9957step0Labels := by
      have ha : raw9957step0 = (fun i j => raw9957 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9957step0 raw9957; decide +kernel
      have hl : raw9957step0Labels = raw9957Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9957 raw9957Labels permutation152 permutation7
    mixedMoment B raw9957step0 raw9957step0Labels = mixedMoment B raw9957step1 raw9957step1Labels := by
      have ha : raw9957step1 = raw9957step0 := by apply Matrix.ext; unfold raw9957step1 raw9957step0; decide +kernel
      have hl : raw9957step0Labels = labelEmbedding1 ∘ raw9957step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9957step0 raw9957step0Labels raw9957step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3080 node3080Labels := by rfl

def raw9958 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9958step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9958step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw9958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9958 raw9958Labels = mixedMoment B node3092 node3092Labels := by
  calc
    mixedMoment B raw9958 raw9958Labels = mixedMoment B raw9958step0 raw9958step0Labels := by
      have hz : ∀ j, raw9958 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9958step0 = (fun i j => raw9958 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9958step0 raw9958; decide +kernel
      have hl : raw9958step0Labels = raw9958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9958 raw9958Labels permutation346 hz
    mixedMoment B raw9958step0 raw9958step0Labels = mixedMoment B raw9958step1 raw9958step1Labels := by
      have ha : raw9958step1 = (fun i j => raw9958step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9958step1 raw9958step0; decide +kernel
      have hl : raw9958step1Labels = raw9958step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9958step0 raw9958step0Labels permutation32 permutation7
    mixedMoment B raw9958step1 raw9958step1Labels = mixedMoment B raw9958step2 raw9958step2Labels := by
      have ha : raw9958step2 = raw9958step1 := by apply Matrix.ext; unfold raw9958step2 raw9958step1; decide +kernel
      have hl : raw9958step1Labels = labelEmbedding1 ∘ raw9958step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9958step1 raw9958step1Labels raw9958step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3092 node3092Labels := by rfl

def raw9959 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9959step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw9959step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9959step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9959step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9959step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9959step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9959 raw9959Labels = mixedMoment B node3214 node3214Labels := by
  calc
    mixedMoment B raw9959 raw9959Labels = mixedMoment B raw9959step0 raw9959step0Labels := by
      have hz : ∀ j, raw9959 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9959step0 = (fun i j => raw9959 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9959step0 raw9959; decide +kernel
      have hl : raw9959step0Labels = raw9959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9959 raw9959Labels permutation346 hz
    mixedMoment B raw9959step0 raw9959step0Labels = mixedMoment B raw9959step1 raw9959step1Labels := by
      have ha : raw9959step1 = (fun i j => raw9959step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9959step1 raw9959step0; decide +kernel
      have hl : raw9959step1Labels = raw9959step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9959step0 raw9959step0Labels permutation40 permutation5
    mixedMoment B raw9959step1 raw9959step1Labels = mixedMoment B raw9959step2 raw9959step2Labels := by
      have ha : raw9959step2 = -raw9959step1 := by apply Matrix.ext; change ∀ i j, raw9959step2 i j = -(raw9959step1 i j); unfold raw9959step2 raw9959step1; decide +kernel
      have hl : raw9959step2Labels = raw9959step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9959step2 raw9959step2Labels = mixedMoment B raw9959step3 raw9959step3Labels := by
      have ha : raw9959step3 = raw9959step2 := by apply Matrix.ext; unfold raw9959step3 raw9959step2; decide +kernel
      have hl : raw9959step2Labels = labelEmbedding1 ∘ raw9959step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9959step2 raw9959step2Labels raw9959step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3214 node3214Labels := by rfl

def raw9960 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9960step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9960step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9960step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9960step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9960step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9960step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9960 raw9960Labels = mixedMoment B node3112 node3112Labels := by
  calc
    mixedMoment B raw9960 raw9960Labels = mixedMoment B raw9960step0 raw9960step0Labels := by
      have hz : ∀ j, raw9960 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9960step0 = (fun i j => raw9960 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9960step0 raw9960; decide +kernel
      have hl : raw9960step0Labels = raw9960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9960 raw9960Labels permutation346 hz
    mixedMoment B raw9960step0 raw9960step0Labels = mixedMoment B raw9960step1 raw9960step1Labels := by
      have hz : ∀ j, raw9960step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9960step1 = (fun i j => raw9960step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9960step1 raw9960step0; decide +kernel
      have hl : raw9960step1Labels = raw9960step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9960step0 raw9960step0Labels permutation56 hz
    mixedMoment B raw9960step1 raw9960step1Labels = mixedMoment B raw9960step2 raw9960step2Labels := by
      have ha : raw9960step2 = (fun i j => raw9960step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9960step2 raw9960step1; decide +kernel
      have hl : raw9960step2Labels = raw9960step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9960step1 raw9960step1Labels permutation8 permutation7
    mixedMoment B raw9960step2 raw9960step2Labels = mixedMoment B raw9960step3 raw9960step3Labels := by
      have ha : raw9960step3 = raw9960step2 := by apply Matrix.ext; unfold raw9960step3 raw9960step2; decide +kernel
      have hl : raw9960step2Labels = labelEmbedding1 ∘ raw9960step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9960step2 raw9960step2Labels raw9960step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3112 node3112Labels := by rfl

def raw9961 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9961step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9961step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9961 raw9961Labels = mixedMoment B node3081 node3081Labels := by
  calc
    mixedMoment B raw9961 raw9961Labels = mixedMoment B raw9961step0 raw9961step0Labels := by
      have ha : raw9961step0 = (fun i j => raw9961 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9961step0 raw9961; decide +kernel
      have hl : raw9961step0Labels = raw9961Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9961 raw9961Labels permutation152 permutation7
    mixedMoment B raw9961step0 raw9961step0Labels = mixedMoment B raw9961step1 raw9961step1Labels := by
      have ha : raw9961step1 = raw9961step0 := by apply Matrix.ext; unfold raw9961step1 raw9961step0; decide +kernel
      have hl : raw9961step0Labels = labelEmbedding1 ∘ raw9961step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9961step0 raw9961step0Labels raw9961step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3081 node3081Labels := by rfl

def raw9962 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9962Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9962step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw9962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw9962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9962 raw9962Labels = mixedMoment B node3094 node3094Labels := by
  calc
    mixedMoment B raw9962 raw9962Labels = mixedMoment B raw9962step0 raw9962step0Labels := by
      have hz : ∀ j, raw9962 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9962step0 = (fun i j => raw9962 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9962step0 raw9962; decide +kernel
      have hl : raw9962step0Labels = raw9962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9962 raw9962Labels permutation346 hz
    mixedMoment B raw9962step0 raw9962step0Labels = mixedMoment B raw9962step1 raw9962step1Labels := by
      have ha : raw9962step1 = (fun i j => raw9962step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9962step1 raw9962step0; decide +kernel
      have hl : raw9962step1Labels = raw9962step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9962step0 raw9962step0Labels permutation32 permutation7
    mixedMoment B raw9962step1 raw9962step1Labels = mixedMoment B raw9962step2 raw9962step2Labels := by
      have ha : raw9962step2 = raw9962step1 := by apply Matrix.ext; unfold raw9962step2 raw9962step1; decide +kernel
      have hl : raw9962step1Labels = labelEmbedding1 ∘ raw9962step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9962step1 raw9962step1Labels raw9962step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3094 node3094Labels := by rfl

def raw9963 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9963step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9963step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9963 raw9963Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw9963 raw9963Labels = mixedMoment B raw9963step0 raw9963step0Labels := by
      have hz : ∀ j, raw9963 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9963step0 = (fun i j => raw9963 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9963step0 raw9963; decide +kernel
      have hl : raw9963step0Labels = raw9963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9963 raw9963Labels permutation346 hz
    mixedMoment B raw9963step0 raw9963step0Labels = mixedMoment B raw9963step1 raw9963step1Labels := by
      have ha : raw9963step1 = (fun i j => raw9963step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9963step1 raw9963step0; decide +kernel
      have hl : raw9963step1Labels = raw9963step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9963step0 raw9963step0Labels permutation38 permutation4
    mixedMoment B raw9963step1 raw9963step1Labels = mixedMoment B raw9963step2 raw9963step2Labels := by
      have ha : raw9963step2 = -raw9963step1 := by apply Matrix.ext; change ∀ i j, raw9963step2 i j = -(raw9963step1 i j); unfold raw9963step2 raw9963step1; decide +kernel
      have hl : raw9963step2Labels = raw9963step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw9964 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw9964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9964 raw9964Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw9964 raw9964Labels = mixedMoment B raw9964step0 raw9964step0Labels := by
      have hz : ∀ j, raw9964 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9964step0 = (fun i j => raw9964 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9964step0 raw9964; decide +kernel
      have hl : raw9964step0Labels = raw9964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9964 raw9964Labels permutation346 hz
    mixedMoment B raw9964step0 raw9964step0Labels = mixedMoment B raw9964step1 raw9964step1Labels := by
      have ha : raw9964step1 = (fun i j => raw9964step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9964step1 raw9964step0; decide +kernel
      have hl : raw9964step1Labels = raw9964step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9964step0 raw9964step0Labels permutation41 permutation4
    mixedMoment B raw9964step1 raw9964step1Labels = mixedMoment B raw9964step2 raw9964step2Labels := by
      have ha : raw9964step2 = -raw9964step1 := by apply Matrix.ext; change ∀ i j, raw9964step2 i j = -(raw9964step1 i j); unfold raw9964step2 raw9964step1; decide +kernel
      have hl : raw9964step2Labels = raw9964step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2058 node2058Labels := by rfl

def raw9965 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9965step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9965 raw9965Labels = mixedMoment B node2051 node2051Labels := by
  calc
    mixedMoment B raw9965 raw9965Labels = mixedMoment B raw9965step0 raw9965step0Labels := by
      have ha : raw9965step0 = (fun i j => raw9965 (permutation200 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9965step0 raw9965; decide +kernel
      have hl : raw9965step0Labels = raw9965Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9965 raw9965Labels permutation200 permutation4
    mixedMoment B raw9965step0 raw9965step0Labels = mixedMoment B raw9965step1 raw9965step1Labels := by
      have ha : raw9965step1 = -raw9965step0 := by apply Matrix.ext; change ∀ i j, raw9965step1 i j = -(raw9965step0 i j); unfold raw9965step1 raw9965step0; decide +kernel
      have hl : raw9965step1Labels = raw9965step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2051 node2051Labels := by rfl

def raw9966 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw9966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9966step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw9966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9966step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9966step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9966 raw9966Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw9966 raw9966Labels = mixedMoment B raw9966step0 raw9966step0Labels := by
      have hz : ∀ j, raw9966 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9966step0 = (fun i j => raw9966 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9966step0 raw9966; decide +kernel
      have hl : raw9966step0Labels = raw9966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9966 raw9966Labels permutation434 hz
    mixedMoment B raw9966step0 raw9966step0Labels = mixedMoment B raw9966step1 raw9966step1Labels := by
      have hz : ∀ j, raw9966step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9966step1 = (fun i j => raw9966step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9966step1 raw9966step0; decide +kernel
      have hl : raw9966step1Labels = raw9966step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9966step0 raw9966step0Labels permutation80 hz
    mixedMoment B raw9966step1 raw9966step1Labels = mixedMoment B raw9966step2 raw9966step2Labels := by
      have ha : raw9966step2 = (fun i j => raw9966step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9966step2 raw9966step1; decide +kernel
      have hl : raw9966step2Labels = raw9966step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9966step1 raw9966step1Labels permutation8 permutation4
    mixedMoment B raw9966step2 raw9966step2Labels = mixedMoment B raw9966step3 raw9966step3Labels := by
      have ha : raw9966step3 = -raw9966step2 := by apply Matrix.ext; change ∀ i j, raw9966step3 i j = -(raw9966step2 i j); unfold raw9966step3 raw9966step2; decide +kernel
      have hl : raw9966step3Labels = raw9966step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2291 node2291Labels := by rfl

def raw9967 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw9967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw9967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw9967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9967 raw9967Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw9967 raw9967Labels = mixedMoment B raw9967step0 raw9967step0Labels := by
      have hz : ∀ j, raw9967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9967step0 = (fun i j => raw9967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9967step0 raw9967; decide +kernel
      have hl : raw9967step0Labels = raw9967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9967 raw9967Labels permutation346 hz
    mixedMoment B raw9967step0 raw9967step0Labels = mixedMoment B raw9967step1 raw9967step1Labels := by
      have ha : raw9967step1 = (fun i j => raw9967step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9967step1 raw9967step0; decide +kernel
      have hl : raw9967step1Labels = raw9967step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9967step0 raw9967step0Labels permutation39 permutation4
    mixedMoment B raw9967step1 raw9967step1Labels = mixedMoment B raw9967step2 raw9967step2Labels := by
      have ha : raw9967step2 = -raw9967step1 := by apply Matrix.ext; change ∀ i j, raw9967step2 i j = -(raw9967step1 i j); unfold raw9967step2 raw9967step1; decide +kernel
      have hl : raw9967step2Labels = raw9967step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2054 node2054Labels := by rfl

def raw9968 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw9968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9968step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9968 raw9968Labels = mixedMoment B node2053 node2053Labels := by
  calc
    mixedMoment B raw9968 raw9968Labels = mixedMoment B raw9968step0 raw9968step0Labels := by
      have hz : ∀ j, raw9968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9968step0 = (fun i j => raw9968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9968step0 raw9968; decide +kernel
      have hl : raw9968step0Labels = raw9968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9968 raw9968Labels permutation346 hz
    mixedMoment B raw9968step0 raw9968step0Labels = mixedMoment B raw9968step1 raw9968step1Labels := by
      have ha : raw9968step1 = (fun i j => raw9968step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9968step1 raw9968step0; decide +kernel
      have hl : raw9968step1Labels = raw9968step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9968step0 raw9968step0Labels permutation38 permutation4
    mixedMoment B raw9968step1 raw9968step1Labels = mixedMoment B raw9968step2 raw9968step2Labels := by
      have ha : raw9968step2 = -raw9968step1 := by apply Matrix.ext; change ∀ i j, raw9968step2 i j = -(raw9968step1 i j); unfold raw9968step2 raw9968step1; decide +kernel
      have hl : raw9968step2Labels = raw9968step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2053 node2053Labels := by rfl

def raw9969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw9969step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9969step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9969 raw9969Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw9969 raw9969Labels = mixedMoment B raw9969step0 raw9969step0Labels := by
      have hz : ∀ j, raw9969 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9969step0 = (fun i j => raw9969 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9969step0 raw9969; decide +kernel
      have hl : raw9969step0Labels = raw9969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9969 raw9969Labels permutation346 hz
    mixedMoment B raw9969step0 raw9969step0Labels = mixedMoment B raw9969step1 raw9969step1Labels := by
      have ha : raw9969step1 = (fun i j => raw9969step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9969step1 raw9969step0; decide +kernel
      have hl : raw9969step1Labels = raw9969step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9969step0 raw9969step0Labels permutation151 permutation2
    mixedMoment B raw9969step1 raw9969step1Labels = mixedMoment B raw9969step2 raw9969step2Labels := by
      have ha : raw9969step2 = -raw9969step1 := by apply Matrix.ext; change ∀ i j, raw9969step2 i j = -(raw9969step1 i j); unfold raw9969step2 raw9969step1; decide +kernel
      have hl : raw9969step2Labels = raw9969step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw9970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9970 raw9970Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw9970 raw9970Labels = mixedMoment B raw9970step0 raw9970step0Labels := by
      have ha : raw9970step0 = (fun i j => raw9970 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9970step0 raw9970; decide +kernel
      have hl : raw9970step0Labels = raw9970Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9970 raw9970Labels permutation182 permutation2
    _ = mixedMoment B node5423 node5423Labels := by rfl

def raw9971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9971step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9971 raw9971Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw9971 raw9971Labels = mixedMoment B raw9971step0 raw9971step0Labels := by
      have hz : ∀ j, raw9971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9971step0 = (fun i j => raw9971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9971step0 raw9971; decide +kernel
      have hl : raw9971step0Labels = raw9971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9971 raw9971Labels permutation346 hz
    mixedMoment B raw9971step0 raw9971step0Labels = mixedMoment B raw9971step1 raw9971step1Labels := by
      have ha : raw9971step1 = (fun i j => raw9971step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9971step1 raw9971step0; decide +kernel
      have hl : raw9971step1Labels = raw9971step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9971step0 raw9971step0Labels permutation38 permutation2
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw9972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw9972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw9972step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw9972step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9972step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9972step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9972 raw9972Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw9972 raw9972Labels = mixedMoment B raw9972step0 raw9972step0Labels := by
      have hz : ∀ j, raw9972 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9972step0 = (fun i j => raw9972 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9972step0 raw9972; decide +kernel
      have hl : raw9972step0Labels = raw9972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9972 raw9972Labels permutation520 hz
    mixedMoment B raw9972step0 raw9972step0Labels = mixedMoment B raw9972step1 raw9972step1Labels := by
      have hz : ∀ j, raw9972step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9972step1 = (fun i j => raw9972step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9972step1 raw9972step0; decide +kernel
      have hl : raw9972step1Labels = raw9972step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9972step0 raw9972step0Labels permutation80 hz
    mixedMoment B raw9972step1 raw9972step1Labels = mixedMoment B raw9972step2 raw9972step2Labels := by
      have ha : raw9972step2 = (fun i j => raw9972step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9972step2 raw9972step1; decide +kernel
      have hl : raw9972step2Labels = raw9972step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9972step1 raw9972step1Labels permutation29 permutation7
    mixedMoment B raw9972step2 raw9972step2Labels = mixedMoment B raw9972step3 raw9972step3Labels := by
      have ha : raw9972step3 = raw9972step2 := by apply Matrix.ext; unfold raw9972step3 raw9972step2; decide +kernel
      have hl : raw9972step2Labels = labelEmbedding10 ∘ raw9972step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9972step2 raw9972step2Labels raw9972step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5441 node5441Labels := by rfl

def raw9973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9973step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9973step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9973step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9973step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9973 raw9973Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw9973 raw9973Labels = mixedMoment B raw9973step0 raw9973step0Labels := by
      have hz : ∀ j, raw9973 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9973step0 = (fun i j => raw9973 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9973step0 raw9973; decide +kernel
      have hl : raw9973step0Labels = raw9973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9973 raw9973Labels permutation346 hz
    mixedMoment B raw9973step0 raw9973step0Labels = mixedMoment B raw9973step1 raw9973step1Labels := by
      have ha : raw9973step1 = (fun i j => raw9973step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9973step1 raw9973step0; decide +kernel
      have hl : raw9973step1Labels = raw9973step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9973step0 raw9973step0Labels permutation40 permutation7
    mixedMoment B raw9973step1 raw9973step1Labels = mixedMoment B raw9973step2 raw9973step2Labels := by
      have ha : raw9973step2 = -raw9973step1 := by apply Matrix.ext; change ∀ i j, raw9973step2 i j = -(raw9973step1 i j); unfold raw9973step2 raw9973step1; decide +kernel
      have hl : raw9973step2Labels = raw9973step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9973step2 raw9973step2Labels = mixedMoment B raw9973step3 raw9973step3Labels := by
      have ha : raw9973step3 = raw9973step2 := by apply Matrix.ext; unfold raw9973step3 raw9973step2; decide +kernel
      have hl : raw9973step2Labels = labelEmbedding10 ∘ raw9973step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9973step2 raw9973step2Labels raw9973step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw9974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9974step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9974 raw9974Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw9974 raw9974Labels = mixedMoment B raw9974step0 raw9974step0Labels := by
      have hz : ∀ j, raw9974 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9974step0 = (fun i j => raw9974 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9974step0 raw9974; decide +kernel
      have hl : raw9974step0Labels = raw9974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9974 raw9974Labels permutation346 hz
    mixedMoment B raw9974step0 raw9974step0Labels = mixedMoment B raw9974step1 raw9974step1Labels := by
      have ha : raw9974step1 = (fun i j => raw9974step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9974step1 raw9974step0; decide +kernel
      have hl : raw9974step1Labels = raw9974step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9974step0 raw9974step0Labels permutation40 permutation2
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw9975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9975step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9975 raw9975Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw9975 raw9975Labels = mixedMoment B raw9975step0 raw9975step0Labels := by
      have ha : raw9975step0 = (fun i j => raw9975 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9975step0 raw9975; decide +kernel
      have hl : raw9975step0Labels = raw9975Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9975 raw9975Labels permutation184 permutation2
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw9976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9976step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9976step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9976 raw9976Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw9976 raw9976Labels = mixedMoment B raw9976step0 raw9976step0Labels := by
      have hz : ∀ j, raw9976 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9976step0 = (fun i j => raw9976 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9976step0 raw9976; decide +kernel
      have hl : raw9976step0Labels = raw9976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9976 raw9976Labels permutation346 hz
    mixedMoment B raw9976step0 raw9976step0Labels = mixedMoment B raw9976step1 raw9976step1Labels := by
      have ha : raw9976step1 = (fun i j => raw9976step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9976step1 raw9976step0; decide +kernel
      have hl : raw9976step1Labels = raw9976step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9976step0 raw9976step0Labels permutation40 permutation2
    _ = mixedMoment B node5101 node5101Labels := by rfl

def raw9977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw9977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw9977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw9977step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9977step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9977 raw9977Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw9977 raw9977Labels = mixedMoment B raw9977step0 raw9977step0Labels := by
      have hz : ∀ j, raw9977 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9977step0 = (fun i j => raw9977 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9977step0 raw9977; decide +kernel
      have hl : raw9977step0Labels = raw9977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9977 raw9977Labels permutation520 hz
    mixedMoment B raw9977step0 raw9977step0Labels = mixedMoment B raw9977step1 raw9977step1Labels := by
      have hz : ∀ j, raw9977step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9977step1 = (fun i j => raw9977step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9977step1 raw9977step0; decide +kernel
      have hl : raw9977step1Labels = raw9977step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9977step0 raw9977step0Labels permutation80 hz
    mixedMoment B raw9977step1 raw9977step1Labels = mixedMoment B raw9977step2 raw9977step2Labels := by
      have ha : raw9977step2 = (fun i j => raw9977step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9977step2 raw9977step1; decide +kernel
      have hl : raw9977step2Labels = raw9977step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9977step1 raw9977step1Labels permutation10 permutation2
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw9978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9978step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9978 raw9978Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw9978 raw9978Labels = mixedMoment B raw9978step0 raw9978step0Labels := by
      have hz : ∀ j, raw9978 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9978step0 = (fun i j => raw9978 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9978step0 raw9978; decide +kernel
      have hl : raw9978step0Labels = raw9978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9978 raw9978Labels permutation346 hz
    mixedMoment B raw9978step0 raw9978step0Labels = mixedMoment B raw9978step1 raw9978step1Labels := by
      have ha : raw9978step1 = (fun i j => raw9978step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9978step1 raw9978step0; decide +kernel
      have hl : raw9978step1Labels = raw9978step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9978step0 raw9978step0Labels permutation40 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw9979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9979step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9979 raw9979Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw9979 raw9979Labels = mixedMoment B raw9979step0 raw9979step0Labels := by
      have ha : raw9979step0 = (fun i j => raw9979 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9979step0 raw9979; decide +kernel
      have hl : raw9979step0Labels = raw9979Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9979 raw9979Labels permutation200 permutation2
    _ = mixedMoment B node4589 node4589Labels := by rfl

def raw9980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9980step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9980 raw9980Labels = mixedMoment B node5184 node5184Labels := by
  calc
    mixedMoment B raw9980 raw9980Labels = mixedMoment B raw9980step0 raw9980step0Labels := by
      have ha : raw9980step0 = (fun i j => raw9980 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9980step0 raw9980; decide +kernel
      have hl : raw9980step0Labels = raw9980Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9980 raw9980Labels permutation158 permutation2
    _ = mixedMoment B node5184 node5184Labels := by rfl

def raw9981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw9981step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9981 raw9981Labels = mixedMoment B node5072 node5072Labels := by
  calc
    mixedMoment B raw9981 raw9981Labels = mixedMoment B raw9981step0 raw9981step0Labels := by
      have ha : raw9981step0 = (fun i j => raw9981 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9981step0 raw9981; decide +kernel
      have hl : raw9981step0Labels = raw9981Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9981 raw9981Labels permutation200 permutation2
    _ = mixedMoment B node5072 node5072Labels := by rfl

def raw9982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw9982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw9982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw9982step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9982 raw9982Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw9982 raw9982Labels = mixedMoment B raw9982step0 raw9982step0Labels := by
      have hz : ∀ j, raw9982 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9982step0 = (fun i j => raw9982 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9982step0 raw9982; decide +kernel
      have hl : raw9982step0Labels = raw9982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9982 raw9982Labels permutation520 hz
    mixedMoment B raw9982step0 raw9982step0Labels = mixedMoment B raw9982step1 raw9982step1Labels := by
      have ha : raw9982step1 = (fun i j => raw9982step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9982step1 raw9982step0; decide +kernel
      have hl : raw9982step1Labels = raw9982step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9982step0 raw9982step0Labels permutation44 permutation2
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw9983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9983step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9983 raw9983Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw9983 raw9983Labels = mixedMoment B raw9983step0 raw9983step0Labels := by
      have ha : raw9983step0 = (fun i j => raw9983 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9983step0 raw9983; decide +kernel
      have hl : raw9983step0Labels = raw9983Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9983 raw9983Labels permutation200 permutation2
    _ = mixedMoment B node5256 node5256Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
